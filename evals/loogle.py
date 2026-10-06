"""Bounded host-side Loogle observations; results are advisory until pinned Lean checks.

Official API: https://github.com/nomeata/loogle#web-service documents /json?q=… and warns
that its schema is unstable. The public service searches its current corpus, not this pinned project.
No URLs from queries/results are fetched. No retries, shell, dependency install or model calls occur.
The owner records returned JSON-safe observations; this module writes no persistent state.
"""
import base64
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request

ENDPOINT = "https://loogle.lean-lang.org/json"
QUERY_BYTES = 2048
RESPONSE_BYTES = 256 * 1024
TIMEOUT_SECONDS = 15
HITS_MAX = 20


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, response, code, message, headers, url):
        return None


def _fetch(url, timeout, limit):
    """One fixed-origin read in a disposable child; the parent supplies the hard wall deadline."""
    parsed = urllib.parse.urlsplit(url)
    if (parsed.scheme, parsed.netloc, parsed.path) != ("https", "loogle.lean-lang.org", "/json") or parsed.fragment:
        raise ValueError("Loogle endpoint is fixed")
    request = urllib.request.Request(url, headers={"Accept": "application/json", "Accept-Encoding": "identity",
                                                  "User-Agent": "ftqclib-evals/loogle-owner-client"})
    opener = urllib.request.build_opener(NoRedirect())
    try:
        response = opener.open(request, timeout=timeout)
    except urllib.error.HTTPError as error:
        response = error
    with response:
        body = response.read(limit + 1)
        headers = {name.lower(): response.headers.get(name, "")[:256]
                   for name in ("Content-Type", "Content-Encoding", "Date", "ETag", "Retry-After")}
        return {"http_status": response.status, "headers": headers,
                "body_b64": base64.b64encode(body).decode("ascii")}


def host_transport(url, timeout, limit):
    """Bounded HTTP and child lifetime, including DNS/slow response stalls; no shell is used."""
    child = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--fetch"],
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    request = json.dumps({"url": url, "timeout": timeout, "limit": limit}).encode()
    try:
        stdout, _ = child.communicate(request, timeout=timeout)
    except subprocess.TimeoutExpired:
        child.kill()
        child.communicate()
        raise TimeoutError("Loogle wall deadline reached") from None
    if child.returncode or len(stdout) > 2 * (limit + 4096):
        raise OSError("Loogle transport child failed")
    result = json.loads(stdout)
    if "failure" in result:
        raise OSError(result["failure"])
    result["body"] = base64.b64decode(result.pop("body_b64"), validate=True)
    return result


def search(query, *, transport=None, timeout=10, max_hits=HITS_MAX):
    """Observe one search. Injected transport(url, timeout, limit) returns status/headers/body bytes.

    The injected owner transport must honor the supplied bounds. Default transport enforces a wall
    deadline in a reaped subprocess. Returned raw bytes are base64 for parent Store recording; a digest
    of an oversize response explicitly covers only the retained prefix, never an unseen complete body.
    Empty means this service returned zero hits for this query, not that a theorem does not exist.
    """
    record = {"service": "loogle", "endpoint": ENDPOINT, "query": None,
              "advisory": True, "hits": [], "client_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if (not isinstance(query, str) or not query.strip() or type(max_hits) is not int or not 1 <= max_hits <= HITS_MAX
            or isinstance(timeout, bool) or not isinstance(timeout, (int, float)) or not 0 < timeout <= TIMEOUT_SECONDS):
        return {**record, "status": "refused", "reason": "invalid query, timeout or hit bound"}
    try:
        query_bytes = query.encode("utf-8")
    except UnicodeError:
        return {**record, "status": "refused", "reason": "query is not valid UTF-8"}
    if len(query_bytes) > QUERY_BYTES or any(character in query for character in "\0\r\n"):
        return {**record, "status": "refused", "reason": "query exceeds byte bound or contains a line/control separator"}
    url = ENDPOINT + "?" + urllib.parse.urlencode({"q": query})
    record.update({"query": query, "request_url": url, "timeout_seconds": timeout, "max_hits": max_hits})
    try:
        response = (transport or host_transport)(url, timeout, RESPONSE_BYTES)
    except TimeoutError:
        return {**record, "status": "unavailable", "reason": "timeout"}
    except (OSError, ValueError, urllib.error.URLError) as error:
        return {**record, "status": "unavailable", "reason": "transport: " + str(error)[:512]}
    if (not isinstance(response, dict) or not isinstance(response.get("body"), bytes)
            or type(response.get("http_status")) is not int or not isinstance(response.get("headers"), dict)):
        return {**record, "status": "error", "reason": "invalid transport response"}
    body = response["body"]
    retained = body[:RESPONSE_BYTES]
    record.update({"http_status": response["http_status"], "response_headers": {
        name: str(response["headers"].get(name, ""))[:256]
        for name in ("content-type", "content-encoding", "date", "etag", "retry-after")},
        "raw_response_b64": base64.b64encode(retained).decode("ascii"),
        "raw_response_sha256": hashlib.sha256(retained).hexdigest(), "retained_bytes": len(retained),
        "raw_response_complete": len(body) <= RESPONSE_BYTES})
    if len(body) > RESPONSE_BYTES:
        return {**record, "status": "error", "reason": "response byte bound exceeded"}
    http_status = response["http_status"]
    if http_status == 429 or 500 <= http_status <= 599:
        return {**record, "status": "unavailable", "reason": "HTTP " + str(http_status)}
    if http_status != 200:
        return {**record, "status": "error", "reason": "HTTP " + str(http_status)}
    if record["response_headers"]["content-encoding"].lower() not in ("", "identity"):
        return {**record, "status": "error", "reason": "unsupported content encoding"}
    try:
        data = json.loads(body.decode("utf-8"))
    except (ValueError, UnicodeError, RecursionError):
        return {**record, "status": "error", "reason": "invalid JSON response"}
    if not isinstance(data, dict):
        return {**record, "status": "error", "reason": "response is not an object"}
    if isinstance(data.get("error"), str):
        return {**record, "status": "error", "reason": "service: " + data["error"][:1024]}
    count, hits = data.get("count"), data.get("hits")
    if type(count) is not int or count < 0 or not isinstance(hits, list) or count < len(hits) or (count > 0 and not hits):
        return {**record, "status": "error", "reason": "unsupported response schema"}
    for hit in hits:
        if (not isinstance(hit, dict) or not isinstance(hit.get("name"), str) or not hit["name"]
                or not isinstance(hit.get("type"), str) or not isinstance(hit.get("module", ""), str)):
            return {**record, "status": "error", "reason": "invalid declaration hit"}
        try:
            sizes = [len(hit.get(field, "").encode("utf-8")) for field in ("name", "type", "module")]
        except UnicodeError:
            return {**record, "status": "error", "reason": "invalid UTF-8 declaration hit"}
        if sizes[0] > 1024 or sizes[1] > 65536 or sizes[2] > 1024:
            return {**record, "status": "error", "reason": "declaration hit byte bound exceeded"}
    normalized = [{"name": hit["name"], "type": hit["type"], "module": hit.get("module", "")}
                  for hit in hits[:max_hits]]
    return {**record, "status": "ok" if hits else "empty", "hits": normalized, "service_count": count,
            "returned_count": len(hits), "hits_truncated": count > len(normalized)}


if __name__ == "__main__":
    if sys.argv[1:] != ["--fetch"]:
        raise SystemExit("owner library; transport child only")
    try:
        request = json.loads(sys.stdin.buffer.read(16 * 1024))
        output = _fetch(request["url"], request["timeout"], request["limit"])
    except (OSError, ValueError, KeyError, urllib.error.URLError) as error:
        output = {"failure": str(error)[:512]}
    sys.stdout.write(json.dumps(output))
