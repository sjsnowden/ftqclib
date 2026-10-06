"""Goal: fixed-origin bounded search records distinguish observations, empty results and failures.

Method: scripted owner transports feed captured API-shaped responses and faults; no network/model/build
is used by this test. Exact byte identity, bounds, Unicode and schema refusals are checked.
"""
import base64
import hashlib
import json
import urllib.parse

import loogle


def reply(data, status=200):
    return {"http_status": status, "headers": {"content-type": "application/json"},
            "body": json.dumps(data, ensure_ascii=False).encode()}


def check():
    query = '"Nat.add_comm", _ + _ = _ + _'
    response = reply({"count": 1, "hits": [{"name": "Nat.add_comm", "module": "Init.Data.Nat.Basic",
                                         "type": " (n m : ℕ) : n + m = m + n", "doc": None}]})
    calls = []

    def script(url, timeout, limit):
        calls.append((url, timeout, limit))
        return response

    observed = loogle.search(query, transport=script)
    assert observed["status"] == "ok" and observed["advisory"]
    assert observed["hits"][0]["name"] == "Nat.add_comm"
    assert "ℕ" in observed["hits"][0]["type"]
    assert base64.b64decode(observed["raw_response_b64"]) == response["body"]
    assert observed["raw_response_sha256"] == hashlib.sha256(response["body"]).hexdigest()
    assert observed["raw_response_complete"] and not observed["hits_truncated"]
    parsed = urllib.parse.urlsplit(calls[0][0])
    assert parsed.scheme == "https" and parsed.netloc == "loogle.lean-lang.org" and parsed.path == "/json"
    assert urllib.parse.parse_qs(parsed.query) == {"q": [query]}
    assert calls[0][1:] == (10, loogle.RESPONSE_BYTES)
    loogle.search('https://other.invalid/?q=x&url=y', transport=script)
    assert urllib.parse.urlsplit(calls[-1][0]).netloc == "loogle.lean-lang.org"
    for query in (None, "", "x\ny", "x\0y", "é" * (loogle.QUERY_BYTES // 2 + 1), "\ud800"):
        before = len(calls)
        assert loogle.search(query, transport=script)["status"] == "refused"
        assert len(calls) == before
    for setting in ({"timeout": 0}, {"timeout": 100}, {"max_hits": 0}, {"max_hits": 21}):
        assert loogle.search("Nat", transport=script, **setting)["status"] == "refused"
    cases = [(reply({"count": 0, "hits": []}), "empty"),
             (reply({"error": "unknown identifier"}), "error"), (reply({}, 503), "unavailable"),
             (reply({}, 429), "unavailable"), (reply({}, 403), "error"), (reply({}, 302), "error"),
             (reply({"count": 1, "hits": []}), "error"), (reply({"count": False, "hits": []}), "error"),
             (reply({"count": 1, "hits": [{"name": "x"}]}), "error"),
             ({"http_status": 200, "headers": {}, "body": b"not JSON"}, "error"),
             ({"http_status": 200, "headers": {}, "body": b"\xff"}, "error"),
             ({"http_status": 200, "headers": {},
               "body": b'{"count":1,"hits":[{"name":"\\ud800","type":"Prop"}]}'}, "error")]
    for response, expected in cases:
        result = loogle.search("Nat", transport=lambda *_: response)
        assert result["status"] == expected, result
        assert not result["hits"] and result["raw_response_complete"]
    oversized = {"http_status": 200, "headers": {}, "body": b"x" * (loogle.RESPONSE_BYTES + 1)}
    result = loogle.search("Nat", transport=lambda *_: oversized)
    assert result["status"] == "error" and not result["raw_response_complete"]
    assert result["retained_bytes"] == loogle.RESPONSE_BYTES
    assert len(base64.b64decode(result["raw_response_b64"])) == loogle.RESPONSE_BYTES
    response = reply({"count": 3, "hits": [{"name": "a", "type": "Prop"}, {"name": "b", "type": "Prop"}]})
    result = loogle.search("Nat", max_hits=1, transport=lambda *_: response)
    assert len(result["hits"]) == 1 and result["service_count"] == 3 and result["hits_truncated"]

    def timeout(*_):
        raise TimeoutError("scripted deadline")

    def unavailable(*_):
        raise OSError("scripted unavailable")

    assert loogle.search("Nat", transport=timeout)["reason"] == "timeout"
    assert loogle.search("Nat", transport=unavailable)["status"] == "unavailable"
    assert loogle.search("Nat", transport=lambda *_: None)["status"] == "error"
    for url in ("http://loogle.lean-lang.org/json?q=x", "https://other.invalid/json?q=x",
                "https://loogle.lean-lang.org/other?q=x", "https://loogle.lean-lang.org/json?q=x#fragment"):
        try:
            loogle._fetch(url, 1, 100)
        except ValueError:
            pass
        else:
            raise AssertionError("nonfixed URL admitted")
    json.dumps(observed, ensure_ascii=False)
    print("Loogle fixed-origin records, bounds, schema and scripted failures passed; no live calls")


if __name__ == "__main__":
    check()
