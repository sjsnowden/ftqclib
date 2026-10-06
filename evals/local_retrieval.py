"""Owner-side, snapshot-bound local search and declaration lookup; no model tools.

Snapshots are immutable owner inputs, never worker-writable. One owner process
audits bytes on admission then checks full metadata before/after each request.
This assumes no hostile local OS user, like runtime.py. Query cache is local to
that owner process; raw executions and compact receipts are durable Store objects.
"""
import argparse
import base64
import json
from pathlib import Path
import re
import tempfile
import time
import uuid

import runtime
import study

QUERY_BYTES = 512
RESULT_BYTES = 32768


def valid_name(value):
    if not isinstance(value, list) or not 1 <= len(value) <= 32:
        return False
    try:
        return all(isinstance(part, str) and 0 < len(part.encode("utf-8")) <= 256
                   and not any(char in part for char in "\x00\r\n/\\") for part in value)
    except UnicodeError:
        return False


def refusal(operation, payload):
    if operation == "read_declaration":
        return None if valid_name(payload) else "invalid declaration name components"
    if operation != "search":
        return "operation is not granted"
    try:
        valid = isinstance(payload, str) and bool(payload.strip()) and len(payload.encode()) <= QUERY_BYTES
        valid = valid and not any(ord(char) < 32 for char in payload)
    except UnicodeError:
        valid = False
    return None if valid else "query must be one nonempty bounded UTF-8 line"


def streams(store, result):
    found = {"stdout": b"", "stderr": b""}
    for line in store.get(result["capture"]).splitlines():
        row = json.loads(line)
        if row.get("kind") == "bytes":
            found[row["stream"]] += base64.b64decode(row["data_base64"], validate=True)
    return found


def observe(content, operation, payload, store, checker, *, max_hits=5, seconds=30):
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="local-retrieval-") as temporary:
        candidate = Path(temporary)
        study.write_new(candidate / "request.json", study.canonical(
            {"operation": operation, "payload": payload, "max_hits": max_hits}))
        result = checker.run(str(candidate), ["/usr/bin/python3", "-B", "/deps/snapshot/driver.py"],
                             store, "retrieval-" + uuid.uuid4().hex,
                             readonly=[(str(content), "/deps/snapshot")],
                             environment={"LEAN_PATH": "/deps/snapshot/lib", "LEAN_NUM_THREADS": "2"},
                             deadline_seconds=seconds, log_bytes_max=256 * 1024,
                             memory_bytes=8 * 1024**3)
    return result, streams(store, result), time.monotonic() - started


def clip(value, limit):
    raw = value.encode("utf-8")
    return {"text": raw[:limit].decode("utf-8", errors="ignore"), "truncated": len(raw) > limit}


def normalize_search(data, max_hits):
    if isinstance(data.get("error"), str):
        return {"status": "invalid_query", "reason": clip(data["error"], 1024), "hits": []}
    count, hits = data.get("count"), data.get("hits")
    if (type(count) is not int or count < 0 or not isinstance(hits, list) or not len(hits) <= count
            or (count > 0 and not hits)):
        raise ValueError("unsupported Loogle response schema")
    normalized = []
    for hit in hits[:max_hits]:
        if (not isinstance(hit, dict) or not isinstance(hit.get("name"), str)
                or not isinstance(hit.get("type"), str) or not isinstance(hit.get("module"), str)):
            raise ValueError("invalid declaration hit")
        if len(hit["name"].encode()) > 1024 or len(hit["module"].encode()) > 1024:
            raise ValueError("declaration identity byte bound")
        normalized.append({"name": hit["name"], "module": hit["module"],
                           "type": clip(hit["type"], 2048)})
    return {"status": "ok" if hits else "empty", "count": count, "hits": normalized,
            "hits_truncated": count > len(normalized)}


def normalize_lookup(data, limit):
    if data.get("status") not in ("ok", "missing", "error"):
        raise ValueError("unsupported declaration response schema")
    if data["status"] == "ok":
        if not valid_name(data.get("name")) or not valid_name(data.get("origin_module")):
            raise ValueError("invalid declaration or origin identity")
        if data.get("kind") != "definition" and data.get("body") is not None:
            raise ValueError("non-definition body disclosure")
        # Preserve the type first, then bounded documentation and definition text.
        for key in ("type", "docstring", "body"):
            value = data.get(key)
            if value is not None and (not isinstance(value, dict) or not isinstance(value.get("text"), str)):
                raise ValueError("invalid declaration text")
        while len(study.canonical(data)) > limit:
            choices = [key for key in ("body", "docstring", "type") if data.get(key) and data[key]["text"]]
            if not choices:
                raise ValueError("declaration metadata byte bound")
            key = choices[0]
            data[key]["text"] = data[key]["text"][:len(data[key]["text"]) // 2]
            data[key].update(truncated=True, retained_bytes=len(data[key]["text"].encode()))
    if len(study.canonical(data)) > limit:
        raise ValueError("declaration result byte bound")
    return data


def interpret(operation, raw, policy):
    lines = raw.splitlines()
    if operation == "search" and lines and lines[0] == b"Loogle is ready.":
        lines = lines[1:]
    if len(lines) != 1:
        raise ValueError("expected exactly one result")
    data = json.loads(lines[0])
    if not isinstance(data, dict):
        raise ValueError("result is not an object")
    return normalize_search(data, policy["max_hits"]) if operation == "search" else normalize_lookup(
        data, policy["lookup_bytes"])


def validate_binding(spec):
    if spec.get("schema") != 1 or spec.get("scope") != "OntologicSearchScope":
        raise ValueError("unknown retrieval snapshot format")
    binding, files = spec["binding"], spec["files"]
    if study.digest(study.canonical(binding)) != spec["closure"]:
        raise ValueError("snapshot dependency binding differs")
    originals = binding["artifacts"]
    if set(files) != set(originals) | {"lib/OntologicSearchScope.trace", "index/loogle.index"}:
        raise ValueError("snapshot artifact set differs from index inputs")
    if any(any(files[path][key] != value[key] for key in ("sha256", "bytes")) for path, value in originals.items()):
        raise ValueError("sealed artifacts differ from original index inputs")


class Backend:
    def __init__(self, snapshot, expected_id, store, checker, *, lease=None):
        self.root, self.store, self.checker = Path(snapshot).resolve(), store, checker
        raw = (self.root / "snapshot.json").read_bytes()
        if not re.fullmatch(r"[0-9a-f]{64}", expected_id) or study.digest(raw) != expected_id:
            raise ValueError("snapshot identity differs from admitted work item")
        self.snapshot, self.spec = expected_id, json.loads(raw)
        validate_binding(self.spec)
        self.content, self.cache = self.root / "content", {}
        self.policy = self.spec["plan"]
        if (type(self.policy["max_hits"]) is not int or not 1 <= self.policy["max_hits"] <= 5
                or type(self.policy["lookup_bytes"]) is not int or not 1024 <= self.policy["lookup_bytes"] <= 8192):
            raise ValueError("snapshot result bounds")
        self.lease = lease
        if lease is None:
            before = runtime.tree_metadata(self.content)
            if runtime.tree_manifest(self.content) != self.spec["files"]:
                raise ValueError("snapshot artifact bytes differ")
            self.metadata = runtime.tree_metadata(self.content)
            if before != self.metadata:
                raise ValueError("snapshot changed during admission")
        elif lease.snapshot != self.snapshot or lease.content != self.content or not lease.unchanged():
            raise ValueError("runtime lease does not bind this retrieval snapshot")
        if json.loads((self.content / "lib/OntologicSearchScope.trace").read_bytes())["depHash"] != "ontologic-sha256:" + self.spec["closure"]:
            raise ValueError("index trace differs from snapshot binding")
        self.code = store.put(Path(__file__).read_bytes())

    def unchanged(self):
        if self.lease is not None:
            return self.lease.unchanged()
        return runtime.tree_metadata(self.content) == self.metadata

    def record(self, request, result, **details):
        record = {"schema": 1, "snapshot": self.snapshot, "request": request,
                  "result": result, "owner_code": self.code, **details}
        receipt = self.store.put(study.canonical(record))
        study.event(self.store, self.snapshot, "retrieval_result", request=request, result_object=receipt,
                    detail=result["status"])
        return {**result, "snapshot": self.snapshot, "receipt": receipt, "advisory": True}

    def call(self, operation, payload):
        reason = refusal(operation, payload)
        admitted = {"operation": operation, "payload": payload} if reason is None else {
            "operation": operation[:64] if isinstance(operation, str) else None,
            "refusal": reason, "payload_retained": False}
        request = self.store.put(study.canonical({"snapshot": self.snapshot, **admitted,
                                                "policy": self.policy, "code": self.code}))
        if reason:
            return self.record(request, {"status": "refused", "reason": reason})
        try:
            if not self.unchanged():
                raise ValueError("snapshot changed after admission")
            if request in self.cache:
                return self.record(request, {**self.cache[request]["result"], "cache_hit": True},
                                   reused_receipt=self.cache[request]["receipt"])
            execution, output, elapsed = observe(self.content, operation, payload, self.store, self.checker,
                                                 max_hits=self.policy["max_hits"])
            if not self.unchanged():
                raise ValueError("snapshot changed during retrieval")
        except (OSError, ValueError) as error:
            return self.record(request, {"status": "unavailable", "reason": str(error)[:512]})
        try:
            result = interpret(operation, output["stdout"], self.policy) if execution["status"] == "completed" else {
                "status": "unavailable", "reason": execution["status"]}
        except (ValueError, UnicodeError, RecursionError) as error:
            result = {"status": "error", "reason": str(error)[:512]}
        answer = self.record(request, {**result, "cache_hit": False}, execution=execution,
                             elapsed_seconds=elapsed)
        if result["status"] in ("ok", "empty", "missing", "invalid_query"):
            self.cache[request] = {"result": result, "receipt": answer["receipt"]}
        return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("snapshot_id")
    parser.add_argument("--kernel", type=Path, required=True)
    parser.add_argument("--records", type=Path, required=True)
    parser.add_argument("--request", required=True, help='JSON: {"operation":"search","payload":"..."}')
    args = parser.parse_args()
    Store, checker, _ = study.kernel_imports(args.kernel)
    backend = Backend(args.snapshot, args.snapshot_id, Store(str(args.records)), checker)
    request = json.loads(args.request)
    if set(request) != {"operation", "payload"}:
        raise ValueError("request fields differ")
    print(json.dumps(backend.call(request["operation"], request["payload"])))


if __name__ == "__main__":
    main()
