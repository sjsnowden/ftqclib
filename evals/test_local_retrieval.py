"""Model-free integration controls over a real pinned local search snapshot."""
import argparse
import json
from pathlib import Path
import tempfile
import time
import uuid

import local_retrieval as local
import retrieval_loop
import runtime
import study


def request(kind, payload):
    value = {"action": kind, "proof": None, "query": None, "name": None, "reason": None}
    value["query" if kind == "search" else "name"] = payload
    return json.dumps(value)


class Controls:
    def __init__(self, args):
        Store, self.checker, _ = study.kernel_imports(args.kernel)
        self.store = Store(str(args.output / "records"))
        self.rows, self.observations = [], []
        identity = (args.snapshot / "snapshot.ref").read_text().strip()
        started = time.monotonic()
        self.backend = local.Backend(args.snapshot, identity, self.store, self.checker)
        self.admission_seconds = time.monotonic() - started

    def check(self, name, condition):
        self.rows.append({"name": name, "passed": bool(condition)})
        print(json.dumps(self.rows[-1]), flush=True)
        if not condition:
            raise AssertionError(name)

    def call(self, operation, payload):
        started = time.monotonic()
        result = self.backend.call(operation, payload)
        self.observations.append({"operation": operation, "payload": payload, "result": result,
                                  "wall_seconds": time.monotonic() - started})
        return result

    def real_queries(self):
        first = self.call("search", '"IsCosetLeaderMap"')
        self.check("local ECCLib search", first["status"] == "ok" and any(
            hit["name"] == "ECCLib.Coding.IsCosetLeaderMap" for hit in first["hits"]))
        repeat = self.call("search", '"IsCosetLeaderMap"')
        self.check("same snapshot/query/policy reuses receipt", repeat["cache_hit"] and repeat["hits"] == first["hits"]
                   and json.loads(self.store.get(repeat["receipt"]))["reused_receipt"] == first["receipt"])
        css = self.call("search", '"cssX_correct_of_weights_le"')
        self.check("local FTQCLib search", css["status"] == "ok" and any(
            hit["name"] == "FTQCLib.CSS.cssX_correct_of_weights_le" for hit in css["hits"]))
        mathlib = self.call("search", "ZMod, _ + _ = 0")
        self.check("pinned Mathlib type search", mathlib["status"] == "ok" and any(
            hit["name"] == "ZModModule.add_self" for hit in mathlib["hits"]))
        definition = self.call("read_declaration", ["FTQCLib", "CSS", "CorrectsUpToBoundary"])
        self.check("definition has bounded type/body and exact origin", definition["status"] == "ok"
                   and definition["kind"] == "definition" and definition["body"]["text"]
                   and definition["origin_module"] == ["FTQCLib", "CSS", "SurfaceCode"])
        theorem = self.call("read_declaration", ["ECCLib", "Coding", "exists_cosetLeaderMap"])
        self.check("theorem lookup does not expose proof body", theorem["status"] == "ok"
                   and theorem["kind"] == "theorem" and theorem["body"] is None)
        missing = self.call("read_declaration", ["FTQCLib", "Stabilizer", "zShearBy"])
        self.check("unadmitted project module is absent", missing["status"] == "missing"
                   and "FTQCLib.Stabilizer.ZShear" not in self.backend.spec["module_origins"])
        empty = self.call("search", '"ontologic_unaccepted_canary_983247"')
        self.check("zero hits is an explicit empty result", empty["status"] == "empty" and empty["count"] == 0)
        invalid = self.call("search", "(")
        flag = self.call("search", "--help")
        self.check("syntax errors and option-shaped input stay queries", invalid["status"] == "invalid_query"
                   and flag["status"] == "invalid_query")
        refused = [self.call(op, payload) for op, payload in
                   [("bash", "git diff"), ("read_declaration", ["../answers"]), ("search", "a\nb"),
                    ("search", "a" * 513), ("read_declaration", ["A"] * 33)]]
        self.check("paths/commands/oversize payloads refuse without process", all(
            result["status"] == "refused" and "execution" not in json.loads(self.store.get(result["receipt"]))
            for result in refused))

    def owner_loop(self):
        session = retrieval_loop.Session(self.backend, 2, self.backend.snapshot)
        first = session.dispatch(request("search", '"IsCosetLeaderMap"'))
        second = session.dispatch(request("read_declaration", ["ECCLib", "Coding", "IsCosetLeaderMap"]))
        third = session.dispatch(request("search", "Nat"))
        self.check("real owner loop binds results and enforces shared budget", first["status"] == "retrieval_result"
                   and second["status"] == "retrieval_result" and third["status"] == "refused"
                   and session.requests_used == 2)
        packet = retrieval_loop.packet({"obligation": "decoder bridge retrieval control"}, self.backend.policy,
                                       self.backend.snapshot, requests_left=0, retrieved=session.retrieved)
        self.check("next packet has current retrieved definition and exhausted capabilities",
                   packet["retrieved"]["name"] == ["ECCLib", "Coding", "IsCosetLeaderMap"]
                   and packet["capabilities"] == ["check_candidate", "blocked"])
        receipt = json.loads(self.store.get(first["response"]["receipt"]))
        self.check("retained request and result bind snapshot", receipt["snapshot"] == self.backend.snapshot and
                   json.loads(self.store.get(receipt["request"]))["snapshot"] == self.backend.snapshot)

    def stale_indexes(self):
        with tempfile.TemporaryDirectory(prefix="retrieval-index-controls-") as temporary:
            root = Path(temporary)
            (root / "candidate").mkdir()
            study.write_new(root / "stale.trace", b'{"depHash":"different-accepted-input"}')
            for label in ("missing", "stale"):
                index = "/deps/snapshot/index/absent.index" if label == "missing" else "/deps/snapshot/index/loogle.index"
                command = ["/deps/snapshot/bin/loogle", "--path", "/deps/snapshot/lib", "--module",
                           "OntologicSearchScope", "--index-mode", "read", "--index-file", index, "--json", "Nat"]
                reads = [(str(self.backend.content), "/deps/snapshot")]
                if label == "stale":
                    reads += [(str(root / "stale.trace"), "/deps/snapshot/lib/OntologicSearchScope.trace")]
                result = self.checker.run(str(root / "candidate"), command, self.store,
                                          "index-" + uuid.uuid4().hex, readonly=reads,
                                          environment={"LEAN_NUM_THREADS": "2"}, memory_bytes=8 * 1024**3,
                                          deadline_seconds=30, log_bytes_max=65536)
                output = local.streams(self.store, result)
                diagnostic = b"".join(output.values()).decode(errors="replace")
                self.check(label + " index refuses, never rebuilds", result["status"] == "failed" and
                           ("no index file" if label == "missing" else "is stale") in diagnostic)
                self.observations.append({"control": label + "_index", "execution": result})
        self.check("real snapshot unchanged by failure controls", self.backend.unchanged())

    def tampering(self):
        with tempfile.TemporaryDirectory(prefix="retrieval-tamper-control-") as temporary:
            root = Path(temporary)
            (root / "content").mkdir()
            study.write_new(root / "content/input", b"accepted")
            binding = {"artifacts": runtime.tree_manifest(root / "content")}
            closure = study.digest(study.canonical(binding))
            study.write_new(root / "content/lib/OntologicSearchScope.trace",
                            study.canonical({"depHash": "ontologic-sha256:" + closure}))
            study.write_new(root / "content/index/loogle.index", b"control-index")
            spec = {"schema": 1, "scope": "OntologicSearchScope", "closure": closure, "binding": binding,
                    "plan": {"max_hits": 5, "lookup_bytes": 8192}, "files": runtime.tree_manifest(root / "content")}
            raw = study.canonical(spec)
            study.write_new(root / "snapshot.json", raw)
            backend = local.Backend(root, study.digest(raw), self.store, self.checker)
            (root / "content/input").write_bytes(b"replaced")
            outcome = backend.call("search", "Nat")
            self.check("post-admission byte replacement refuses", outcome["status"] == "unavailable")
            try:
                local.Backend(root, study.digest(raw), self.store, self.checker)
                rejected = False
            except ValueError:
                rejected = True
            self.check("fresh admission detects artifact tampering", rejected)
            try:
                local.Backend(root, "0" * 64, self.store, self.checker)
                rejected = False
            except ValueError:
                rejected = True
            self.check("wrong immutable snapshot identity refuses", rejected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("snapshot", "kernel", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    controls = Controls(args)
    try:
        controls.real_queries()
        controls.owner_loop()
        controls.stale_indexes()
        controls.tampering()
    finally:
        study.write_new(args.output / "report.json", study.canonical({
            "schema": 1, "snapshot": controls.backend.snapshot, "admission_seconds": controls.admission_seconds,
            "checks": controls.rows, "observations": controls.observations,
            "worker_model_calls": 0, "worker_tokens": 0}))


if __name__ == "__main__":
    main()
