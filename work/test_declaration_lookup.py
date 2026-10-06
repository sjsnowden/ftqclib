"""Goal: the pinned lookup emits observed imports/types/docs and never theorem proof terms.

Method: compile isolated synthetic fixtures with the existing Lean toolchain, then perform bounded
stdin requests. Optionally inspect the existing pinned Mathlib cache. No paid workers are used.
"""
import json
import os
from pathlib import Path
import subprocess
import sys


def refused_requests(request):
    for bad in ({"op": "eval", "modules": [["LookupFixture"]]},
                {"op": "inventory", "modules": [["..", "secret"]]},
                {"op": "inventory", "modules": []},
                {"op": "lookup", "modules": [["LookupFixture"]], "name": [1]},
                {"op": "inventory", "modules": [["LookupFixture"]], "padding": "x" * 16385}):
        assert request(bad)["status"] == "error"


def check():
    runtime = Path("/home/sam/ftqclib-eval-runtime")
    compiler = runtime / "lean-4.29.1-linux/bin/lean"
    linker = runtime / "lean-4.29.1-linux/bin/leanc"
    root = runtime / "retrieval-helper-01"
    root.mkdir(exist_ok=True)
    source = Path(__file__).resolve().parents[1] / "evals/DeclarationLookup.lean"
    helper = root / "DeclarationLookup.lean"
    helper.write_bytes(source.read_bytes())
    core = runtime / "lean-4.29.1-linux/lib/lean"
    environment = {**os.environ, "LEAN_PATH": str(root) + ":" + str(core)}

    def compile_module(name, text):
        (root / (name + ".lean")).write_text(text)
        extra = ["-c", "DeclarationLookup.c"] if name == "DeclarationLookup" else []
        result = subprocess.run([str(compiler), "-o", name + ".olean", *extra, name + ".lean"],
                                cwd=root, env=environment, capture_output=True, timeout=60)
        assert result.returncode == 0, result.stdout + result.stderr

    compile_module("LookupBase", "namespace LookupFixture\ndef base : Nat := 17\nend LookupFixture\n")
    compile_module("LookupFixture", 'import LookupBase\nnamespace LookupFixture\n'
                   '/-- Observed definition documentation. -/\ndef increment (n : Nat) : Nat := n + 1\n'
                   '/-- Observed theorem documentation. -/\ntheorem same (n : Nat) : n = n := rfl\n'
                   'def «quoted.dot» : Nat := 3\n'
                   '/-- ' + 'λ' * 1600 + ' -/\ndef longDoc : Nat := 0\n'
                   'def longBody : String := "' + 'x' * 5000 + '"\nend LookupFixture\n')
    compile_module("DeclarationLookup", helper.read_text())
    executable = root / "declaration-lookup"
    linked = subprocess.run([str(linker), "-O2", "-rdynamic", "-o", str(executable), "DeclarationLookup.c"],
                            cwd=root, env=environment, capture_output=True, timeout=60)
    assert linked.returncode == 0, linked.stdout + linked.stderr

    def request(value, paths=None):
        config = environment if paths is None else {**environment, "LEAN_PATH": ":".join(paths)}
        result = subprocess.run([str(executable)], input=json.dumps(value).encode(),
                                cwd=root, env=config, capture_output=True, timeout=60)
        assert result.returncode == 0 and not result.stderr, result.stdout + result.stderr
        assert len(result.stdout) <= 2 * 1024 * 1024
        return json.loads(result.stdout)

    def lookup(name):
        return request({"op": "lookup", "modules": [["LookupFixture"]], "name": ["LookupFixture", name]})

    definition = lookup("increment")
    assert definition["status"] == "ok", definition
    assert definition["kind"] == "definition" and definition["name"] == ["LookupFixture", "increment"]
    assert definition["origin_module"] == ["LookupFixture"] and "Nat" in definition["type"]["text"]
    assert definition["body"]["text"] and "Observed definition" in definition["docstring"]["text"]
    theorem = lookup("same")
    assert theorem["kind"] == "theorem" and theorem["body"] is None
    assert "Observed theorem" in theorem["docstring"]["text"]
    assert lookup("base")["origin_module"] == ["LookupBase"]
    assert lookup("quoted.dot")["name"] == ["LookupFixture", "quoted.dot"]
    assert lookup("missing")["status"] == "missing"
    assert lookup("longDoc")["docstring"]["truncated"]
    assert lookup("longBody")["body"]["truncated"]
    inventory = request({"op": "inventory", "modules": [["LookupFixture"]]})
    assert inventory["status"] == "ok" and ["LookupBase"] in inventory["modules"]
    assert ["LookupFixture"] in inventory["modules"] and inventory["count"] == len(inventory["modules"])
    assert len({tuple(module) for module in inventory["modules"]}) == inventory["count"]
    refused_requests(request)
    if len(sys.argv) > 1:
        paths = [str(root), str(core)] + sys.argv[1:]
        mathlib = request({"op": "lookup", "modules": [["Mathlib", "Data", "ZMod", "Basic"]],
                           "name": ["ZModModule", "add_self"]}, paths)
        assert mathlib["status"] == "ok", mathlib
        assert mathlib["kind"] == "theorem" and mathlib["body"] is None
        assert mathlib["origin_module"] == ["Mathlib", "Data", "ZMod", "Basic"]
        print(json.dumps({"mathlib": mathlib}, ensure_ascii=False))
    print("Pinned Lean declaration lookup fixtures, provenance, inventory and truncation passed")


if __name__ == "__main__":
    check()
