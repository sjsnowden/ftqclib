"""Trusted child entry point. The owner supplies one request and read-only snapshot.

No request field becomes a path, module import, executable, environment or option.
Outer eval_check owns network isolation, resource limits, capture and child cleanup.
"""
import json
from pathlib import Path
import subprocess
import sys


def main():
    request = json.loads(Path("/work/request.json").read_bytes())
    root = Path("/deps/snapshot")
    if request["operation"] == "search":
        command = [str(root / "bin/loogle"), "--path", str(root / "lib"),
                   "--module", "OntologicSearchScope", "--index-mode", "read",
                   "--index-file", str(root / "index/loogle.index"), "--json", "--interactive",
                   "--max-results", str(request["max_hits"])]
        data = (request["payload"] + "\n").encode("utf-8")
    elif request["operation"] in ("read_declaration", "inventory"):
        command = [str(root / "bin/declaration-lookup")]
        value = {"op": "lookup" if request["operation"] == "read_declaration" else "inventory",
                 "modules": [["OntologicSearchScope"]]}
        if request["operation"] == "read_declaration":
            value["name"] = request["payload"]
        data = json.dumps(value, ensure_ascii=False).encode("utf-8")
    else:
        raise ValueError("operation outside owner driver")
    return subprocess.run(command, input=data, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())
