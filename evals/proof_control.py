#!/usr/bin/env python3
"""Submit owner commands to a proof study without waiting for its execution lock."""
import argparse
import json
from pathlib import Path

import chain_kernel
import study


def execute(root, words):
    manifest = json.loads((root / "manifest.json").read_bytes())
    if study.digest(study.canonical(manifest)) != (root / "manifest.ref").read_text().strip():
        raise ValueError("manifest identity differs")
    if not manifest.get("proof_program"):
        raise ValueError("this study was prepared without a proof program")
    chain_kernel.native_modules(manifest["kernel"])
    import control_cli
    config = root / "driver-config.json"
    if json.loads(config.read_bytes()) != manifest["kernel_config"]:
        raise ValueError("driver command configuration differs from the manifest")
    return control_cli.execute(str(root / "worktree"), manifest["id"], words, str(config))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("study", type=Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    result, code = execute(args.study.resolve(), args.command)
    print(json.dumps(result))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
