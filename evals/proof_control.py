#!/usr/bin/env python3
"""Submit owner commands to a proof study without waiting for its execution lock."""
import argparse
import json
from pathlib import Path
import sys

import chain_kernel
import study


def execute(root, words=(), data=None):
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
    if data is not None:
        if words:
            raise ValueError("structured submission does not take command arguments")
        return control_cli.request_json(str(root / "worktree"), manifest["id"], str(config), data)
    return control_cli.execute(str(root / "worktree"), manifest["id"], words, str(config))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("study", type=Path)
    parser.add_argument("--request-json", action="store_true", help="Read a canonical typed or legacy request from stdin")
    parser.add_argument("--request-file", type=Path, help="Read the same canonical request from a file")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        if args.request_json and args.request_file:
            raise ValueError("select stdin or file submission")
        if args.request_file:
            with args.request_file.open("rb") as handle:
                data = handle.read(1024 * 1024 + 1)
        else:
            data = sys.stdin.buffer.read(1024 * 1024 + 1) if args.request_json else None
        result, code = execute(args.study.resolve(), args.command, data)
    except (OSError, ValueError, TypeError, KeyError, ImportError) as error:
        result, code = {"status": "error", "reason": str(error)}, 2
    print(json.dumps(result))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
