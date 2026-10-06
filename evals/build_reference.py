"""Bounded owner-side dependency preparation and reference build, before any worker is admitted."""
import argparse
import json
import os
import sys
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("runtime", type=Path)
    parser.add_argument("kernel", type=Path)
    parser.add_argument("stage", choices=("cache", "cache-complete", "reference", "reference-retry"))
    args = parser.parse_args()
    sys.path.insert(0, str(args.kernel / "run"))
    from processes import run_bounded
    runtime = args.runtime.resolve()
    tools = runtime / "lean-4.29.1-linux"
    os.environ["PATH"] = str(tools / "bin") + ":/usr/bin:/bin"
    os.environ["LEAN_NUM_THREADS"] = "2"
    os.environ["MATHLIB_CACHE_DIR"] = str(runtime / "download-cache")
    modules = ["FTQCLib.Stabilizer.ZShearCheck", "FTQCLib.Carrier.ResidualBit",
               "FTQCLib.Carrier.HadamardAmplitudeCheck"]
    if args.stage == "cache-complete":
        command = [str(tools / "bin/lake"), "exe", "cache", "get", "Mathlib"]
    elif args.stage == "cache":
        command = [str(tools / "bin/lake"), "exe", "cache", "get", "--skip-proofwidgets", *modules]
    else:
        command = [str(tools / "bin/lake"), "build", *modules]
    command = ["/usr/bin/prlimit", "--as=7516192768", "--core=0", "--", *command]
    receipt = runtime / (args.stage + "-receipt.json")
    if receipt.exists():
        raise ValueError("stage receipt exists; retain it and use a new preparation root/version")
    started = time.monotonic()
    outcome = run_bounded(command, str(runtime / "reference"), 1200,
                          stdout_path=str(runtime / (args.stage + ".stdout")))
    (runtime / (args.stage + ".stderr")).write_bytes(outcome.pop("stderr"))
    outcome.pop("stdout")
    value = {"schema": 1, "stage": args.stage, "command": command, "elapsed_seconds": time.monotonic() - started,
             "threads": 2, "scope": modules, "result": outcome}
    receipt.write_text(json.dumps(value, indent=2))
    print(json.dumps(value, indent=2))
    print((runtime / (args.stage + ".stderr")).read_text(errors="replace")[-1800:])
    return 0 if outcome["exit"] == 0 and not outcome["survived"] else 1


if __name__ == "__main__":
    sys.exit(main())
