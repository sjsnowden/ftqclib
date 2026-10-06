"""Owner-only preparation of the pinned Linux Lean runtime; never invoked by a worker."""
import argparse
import hashlib
import io
import json
import subprocess
import tarfile
import urllib.request
from pathlib import Path


def prepare_toolchain(root):
    """Fetch the named official release, verify its published digest, and retain provenance."""
    root.mkdir(parents=True, exist_ok=True)
    target = root / "lean-4.29.1-linux"
    receipt = root / "toolchain.json"
    if target.exists():
        if not receipt.is_file():
            raise ValueError("existing toolchain has no preparation receipt")
        return json.loads(receipt.read_text())
    api = "https://api.github.com/repos/leanprover/lean4/releases/tags/v4.29.1"
    request = urllib.request.Request(api, headers={"User-Agent": "ftqclib-eval-preparation"})
    with urllib.request.urlopen(request, timeout=30) as response:
        release = json.load(response)
    asset = next(a for a in release["assets"] if a["name"] == "lean-4.29.1-linux.tar.zst")
    if not asset.get("digest", "").startswith("sha256:"):
        raise ValueError("official release metadata does not provide a SHA-256")
    archive = root / asset["name"]
    subprocess.run(["curl", "--fail", "--location", "--silent", "--show-error", "--max-time", "300",
                    "--output", str(archive), asset["browser_download_url"]], check=True, timeout=310)
    digest = hashlib.file_digest(archive.open("rb"), "sha256").hexdigest()
    if digest != asset["digest"][7:] or archive.stat().st_size != asset["size"]:
        raise ValueError("download does not match official asset digest and size")
    with tarfile.open(archive) as handle:
        handle.extractall(root, filter="data")
    version = subprocess.run([str(target / "bin/lean"), "--version"], capture_output=True,
                             check=True, timeout=10).stdout.decode().strip()
    value = {"schema": 1, "release": api, "url": asset["browser_download_url"], "sha256": digest,
             "bytes": asset["size"], "version": version, "path": str(target)}
    with receipt.open("x") as handle:
        json.dump(value, handle, indent=2)
    return value


def prepare_project(root, source):
    """Clone pinned dependency sources privately; no build artifacts come from the live checkout."""
    target = root / "reference"
    if target.exists():
        raise ValueError("reference destination already exists")
    base = "75589c95949b6d290c53405e0cdc31334120e19a"
    archive = subprocess.run(["git", "-c", "safe.directory=" + str(source), "-C", str(source),
                              "archive", base], capture_output=True, check=True, timeout=60).stdout
    target.mkdir()
    with tarfile.open(fileobj=io.BytesIO(archive)) as handle:
        handle.extractall(target, filter="data")
    manifest = json.loads((target / "lake-manifest.json").read_text())
    packages = target / ".lake/packages"
    packages.mkdir(parents=True)
    for package in manifest["packages"]:
        original = source / ".lake/packages" / package["name"]
        checkout = packages / package["name"]
        subprocess.run(["git", "-c", "safe.directory=" + str(original), "clone", "--quiet", "--no-local",
                        "--no-checkout", str(original), str(checkout)], check=True, timeout=180)
        subprocess.run(["git", "-C", str(checkout), "checkout", "--quiet", "--detach", package["rev"]],
                       check=True, timeout=90)
        subprocess.run(["git", "-C", str(checkout), "remote", "set-url", "origin", package["url"]],
                       check=True, timeout=10)
        print("Prepared " + package["name"] + " at " + package["rev"], flush=True)
    value = {"schema": 1, "base": base, "source": str(source), "target": str(target),
             "manifest_sha256": hashlib.sha256((target / "lake-manifest.json").read_bytes()).hexdigest()}
    (root / "project.json").write_text(json.dumps(value, indent=2))
    return value


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--source", type=Path)
    arguments = parser.parse_args()
    print(json.dumps(prepare_toolchain(arguments.root), indent=2))
    if arguments.source:
        print(json.dumps(prepare_project(arguments.root, arguments.source), indent=2))
