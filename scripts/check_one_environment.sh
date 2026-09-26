#!/bin/sh
# Check that every module of ECCLib and FTQCLib can be imported into one Lean environment.
#
# `lake build` compiles each file separately, so two modules that nothing imports together can
# define the same name without an error. This script writes a Lean file importing every module
# under `ECCLib/` and `FTQCLib/` and compiles it; a name defined by two modules fails the import
# with "environment already contains '<name>'". Run it from the repository root after `lake build`.
# The import takes about two minutes and some gigabytes of memory.
set -eu

cd "$(dirname "$0")/.."

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT INT TERM

file="$tmp/OneEnvironment.lean"
find ECCLib FTQCLib -name '*.lean' | LC_ALL=C sort | sed 's|\.lean$||; s|/|.|g; s|^|import |' > "$file"
echo "#eval IO.println \"imported $(wc -l < "$file") modules into one environment\"" >> "$file"

out="$tmp/out.txt"
status=0
lake env lean "$file" > "$out" 2>&1 || status=$?
cat "$out"
if [ "$status" -ne 0 ] || grep -q 'error' "$out"; then
  echo "check_one_environment: FAILED" >&2
  exit 1
fi
echo "check_one_environment: OK"
