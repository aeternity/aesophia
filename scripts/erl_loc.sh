#!/usr/bin/env bash
set -euo pipefail

# Print line counts for Erlang source files, excluding build artifacts.
# By default, only files under `src/` are considered. Pass --with-tests to include `test/`.

usage() {
  cat <<EOF
Usage: $(basename "$0") [--with-tests]

Lists line counts for tracked .erl files (excluding _build) sorted ascending.

Options:
  --with-tests   Include tracked .erl files under test/ in addition to src/
  -h, --help     Show this help message
EOF
}

include_tests=false
if [[ "${1-}" == "-h" || "${1-}" == "--help" ]]; then
  usage
  exit 0
elif [[ "${1-}" == "--with-tests" ]]; then
  include_tests=true
fi

repo_root="$(pwd)"

# Directories to scan
search_dirs=("$repo_root/src")
if $include_tests; then
  search_dirs+=("$repo_root/test")
fi

# Collect files safely with NUL separator
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

find "${search_dirs[@]}" -type f -name '*.erl' -print0 > "$tmp" || true

if [[ ! -s "$tmp" ]]; then
  echo "No .erl files found under specified paths." >&2
  exit 0
fi

xargs -0 wc -l < "$tmp" | sort -n


