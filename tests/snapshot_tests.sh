#!/bin/bash

# imports assert_snapshot
source ./tests/util.sh

PASSED=0
FAILED=0
FAILED_OUTPUTS=""

$(RUSTFLAGS="-A warnings" cargo b -q --release)

# Runs all files in fixtures-directory
for file in tests/fixtures/*; do 
  if [ -f "$file" ]; then
    filename=$(echo "$file" | cut -d/ -f3)
    snapshot="success_${filename::${#filename}-2}"
    assert_snapshot $snapshot "$file" "$filename" tests/snapshots
  fi
done

# Prints out test-results
printf "$FAILED_OUTPUTS"
printf "\nTests passed: $PASSED\nTests failed: $FAILED\n"
if [ $FAILED -gt 0 ]; then
  exit 1
fi
