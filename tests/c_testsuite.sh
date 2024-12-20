#!/bin/bash

# imports assert_snapshot
source ./tests/util.sh

PASSED=0
FAILED=0
FAILED_OUTPUTS=""

$(RUSTFLAGS="-A warnings" cargo b -q --release)

if [[ -z "${C_TESTSUITE}" ]]; then
  echo "Error: requires C_TESTSUITE env var to be set to c-testsuite installation path"
  exit 1
fi

for file in "$C_TESTSUITE"/tests/single-exec/*; do 
  if [[ ! $file =~ tags$ ]]; then
    if [[ ! $file =~ expected$ ]]; then
      if [ -f "$file" ]; then
        filename=$(basename "$file")
        snapshot="${filename}.expected"
        assert_snapshot $snapshot "$file" "$filename" "$C_TESTSUITE"/tests/single-exec
      fi
    fi
  fi
done

# Prints out test-results
printf "\nTests passed: $PASSED\nTests failed: $FAILED\n"
