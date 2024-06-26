#!/bin/bash

PASSED=0
FAILED=0

$(RUSTFLAGS="-A warnings" cargo b -q --release)

function assert_eq {
  if [ $# -eq 3 ]; then
    local snapshot=$1
    local fixture=$2
    local name=$3
  else
    echo "assert_eq accepts 3 arguments"
    exit 1
  fi

$(RUSTFLAGS="-A warnings" ./target/release/wrecc "$fixture" --no-color 2> static_err)
  
  found_error=$(cat static_err)
  if [[ "$found_error" = "" ]]; then
    $(./a.out >& tmp)
  else
    $(cat static_err >& tmp)
  fi
  result=$(diff tests/snapshots/"$snapshot" tmp 2> err)
  error=$(cat err)

  if [[ "$result" = "" && "$error" = "" ]];
    then printf "\x1b[32mPASSED!\x1b[0m $name\n"; let "PASSED += 1"
    else printf "\x1b[31mFAILED!\x1b[0m $name\nexpected: '$(cat tests/snapshots/"$snapshot")'\nactual: '$(cat tmp)'\n\n"; let "FAILED += 1"
  fi

  if [[ "$found_error" = "" ]]; then
    rm a.out
  fi
  rm static_err
  rm tmp
  rm err
}

# Runs all files in fixtures-directory
for file in tests/fixtures/*; do 
  if [ -f "$file" ]; then
    filename=$(echo "$file" | cut -d/ -f3)
    snapshot="success_${filename::${#filename}-2}"
    assert_eq $snapshot "$file" "$filename"
  fi
done

# Prints out test-results
printf "\nTests passed: $PASSED\nTests failed: $FAILED\n"
if [ $FAILED -gt 0 ]; then
  exit 1
fi
