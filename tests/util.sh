# Exposes a generic assertion function to compare snapshots

function assert_snapshot {
  if [ $# -eq 4 ]; then
    local snapshot=$1
    local fixture=$2
    local name=$3
    local dir=$4
  else
    echo "assert_eq accepts 4 arguments"
    exit 1
  fi

$(RUSTFLAGS="-A warnings" ./target/release/wrecc "$fixture" --no-color 2> static_err)
  
  found_error=$(cat static_err)
  if [[ "$found_error" = "" ]]; then
    $(./a.out >& tmp)
  else
    $(cat static_err >& tmp)
  fi
  result=$(diff "$dir"/"$snapshot" tmp 2> err)
  error=$(cat err)

  local pass=0
  if [[ "$result" = "" && "$error" = "" ]];
    then 
      let "PASSED += 1"
      pass=1
      printf "\x1b[32mPASSED!\x1b[0m $name\n"
    else 
      let "FAILED += 1"
      printf "\x1b[31mFAILED!\x1b[0m $name\n"
      FAILED_OUTPUTS+="\n==============================\n"
      FAILED_OUTPUTS+="\x1b[31mFAILED!\x1b[0m $name\n"
      FAILED_OUTPUTS+="expected: '$(cat "$dir"/"$snapshot" 2>/dev/null)'"$'\n'
      FAILED_OUTPUTS+="actual: '$(cat tmp 2>/dev/null)'"$'\n'
  fi

  if [[ "$found_error" = "" ]]; then
    rm a.out
  fi
  rm static_err
  rm tmp
  rm err

  return $pass
}
