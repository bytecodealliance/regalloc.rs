#!/bin/bash

set -e

TARGET=${1:-bt}
JOBS=${2:-1}

echo "Fuzzing target $TARGET with $JOBS jobs."

cargo +nightly fuzz run --release --jobs=$JOBS $TARGET -- -rss_limit_mb=0 -max_len=1048576 -len_control=0
