#!/usr/bin/env bash
# Stop the CI build once, before the runner runs out of memory, so the runner survives
# and the cache-save step still runs. The next run continues from the saved modules.
while sleep 1; do
  read -r avail swapfree swaptotal < <(awk '/^MemAvailable:/{a=$2} /^SwapFree:/{f=$2} /^SwapTotal:/{t=$2} END{print a, f, t}' /proc/meminfo)
  if (( avail < 512 * 1024 || swaptotal - swapfree > 2 * 1024 * 1024 )); then
    echo "::error::memory watchdog: stopping the build (available ${avail} kB, swap used $((swaptotal - swapfree)) kB)"
    free -m
    pkill -x lake
    pkill -x lean
    exit 0
  fi
done
