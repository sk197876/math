#!/bin/bash
# Run a Rocq command (make, rocq compile, rocqchk, ...) for the subprojects
# allard1972, DPDRG2018 and DPGPR2026 under the resource policy of
# federer1969/docs/resources.md:
#   - weekdays 07:00-17:00 Europe/Warsaw: at most two such commands at once
#     (two lock slots under /opt/rocq/locks); nights and weekends unrestricted;
#   - always nice 10, umask 0002, group llm and the pinned opam switch.
# Usage: tools/rocq_run.sh COMMAND [ARGS...]   (run from any directory)
set -euo pipefail
SWITCH='RP.2026.02.0~9.1~2026.01'
if [ "$(id -gn)" != llm ]; then
  exec sg llm -c "$(printf '%q ' "$0" "$@")"
fi
umask 0002
LOCKS=/opt/rocq/locks
mkdir -p "$LOCKS"
daytime() {
  local dow hour
  dow=$(TZ=Europe/Warsaw date +%u)
  hour=$(TZ=Europe/Warsaw date +%H)
  [ "$dow" -le 5 ] && [ "$((10#$hour))" -ge 7 ] && [ "$((10#$hour))" -lt 17 ]
}
run() { exec nice -n 10 opam exec --switch="$SWITCH" -- "$@"; }
if ! daytime; then run "$@"; fi
while true; do
  for slot in 1 2; do
    exec 9>"$LOCKS/subproject-compiler-$slot.lock"
    if flock -n 9; then run "$@"; fi
    exec 9>&-
  done
  sleep 5
done
