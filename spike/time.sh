#!/usr/bin/env bash
# Check one spike module afresh and report its time.  Usage, from the
# repository root: bash spike/time.sh Spike/Module [extra agda flags]
# The module's own interface is removed first, so that Agda checks it
# again; the interfaces of its imports are kept.
set -u
m="$1"; shift
find _build -path "*/spike/${m}.agdai" -delete 2>/dev/null
start=$(date +%s.%N)
.agda/bin/agda -i spike -i src "spike/${m}.agda" "$@" +RTS -M6G -A128M -RTS
status=$?
end=$(date +%s.%N)
printf 'module %s: exit %s, %.2f s wall\n' "$m" "$status" "$(echo "$end - $start" | bc)"
exit $status
