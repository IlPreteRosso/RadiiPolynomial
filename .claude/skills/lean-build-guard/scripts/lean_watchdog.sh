#!/bin/zsh
# lean_watchdog.sh [--once] — kill lean/lake processes compiling dependency sources (.lake/packages/*), which must never happen.
once=0; [ "${1:-}" = "--once" ] && once=1
while true; do
  pids=$(ps -Ao pid,command | command grep -E '[/]bin/lean .*\.lake/packages/[^ ]+/[^ ]+\.lean' | awk '{print $1}')
  if [ -n "$pids" ]; then
    echo "WATCHDOG $(date -u +%FT%TZ): dependency compile detected — killing lean pids: $pids"
    ps -Ao pid,command | command grep -E '[/]bin/lean .*\.lake/packages/' | cut -c1-160 | head -3
    kill $pids 2>/dev/null; pkill -f '[/]bin/lake build' 2>/dev/null; sleep 1
    [ $once -eq 1 ] && exit 1
  else
    [ $once -eq 1 ] && { echo "watchdog: no dependency compile running"; exit 0; }
  fi
  sleep 2
done
