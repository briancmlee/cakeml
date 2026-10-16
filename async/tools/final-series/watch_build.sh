#!/bin/zsh
# usage: watch_build.sh LOG DIR1 DIR2 ...  (run inside an async/ tree)
# Holmake -j1 in each dir under holslot (timeout 3600); kill any HOL process whose footprint >= 4 GB
LOG=$1; shift; WT=$(pwd)   # only processes of this tree are watched
: > $LOG
for d in "$@"; do
  ( cd $d && ~/.cache/orchestrator/holslot timeout 3600 arch -arm64 $HOME/HOL/bin/Holmake -j1 >> $LOG 2>&1; echo "exit $? $d" >> $LOG ) &
  BP=$!
  while kill -0 $BP 2>/dev/null; do
    for p in $(pgrep -f "$WT"); do
      m=$(top -l 1 -pid $p -stats mem 2>/dev/null | tail -1 | tr -d ' ')
      case $m in *G) v=${m%G}; v=${v%%+*}; if (( ${v%.*} >= 4 )); then echo "KILL $p mem=$m" >> $LOG; kill -9 $p; fi;; esac
    done
    sleep 10
  done
  grep -q "^exit 0 $d" $LOG || break
done
echo "DONE" >> $LOG
