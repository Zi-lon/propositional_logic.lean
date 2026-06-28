LOG=resultaten/timings.log
LOG_LOGIC=resultaten/logic.log
LOG_GRIND=resultaten/grind.log

> "$LOG"
> "$LOG_LOGIC"
> "$LOG_GRIND"

start=$SECONDS
for n in {1..10}; do
  for i in {1..5}; do

    echo "Run $n $i - Logic" | tee -a "$LOG"
    /usr/bin/time -p lake exe bench_logic > /dev/null 2>> "$LOG_LOGIC"
    echo "--------------------------------------------------" >> "$LOG_LOGIC"

    echo "Run $n $i - Grind" | tee -a "$LOG"
    /usr/bin/time -p lake exe bench_grind > /dev/null 2>> "$LOG_GRIND"
    echo "--------------------------------------------------" >> "$LOG_GRIND"
  done
done
echo "duration=$(( SECONDS - start )) seconds"


echo "=== RESULTATEN ==="

echo ""
echo "--- LOGIC ---"
awk '
/real/ {r+=$2; rc++}
/user/ {u+=$2; uc++}
/sys/  {s+=$2; sc++}
END {
  printf "Runs: %d\nGemiddelde real: %.3f s\nGemiddelde user: %.3f s\nGemiddelde sys:  %.3f s\n",
         rc, r/rc, u/uc, s/sc
}' "$LOG_LOGIC"

echo ""
echo "--- GRIND ---"
awk '
/real/ {r+=$2; rc++}
/user/ {u+=$2; uc++}
/sys/  {s+=$2; sc++}
END {
  printf "Runs: %d\nGemiddelde real: %.3f s\nGemiddelde user: %.3f s\nGemiddelde sys:  %.3f s\n",
         rc, r/rc, u/uc, s/sc
}' "$LOG_GRIND"