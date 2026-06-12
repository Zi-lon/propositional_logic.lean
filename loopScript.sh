#!/bin/bash
for i in {1..2}; do
/usr/bin/time -p lake build > /dev/null 2>> timings.log
echo "--------------------------------------------------" >> timings.log
done

echo "=== Berekening voltooid ==="
awk '/real/ {r+=$2; rc++} /user/ {u+=$2; uc++} /sys/ {s+=$2; sc++} END {
  if (rc > 0) printf "Aantal succesvolle runs: %d\nGemiddelde real: %.2f s\nGemiddelde user: %.2f s\nGemiddelde sys:  %.2f s\n", rc, r/rc, u/uc, s/sc
}' timings.log