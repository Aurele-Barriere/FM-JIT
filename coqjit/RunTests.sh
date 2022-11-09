#!/bin/bash

echo "Running the JIT, with native code execution"
read -p "Press any key to resume ..."
native_start=$(date +%s.3%N)
./jit progs_IR/prime.ir
native_end=$(date +%s.3%N)

echo "Now Running the JIT on the same program, but interpretation only"
read -p "Press any key to resume ..."
interp_start=$(date +%s.3%N)
./jit progs_IR/prime.ir -i
interp_end=$(date +%s.3%N)


native=$(echo "scale=3; $native_end - $native_start" | bc)
interp=$(echo "scale=3; $interp_end - $interp_start" | bc)
ratio=$(echo "$interp / $native" | bc -l)

echo "JIT time:    $native seconds"
echo "Interp time: $interp seconds"
echo "JIT was $ratio times faster"

