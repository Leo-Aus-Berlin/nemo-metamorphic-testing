#!/bin/bash
echo "Remember to cargo build --release"
for i in {60002..70000}
do
 echo "Transformation EXP:" $(($i -60000)) " / 10000"
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 10)) --type EXP --seed $i --lean --gen $(($i % 40 + 10)) mtf_EXP_$i
done
for i in {70000..80000}
do
 echo "Transformation EQU:" $(($i -60000)) " / 20000"
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 10)) --type EQU --seed $i --lean --gen $(($i % 40 + 10)) mtf_EQU_$i
done
for i in {80000..90000}
do
 echo "Transformation CON:" $(($i -60000)) " / 30000"
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 10)) --type CON --seed $i --lean --gen $(($i % 40 + 10)) mtf_CON_$i
done