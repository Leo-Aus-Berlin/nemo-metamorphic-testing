#!/bin/bash
for i in {30000..40000}
do
 echo "Transformation EXP:" $(($i -30000)) " / 10000"
 ./../target/debug/nemo-metamorphic-testing --num $(($i % 100 + 10)) --type EXP --seed $i --lean --gen $(($i % 40 + 10)) mtf_EXP_$i
done
for i in {40000..50000}
do
 echo "Transformation EQU:" $(($i -30000)) " / 20000"
 ./../target/debug/nemo-metamorphic-testing --num $(($i % 100 + 10)) --type EQU --seed $i --lean --gen $(($i % 40 + 10)) mtf_EQU_$i
done
for i in {50000..60000}
do
 echo "Transformation CON:" $(($i -30000)) " / 30000"
 ./../target/debug/nemo-metamorphic-testing --num $(($i % 100 + 10)) --type CON --seed $i --lean --gen $(($i % 40 + 10)) mtf_CON_$i
done