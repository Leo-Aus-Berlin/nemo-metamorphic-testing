
#!/bin/bash
for i in {1..10000}
do
 echo "Transformation EXP:" $i " / 10000"
 ./../target/debug/nemo-metamorphic-testing --num 32 --type EXP --seed $i mtf_EXP_$i
done
for i in {10000..20000}
do
 echo "Transformation EQU:" $i " / 20000"
 ./../target/debug/nemo-metamorphic-testing --num 32 --type EQU --seed $i mtf_EQU_$i
done
for i in {20000..30000}
do
 echo "Transformation EQU:" $i " / 30000"
 ./../target/debug/nemo-metamorphic-testing --num 32 --type CON --seed $i mtf_CON_$i
done