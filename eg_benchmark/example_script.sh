#!/bin/bash
echo "Remember to cargo build --release"
for i in {5000000..10000000..8}
do
 echo "Transformations:" $(($i - 499999 )) " - " $(($i + 8 - 499999)) " / 1.000.000"
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 10)) --type EQU --seed $(($i + 1)) --lean --gen $(($i % 40 + 12)) mtf_EQU_$(($i + 1)) &
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 11)) --type EXP --seed $(($i + 2)) --lean --gen $(($i % 40 + 13)) mtf_EXP_$(($i + 2)) &
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 12)) --type CON --seed $(($i + 3)) --lean --gen $(($i % 40 + 14)) mtf_CON_$(($i + 3)) &
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 13)) --type EQU --seed $(($i + 4)) --lean --gen $(($i % 40 + 15)) mtf_EQU_$(($i + 4)) &
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 14)) --type EXP --seed $(($i + 5)) --lean --gen $(($i % 40 + 16)) mtf_EXP_$(($i + 5)) &
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 15)) --type CON --seed $(($i + 6)) --lean --gen $(($i % 40 + 17)) mtf_CON_$(($i + 6)) &
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 17)) --type EXP --seed $(($i + 8)) --lean --gen $(($i % 40 + 19)) mtf_EXP_$(($i + 8)) &
 ./../target/release/nemo-metamorphic-testing --num $(($i % 100 + 18)) --type CON --seed $(($i + 9)) --lean --gen $(($i % 40 + 20)) mtf_CON_$(($i + 9)) &
 wait
done
# -r would mean random seed file, absence means no seed file