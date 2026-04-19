#!/usr/bin/env bash
set -euo pipefail

ivy_file="ivybench/total/ivy/distributed_lock_v2.ivy"

for epoch in 3 4 5 6 7; do
    log_file="distributed_lock_v2_epoch_${epoch}.log"
    echo "Running epoch=${epoch} -> ${log_file}"

    if ! python3 QSM-Cutoff.py "${ivy_file}" \
        -s "node=2,epoch=${epoch}" \
        -v 4 \
        -l "${log_file}" \
        -y \
        -a \
        -k; then
        echo "Epoch ${epoch} failed, continuing to next epoch"
    fi
done
