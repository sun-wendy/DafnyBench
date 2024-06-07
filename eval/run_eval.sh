#!/bin/bash
#SBATCH --job-name=eval
#SBATCH -o log/%j-eval.log
#SBATCH -c 1

export PATH=$DAFNYBENCH_ROOT:$PATH
export TEST_SET_DIR=$DAFNYBENCH_ROOT/DafnyBench/dataset/hints_removed

sleep 0.1

source $DAFNYBENCH_ROOT/stats/bin/activate

mkdir -p ../results/results_summary
if [ ! -f "../results/results_summary/${model_to_eval}_results.csv" ]; then
    echo "test_ID,test_file,success_on_attempt_#" > "../results/results_summary/${model_to_eval}_results.csv"
fi

mkdir -p ../results/reconstructed_files
outputs_file="../results/reconstructed_files/${model_to_eval}_outputs.json"
if [ ! -f "$outputs_file" ]; then
    echo "{}" > "$outputs_file"
fi

# Evaluation
for DAFNY_FILE in "$TEST_SET_DIR"/*.dfy
do
    echo "Reconstructing $DAFNY_FILE"
    if [ -f "$DAFNY_FILE" ]; then
        FILENAME=$(basename "$DAFNY_FILE")
        python fill_hints.py \
            --model "$model_to_eval" \
            --test_file "$FILENAME" \
            --feedback_turn 10 \
            --dafny_path "$DAFNY_PATH"  # Example Dafny path: "/opt/homebrew/bin/Dafny"
            > log/%j-eval.log 2>&1
    fi
done

# Calculate success rate
results_file="../results/results_summary/${model_to_eval}_results.csv"
lines=($(<"$results_file"))
total_num_files=$((${#lines[@]} - 1))
num_failed=0

for ((i=1; i<=total_num_files; i++)); do
    if [[ ${lines[i]} == *"failed" ]]; then
        ((num_failed++))
    fi
done

success_rate=$(echo "scale=2; ($total_num_files - $num_failed) / $total_num_files" | bc)
echo "Success rate for $model_to_eval = $success_rate"
