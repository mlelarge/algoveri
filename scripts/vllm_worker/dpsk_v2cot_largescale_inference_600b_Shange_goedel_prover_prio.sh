#!/bin/bash
# TOTAL_NODES=4
# GPUS_PER_NODE=4
TOTAL_NODES=2
GPUS_PER_NODE=8
# TRUNK=40
# PASSN=2
TRUNK=4
PASSN=4
# COMPILE=1 # whether sumbmit compilation jobs
COMPILE=0 # no compilation
INFERNCE_HANDLER="dpskcot"
MAX_LENGTH=16348
sfx="v1"
timestr=$(date +%y%m%d%H%M%S%3N)

# your dir
# PROJECT_DIR="/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5"
PROJECT_DIR="/scratch/gpfs/st3812/aiformath/Deepseek"

cd ${PROJECT_DIR}

JOBNAME="unified_inference"

mkdir -p sbatch_jobs logs results_unified

create_train_script() {
    local split=$1
    local model_path=$2
    local input_file=$3
    local model_name=$(basename "$model_path")
    local input_filename=$(basename "$input_file")
    local input_name="${input_filename%.*}"
    result_dir="results_unified/${input_name}"
    local input_path="${input_file}"
    local output_dir="${result_dir}/${model_name}_${sfx}/${split}"
    local log_name="${timestr}_${script_name}_${input_name}_${split}_${model_name}"
    local script_name="${log_name}"
    cat << EOF > "sbatch_jobs/${script_name}.sh"
#!/bin/bash
#SBATCH --job-name=unified_inference # create a short name for your job
#SBATCH --nodes=${TOTAL_NODES}
#SBATCH --ntasks=${TOTAL_NODES}
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=$((GPUS_PER_NODE * 12))
#SBATCH --gres=gpu:${GPUS_PER_NODE}
#SBATCH --mem=$((GPUS_PER_NODE * 100))g
#SBATCH --partition=pli-p
#SBATCH --account=goedel_prover_prio
#SBATCH --qos=pli-high
#SBATCH --exclude=della-k14g2,della-k14g3,della-k18g1,della-k12g3,della-k14g1,della-j12g3,della-j13g3,della-j13g1,della-j16g1
#SBATCH --time=23:59:00
#SBATCH --output=logs/${log_name}.log
#SBATCH --error=logs/${log_name}.err
#SBATCH --mail-type=ALL
#SBATCH --mail-user="st3812@princeton.edu"

source ~/.bashrc
conda activate verl

echo python unified_inference/unified_inference.py --input_path ${input_path} --model_path ${model_path} --output_dir ${output_dir} --split ${split} --n ${PASSN} --gpu ${GPUS_PER_NODE} --trunck ${TRUNK} --inference_handler ${INFERNCE_HANDLER}  --max_model_len ${MAX_LENGTH}

srun --nodes=${TOTAL_NODES}  --mem=200G --ntasks-per-node=1 --gres=gpu:${GPUS_PER_NODE} --cpu-bind=none bash -c '
export RAY_CGRAPH_get_timeout=300
export VLLM_HOST_IP=\$(hostname -i)
if [ "\$SLURM_PROCID" -eq 0 ]; then
  ray start --head --port=6379 --node-ip-address=\$VLLM_HOST_IP
  sleep 10
  cd ${PROJECT_DIR}
  python unified_inference/unified_inference.py --input_path ${input_path} --model_path ${model_path} --output_dir ${output_dir} --split ${split} --n ${PASSN} --gpu ${GPUS_PER_NODE} --trunck ${TRUNK} --inference_handler ${INFERNCE_HANDLER} --max_model_len ${MAX_LENGTH} --node ${TOTAL_NODES}
else
  sleep 5
  ray start --address=\$(scontrol show hostnames \$SLURM_JOB_NODELIST | head -n1):6379 --node-ip-address=\$VLLM_HOST_IP
  sleep infinity
fi
'


if [ ${COMPILE} -gt 0 ]; then
    sbatch unified_inference/unified_compile_summarize.sh -i ${output_dir}/to_inference_codes.json -o ${output_dir}
fi

 
echo "Job finished at \$(date)"
EOF

    chmod +x "sbatch_jobs/${script_name}.sh"
    echo "Submitting job sbatch_jobs/${script_name}.sh for ${input_name} on SPLIT=${split}, MODEL=${model_path}, COMPILE=${COMPILE}."
    sbatch "sbatch_jobs/${script_name}.sh"
}

files=(
    # "datasets/minif2f_reformat.jsonl"
    # "datasets/lean_workbook/lwbv1tov5_statements_lwb_style_translated_full_unsolved_smallersplit.jsonl"
    # "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/lean_workbook/lwbv1tov5_statements_lwb_style_translated_full_unsolved_smallersplit_unsolved.jsonl"
    # "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/lean_workbook/lwbv1tov5_statements_lwb_style_translated_full_unsolved_smallersplit_unsolved_filter.jsonl"
    "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/lean_workbook/lwbv1tov5_statements_lwb_style_translated_full_unsolved_smallersplit_unsolved_filter_negated.jsonl"
)

# "dpskcot", "dpsknoncot", "kiminacot"
model_tuples=(
    "/scratch/gpfs/CHIJ/DeepSeek-Prover-V2-671B"
)

# "/scratch/gpfs/yl7690/models/Kimina-Prover-Preview-Distill-7B,kiminacot" 
# ",dpskcot"

# Loop through each tuple
# for split in $(seq 100 120); do
# for split in $(seq 103 104); do
# for split in $(seq 105 108); do
# for split in $(seq 109 110); do
# for split in $(seq 111 114); do
# for split in $(seq 112 114); do
# for split in $(seq 113 114); do
# for split in $(seq 115 116); do
# for split in $(seq 117 120); do
# for split in $(seq 119 120); do
# for split in $(seq 121 122); do
# for split in $(seq 123 126); do
# for split in $(seq 126 127); do
# for split in $(seq 128 129); do
# for split in $(seq 130 131); do
# for split in $(seq 132 133); do
# for split in $(seq 133 133); do
# for split in $(seq 134 137); do
# for split in $(seq 138 140); do
# for split in $(seq 141 144); do
# for split in $(seq 151 154); do
for split in $(seq 155 162); do
    for file in "${files[@]}"; do
        for model_path in "${model_tuples[@]}"; do
            echo "$model_path, ${file}, ${split}"
            create_train_script ${split} ${model_path} ${file}
        done
    done
done

