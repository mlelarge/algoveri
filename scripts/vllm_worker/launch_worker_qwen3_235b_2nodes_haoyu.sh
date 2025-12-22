#!/bin/bash
#SBATCH --job-name=vllm_worker
#SBATCH --nodes=2
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=40
#SBATCH --mem=400G
#SBATCH --gres=gpu:4
#SBATCH --time=23:59:00
#SBATCH --partition=pli-c
#SBATCH --account=pli
#SBATCH --mail-type=FAIL
#SBATCH --mail-user=haoyu@princeton.edu
#SBATCH --output=slurm_output/%x-%j.out



# Port for this vLLM worker. Ensure it's unique if running multiple workers on the same node.
# This command asks the OS for an available port and saves it to the variable.
WORKER_PORT=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
echo "Found and assigned free port: ${WORKER_PORT}"
# ---

# The Hugging Face model to be served by this worker.
MODEL_PATH="/scratch/gpfs/ARORA/haoyu/Qwen3-235B-A22B"
TENSOR_PARALLEL_SIZE=4 # Should match --gpus-per-task

# --- Environment Setup ---

# Activate your Python/Conda environment where vLLM is installed.
# Replace with your specific environment activation command.
source /scratch/gpfs/ARORA/haoyu/miniconda3/etc/profile.d/conda.sh
conda activate algoveri

echo "Environment activated."

# 2. Network Setup for Ray
# Get the first node's hostname as the head node
nodes=$(scontrol show hostnames "$SLURM_JOB_NODELIST")
nodes_array=($nodes)
head_node=${nodes_array[0]}
head_node_ip=$(srun --nodes=1 --ntasks=1 -w "$head_node" hostname --ip-address)

# Port for Ray head
RAY_PORT=6379

echo "Head node: $head_node ($head_node_ip)"
echo "Starting Ray Cluster..."

# 3. Start Ray Head Node (on the first node)
# We use & to run it in background so we can proceed to start workers
srun --nodes=1 --ntasks=1 -w "$head_node" \
    ray start --head \
    --port=$RAY_PORT \
    --num-cpus=$SLURM_CPUS_PER_TASK \
    --num-gpus=4 \
    --block &
sleep 20 # Wait for head to initialize

# 4. Start Ray Worker Nodes (on all other nodes)
# Loop through the rest of the nodes and connect them to the head
worker_num=$((SLURM_JOB_NUM_NODES - 1))

for ((i=1; i<=worker_num; i++)); do
    node_i=${nodes_array[$i]}
    echo "Starting Worker on $node_i connecting to $head_node_ip:$RAY_PORT"
    srun --nodes=1 --ntasks=1 -w "$node_i" \
        ray start --address "$head_node_ip:$RAY_PORT" \
        --num-cpus=$SLURM_CPUS_PER_TASK \
        --num-gpus=4 \
        --block &
done

sleep 20

module load cudatoolkit/13.0  # Or whichever version you are using

# 2. Set CUDA_HOME explicitly based on the loaded compiler
export CUDA_HOME=$(dirname $(dirname $(which nvcc)))

# 3. Verify it is set (should look like /usr/local/cuda-12.4 or similar)
echo $CUDA_HOME

# --- Launch vLLM Server ---
echo "Starting vLLM worker for model ${MODEL_NAME} on port ${WORKER_PORT}..."

# Get the actual IP of the current node
export VLLM_HOST_IP=$(hostname -I | awk '{print $1}')

# Start the vLLM OpenAI-compatible API server in the background
#python -m vllm.entrypoints.openai.api_server \
vllm serve "${MODEL_PATH}" \
    --port ${WORKER_PORT} \
    --tensor-parallel-size ${TENSOR_PARALLEL_SIZE} \
    --pipeline-parallel-size 2 \
    --reasoning-parser deepseek_r1 \
    --rope-scaling '{"rope_type":"yarn","factor":4.0,"original_max_position_embeddings":32768}' \
    --max-model-len 131072 \
    --trust-remote-code &


echo "vLLM use port: ${WORKER_PORT}"

# Capture the Process ID (PID) of the backgrounded vLLM server
VLLM_PID=$!
echo "vLLM server started with PID: ${VLLM_PID}"

wait ${VLLM_PID}