#!/bin/bash
#SBATCH --job-name=vllm_worker
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=24
#SBATCH --mem=256G
#SBATCH --gres=gpu:2
#SBATCH --time=23:59:00
#SBATCH --partition=pli-c
#SBATCH --account=pli
#SBATCH --mail-type=FAIL
#SBATCH --mail-user=st3812@princeton.edu
#SBATCH --output=slurm_output/%x-%j.out
#SBATCH --exclude=della-j14g3


# --- User Configuration ---
# IMPORTANT: Set this to the address of your running gateway server.
export GATEWAY_URL="http://della9.princeton.edu:8888"

# Port for this vLLM worker. Ensure it's unique if running multiple workers on the same node.
# This command asks the OS for an available port and saves it to the variable.
WORKER_PORT=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
echo "Found and assigned free port: ${WORKER_PORT}"
# ---

# The Hugging Face model to be served by this worker.
MODEL_PATH="/scratch/gpfs/ARORA/haoyu/Qwen3-32B"
TENSOR_PARALLEL_SIZE=2 # Should match --gpus-per-task

# --- Environment Setup ---

# Activate your Python/Conda environment where vLLM is installed.
# Replace with your specific environment activation command.
source /scratch/gpfs/ARORA/haoyu/miniconda3/etc/profile.d/conda.sh
conda activate goedelsdk

echo "Environment activated."

# --- Launch vLLM Server ---
echo "Starting vLLM worker for model ${MODEL_NAME} on port ${WORKER_PORT}..."

# Start the vLLM OpenAI-compatible API server in the background
python -m vllm.entrypoints.openai.api_server \
    --model "${MODEL_PATH}" \
    --host "0.0.0.0" \
    --port ${WORKER_PORT} \
    --tensor-parallel-size ${TENSOR_PARALLEL_SIZE} \
    --trust-remote-code &


echo "vLLM use port: ${WORKER_PORT}"

# Capture the Process ID (PID) of the backgrounded vLLM server
VLLM_PID=$!
echo "vLLM server started with PID: ${VLLM_PID}"

wait ${VLLM_PID}