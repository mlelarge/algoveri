#!/bin/bash
#SBATCH --job-name=vllm_worker
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=40
#SBATCH --mem=400G
#SBATCH --gres=gpu:8
#SBATCH --time=02:00:00
#SBATCH --partition=pli-c
#SBATCH --output=slurm_output/%x-%j.out
#SBATCH --mail-type=ALL
#SBATCH --mail-user=haoyu@princeton.edu

# 1. Define the container path
CONTAINER="/scratch/gpfs/ARORA/haoyu/apptainer_imgs/vllm.sif"

WORKER_PORT=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
HEAD_NODE_IP=$(hostname -I | awk '{print $1}')
echo "Head node IP: ${HEAD_NODE_IP}"
echo "Found and assigned free port: ${WORKER_PORT}"

MODEL_PATH="/scratch/gpfs/ARORA/haoyu/Qwen3-235B-A22B-Instruct-2507"

# 7. Run vLLM Server
# The server runs on the head node, so we use the head node IP here
echo "Starting vLLM Server..."
apptainer exec --nv --bind /scratch:/scratch \
    --env VLLM_HOST_IP=$head_node_ip \
    $CONTAINER \
    vllm serve "${MODEL_PATH}" \
    --port ${WORKER_PORT} \
    --tensor-parallel-size 8 \
    --max-model-len 262144 \
    --trust-remote-code \
    --host 0.0.0.0 &

echo "vLLM use port: ${WORKER_PORT}"

VLLM_PID=$!
wait ${VLLM_PID}