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
#SBATCH --qos=pli-cp


# 1. Define the container path
CONTAINER="/scratch/gpfs/ARORA/haoyu/apptainer_imgs/vllm.sif"

# 2. Get the Head Node IP
head_node=$(hostname)
head_node_ip=$(hostname --ip-address)
export head_node_ip
port=6379
ip_head=$head_node_ip:$port
export ip_head

echo "Head node IP: $head_node_ip"

# 3. Start Ray Head Node (on the first node)
# We use 'srun' to launch tasks. 
# --pack-group=0 ensures we target the first node for the head.
echo "Starting Ray Head..."
srun --nodes=1 --ntasks=1 --wckey=head \
    apptainer exec --nv --bind /scratch:/scratch $CONTAINER \
    ray start --head --port=$port --num-gpus=4 --block &

# 4. Wait for Head to start
sleep 10

# 5. Start Ray Worker Nodes (on all other nodes)
# We exclude the head node using --exclude or just rely on srun behavior 
# typically we launch workers on ALL nodes minus 1, or just launch on all 
# and let Ray figure it out (but better to separate).
# simpler approach for 2 nodes:
echo "Starting Ray Workers..."
srun --nodes=1 --ntasks=1 --exclude=$head_node \
    apptainer exec --nv --bind /scratch:/scratch $CONTAINER \
    ray start --address=$ip_head --num-gpus=4 --block &

# 6. Wait for workers to connect
sleep 20

# Start the vLLM OpenAI-compatible API server in the background
#python -m vllm.entrypoints.openai.api_server \
# 7. Run vLLM Server (Submitted from the Head Node)
# Note: We must run this inside the container too!

WORKER_PORT=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
echo "Found and assigned free port: ${WORKER_PORT}"


echo "Starting vLLM Server..."
apptainer exec --nv --bind /scratch:/scratch $CONTAINER \
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