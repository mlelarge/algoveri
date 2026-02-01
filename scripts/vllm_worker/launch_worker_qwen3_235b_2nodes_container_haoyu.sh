#!/bin/bash
#SBATCH --job-name=vllm_worker
#SBATCH --nodes=2
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=40
#SBATCH --mem=400G
#SBATCH --gres=gpu:4
#SBATCH --time=02:00:00
#SBATCH --partition=pli-c
#SBATCH --account=pli
#SBATCH --output=slurm_output/%x-%j.out

# 1. Define the container path
CONTAINER="/scratch/gpfs/ARORA/haoyu/apptainer_imgs/vllm.sif"

# 2. Get the Head Node IP
# This is calculated on the node running the script (the Head Node)
head_node=$(hostname)
head_node_ip=$(hostname --ip-address)
port=6379
ip_head=$head_node_ip:$port
export ip_head

echo "Head node IP: $head_node_ip"

# --- REMOVED GLOBAL EXPORT OF VLLM_HOST_IP ---
# We will pass it specifically to each command instead.

# 3. Start Ray Head Node (on the first node)
echo "Starting Ray Head..."
# We explicitly pass env VLLM_HOST_IP matching the head node
srun --nodes=1 --ntasks=1 --wckey=head \
    apptainer exec --nv --bind /scratch:/scratch \
    --env VLLM_HOST_IP=$head_node_ip \
    $CONTAINER \
    ray start --head --node-ip-address=$head_node_ip --port=$port --num-gpus=4 --block &

# 4. Wait for Head to start
sleep 10

# 5. Start Ray Worker Nodes (on all other nodes)
echo "Starting Ray Workers..."
# We use bash -c to run a script ON THE WORKER NODE.
# This allows us to calculate 'hostname --ip-address' separately for each worker.
srun --nodes=1 --ntasks=1 --exclude=$head_node \
    /bin/bash -c "
        # Calculate the LOCAL IP of this specific worker node
        MY_IP=\$(hostname --ip-address)
        echo \"Worker Node: \$(hostname) has IP: \${MY_IP}\"
        
        # Launch Ray, telling vLLM to use THIS worker's IP
        apptainer exec --nv --bind /scratch:/scratch \
        --env VLLM_HOST_IP=\${MY_IP} \
        $CONTAINER \
        ray start --address=$ip_head --node-ip-address=\${MY_IP} --num-gpus=4 --block
    " &

# 6. Wait for workers to connect
sleep 20

WORKER_PORT=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
echo "Found and assigned free port: ${WORKER_PORT}"

MODEL_PATH="/scratch/gpfs/ARORA/haoyu/Qwen3-235B-A22B"

# 7. Run vLLM Server
# The server runs on the head node, so we use the head node IP here
echo "Starting vLLM Server..."
apptainer exec --nv --bind /scratch:/scratch \
    --env VLLM_HOST_IP=$head_node_ip \
    --env NCCL_SOCKET_IFNAME=eth0 \
    $CONTAINER \
    vllm serve "${MODEL_PATH}" \
    --port ${WORKER_PORT} \
    --tensor-parallel-size 4 \
    --pipeline-parallel-size 2 \
    --reasoning-parser deepseek_r1 \
    --rope-scaling '{"rope_type":"yarn","factor":4.0,"original_max_position_embeddings":32768}' \
    --max-model-len 131072 \
    --trust-remote-code \
    --host 0.0.0.0 &

echo "vLLM use port: ${WORKER_PORT}"

VLLM_PID=$!
wait ${VLLM_PID}