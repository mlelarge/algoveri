#!/bin/bash
#SBATCH --job-name=algoveri
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=40
#SBATCH --mem=400G
#SBATCH --gres=gpu:8
#SBATCH --time=23:59:00
#SBATCH --partition=pli-c
#SBATCH --output=slurm_output/%x-%j.out
#SBATCH --mail-type=ALL
#SBATCH --mail-user=haoyu@princeton.edu
###### $ #SBATCH --qos=pli-cp

source /scratch/gpfs/ARORA/haoyu/miniconda3/etc/profile.d/conda.sh
conda activate algoveri

# --- CONFIGURATION ---
CONTAINER="/scratch/gpfs/ARORA/haoyu/apptainer_imgs/vllm-nightly.sif"
MODEL_PATH="/scratch/gpfs/ARORA/haoyu/Devstral-2-123B-Instruct-2512"
LANGUAGE="dafny"

# Setup Network Variables
HEAD_NODE_IP=$(hostname -I | awk '{print $1}')
WORKER_PORT=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
SERVER_URL="http://localhost:${WORKER_PORT}/v1"
SERVER_PID=""

echo "Configuration: Node IP ${HEAD_NODE_IP}, Port ${WORKER_PORT}"

# --- FUNCTION 1: Start/Restart vLLM ---
start_vllm() {
    echo ">>> [System] Starting vLLM Server..."
    
    # 1. Start the server in the background
    apptainer exec --nv --bind /scratch:/scratch \
        --env VLLM_HOST_IP=${HEAD_NODE_IP} \
        $CONTAINER \
        vllm serve "${MODEL_PATH}" \
        --port ${WORKER_PORT} \
        --tensor-parallel-size 8 \
        --max-model-len 262144 \
        --trust-remote-code \
        --host 0.0.0.0 &> "slurm_output/vllm_server_${SLURM_JOB_ID}.log" &
    
    # 2. Capture the PID
    SERVER_PID=$!
    echo ">>> [System] Server Process ID: $SERVER_PID"

    # 3. Wait loop (Health Check)
    echo ">>> [System] Waiting for health check..."
    local retries=0
    # Wait up to 30 minutes (90 * 20s) for the server to load
    while ! curl -s -o /dev/null -w "%{http_code}" http://localhost:${WORKER_PORT}/v1/models | grep -q "200"; do
        sleep 20
        ((retries++))
        
        # Check if process died while loading
        if ! kill -0 $SERVER_PID 2>/dev/null; then
            echo "!!! [Error] vLLM process died during startup. Check vllm_server.log"
            exit 1
        fi

        if [ $retries -ge 90 ]; then
            echo "!!! [Error] Timed out waiting for server to start."
            exit 1
        fi
        echo "   ... loading model ($retries/90)"
    done
    echo ">>> [System] vLLM is READY!"
    sleep 60
}

# --- FUNCTION 2: Run Task with Retry Logic ---
run_task_robust() {
    local INPUT_PATH=$1
    local TASK_NAME=$(basename "$INPUT_PATH")
    local MAX_RETRIES=2
    local attempt=1

    echo "------------------------------------------------"
    echo "Starting Task: $TASK_NAME"
    echo "------------------------------------------------"

    while [ $attempt -le $MAX_RETRIES ]; do
        # Execute the python command
        # We assume src.run_task uses the --url arg we pass below
        sleep 60
        echo "$INPUT_PATH" | python -m src.run_task \
            --num_passes 10 \
            --model "${MODEL_PATH}" \
            --language "${LANGUAGE}" \
            --url "${SERVER_URL}"
        
        # Capture exit code of python script
        EXIT_CODE=$?

        if [ $EXIT_CODE -eq 0 ]; then
            echo ">>> [Success] Task $TASK_NAME completed."
            return 0
        else
            echo "!!! [Warning] Task $TASK_NAME failed (Attempt $attempt/$MAX_RETRIES)."
            
            if [ $attempt -eq $MAX_RETRIES ]; then
                echo "!!! [Error] Max retries reached for $TASK_NAME. Moving to next task."
                return 1
            fi

            # --- RECOVERY LOGIC ---
            echo ">>> [Recovery] Diagnosing Server Status..."
            sleep 10 # Wait a moment for dust to settle

            # Check if server endpoint responds
            if curl -s -o /dev/null -w "%{http_code}" --max-time 5 http://localhost:${WORKER_PORT}/v1/models | grep -q "200"; then
                echo ">>> [Recovery] Server appears HEALTHY. Retrying task immediately..."
            else
                echo "!!! [Recovery] Server appears DEAD or STUCK. Restarting..."
                
                # Kill old server if it exists
                kill $SERVER_PID 2>/dev/null
                wait $SERVER_PID 2>/dev/null
                
                # Start fresh
                start_vllm
            fi
            
            ((attempt++))
        fi
    done
}

# --- MAIN EXECUTION FLOW ---

# 1. Initial Start
start_vllm

# 2. Run Benchmarks using the robust function


#############################################
# Data structure
#############################################
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/maxheap_push"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/maxheap_popmax"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bst_search"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bst_delete"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bst_insert"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bst_zig"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bst_zigzig"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bst_zigzag"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/stack_push"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/stack_pop"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/queue_enqueue"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/queue_dequeue"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/ringbuffer_enqueue"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/ringbuffer_dequeue"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/unionfind_find"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/unionfind_linkroots"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/splaytree_splay"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/trie_search"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/trie_insert"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/trie_delete"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/ternarysearchtree_search"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/ternarysearchtree_insert"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/ternarysearchtree_delete"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/segmenttree_query"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/segmenttree_modify"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/segmenttree_build"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/llrbt_delete"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/llrbt_insert"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/llrbt_rotateleft"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/llrbt_rotateright"
run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/llrbt_flipcolor"


#############################################
# Sorting, searching, and ordered statistics
#############################################

# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/binary_search"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/linear_search"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bubble_sort"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/insertion_sort"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/merge_sort"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/quick_sort"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/k_smallest"

#############################################
# basic algorithms, DP, xxx
#############################################

# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/longest_common_subsequence"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/coin_change"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/jump_game"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/knapsack_01"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/knapsack_unbounded"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/longest_increasing_subsequence"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/maximum_subarray_sum"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/rod_cutting"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/lca"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/house_robber"

#############################################
# Graph algorithms
#############################################

# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/dfs"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bfs"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/cycle_detection"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bipartite_check"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/topological_sort"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/dijkstra"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bellman_ford"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/prim"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/kruskal"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/max_matching"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/edmond_karp"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/push_relabel"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/scc_tarjan"

#############################################
# Math
#############################################

# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/integer_exponential"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/fast_exponential"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/trial_division_naive"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/trial_division_optimized"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/sieve_method"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/polymul_naive"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/polymul_karatsuba"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/discrete_logarithm"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/linearsys_gf2"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/gcd"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/matrix_multiplication"

#############################################
# String
#############################################

# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/bracket_matching"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/longest_palindrome_substring"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/string_search_naive"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/kmp"
# run_task_robust "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data/ac_automata"


# 3. Final Cleanup
echo ">>>All tasks finished. Shutting down server..."
kill $SERVER_PID
