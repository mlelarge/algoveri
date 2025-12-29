# 1. Define the path (same as your job)
export CACHE_DIR="/scratch/gpfs/ARORA/haoyu/algoveri/tiktoken_cache"
mkdir -p "$CACHE_DIR"

# 2. Run the download using the container itself
# We bind /scratch so the container can write the file directly to your storage

CONTAINER="/scratch/gpfs/ARORA/haoyu/apptainer_imgs/vllm-nightly.sif"

apptainer exec \
    --bind /scratch:/scratch \
    --env TIKTOKEN_RS_CACHE_DIR="$CACHE_DIR" \
    $CONTAINER \
    python3 -c "from openai_harmony import load_harmony_encoding, HarmonyEncodingName; print('Downloading...'); load_harmony_encoding(HarmonyEncodingName.HARMONY_GPT_OSS); print('Success! File saved to:', '$TIKTOKEN_CACHE_DIR')"