import os
import shutil
import tiktoken
from openai_harmony import load_harmony_encoding, HarmonyEncodingName

# 1. Define a local cache directory
cache_dir = os.path.abspath("./tiktoken_cache")
os.makedirs(cache_dir, exist_ok=True)

# 2. Force tiktoken to use this directory
os.environ["TIKTOKEN_CACHE_DIR"] = cache_dir

print(f"Downloading Harmony vocab files to: {cache_dir} ...")

try:
    # This triggers the download of the specific encodings needed for GPT-OSS
    load_harmony_encoding(HarmonyEncodingName.HARMONY_GPT_OSS)
    print("Success! Files downloaded.")
except Exception as e:
    print(f"Error: {e}")

print(f"Please upload the folder '{cache_dir}' to your cluster.")