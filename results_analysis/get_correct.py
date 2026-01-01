import os
import json

results_root_dir = "/scratch/gpfs/ARORA/haoyu/algoveri/test_results"

def get_correct_results(language, model_name):
    correct_count = 0
    dir = os.path.join(results_root_dir, language)
    for filename in os.listdir(dir):
        if model_name in filename:
            filepath = os.path.join(dir, filename)
            # read json file
            with open(filepath, 'r') as f:
                result = json.load(f)
                if isinstance(result, dict) and result.get("verified") is True:
                    code = result.get("details", {}).get("llm_response", {}).get("code", "")
                    if "assume" not in code and "admit" not in code:  # ensure it's not a stub
                        correct_count += 1
                elif isinstance(result, list):
                    print(f"Processing list result in file: {filename}, total items: {len(result)}")
                    for item in result:
                        if isinstance(item, dict) and item.get("verified") is True:
                            code = item.get("details", {}).get("llm_response", {}).get("code", "")
                            if "assume" not in code and "admit" not in code and "#[verifier::external_body]" not in code:  # ensure it's not a stub
                                correct_count += 1
                                print(code)
                                print("\n\n\n")
                                break
    return correct_count

if __name__ == '__main__':
    language = "verus"
    model_name = "Qwen3-Next-80B-A3B-Thinking"
    correct = get_correct_results(language, model_name)
    print(f"Total correct results for {language} with model {model_name}: {correct}")