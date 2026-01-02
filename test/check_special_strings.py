import os

data_path = "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data"

counter = 0

for dirs in os.listdir(data_path):
    dir_path = os.path.join(data_path, dirs)
    if os.path.isdir(dir_path):
        for file in os.listdir(dir_path):
            if file.endswith(".rs"):
                file_path = os.path.join(dir_path, file)
                with open(file_path, 'r') as f:
                    content = f.read()
                if "assume" not in content and "admit" not in content and "#[verifier" not in content:
                #if 'assume' not in content and "verify false" not in content and "axiom" not in content and "extern" not in content or "expect" not in content:
                    counter += 1
                else:
                    print(f"Stub file: {file_path}")

print(f"Total number of non-stub Verus files: {counter}")