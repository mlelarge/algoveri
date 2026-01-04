import os

data_path = "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data"

counter = 0

for dirs in os.listdir(data_path):
    dir_path = os.path.join(data_path, dirs)
    if os.path.isdir(dir_path):
        for file in os.listdir(dir_path):
            if file.endswith("lean_spec.lean"):
                file_path = os.path.join(dir_path, file)
                with open(file_path, 'r') as f:
                    content = f.read()
                #if "assume" not in content and "admit" not in content and "#[verifier" not in content:
                if '-- !benchmark @start auxcode' in content and '-- !benchmark @end auxcode' in content and '-- !benchmark @start code' in content and '-- !benchmark @end code' in content and '-- !benchmark @start lemma' in content and '-- !benchmark @end lemma' in content and '-- !benchmark @start proof' in content and '-- !benchmark @end proof' in content:
                    counter += 1
                else:
                    print(f"Stub file: {file_path}")

print(f"Total number of non-stub Lean files: {counter}")