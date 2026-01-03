import os

def generate_lean_check_prompt(task_name):
    base_path = "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data"
    dir_path = os.path.join(base_path, task_name)
    lean_file = os.path.join(dir_path, "lean_spec.lean")
    dafny_file = os.path.join(dir_path, "dafny_spec.dfy")
    verus_file = os.path.join(dir_path, "verus_spec.rs")

    lean_code = ""
    with open(lean_file, 'r') as f:
        lean_code = f.read()
    dafny_code = ""
    with open(dafny_file, 'r') as f:
        dafny_code = f.read()
    verus_code = ""
    with open(verus_file, 'r') as f:
        verus_code = f.read()
    
    prompt = f"I am working on a formal verification benchmark. I already have the specification from Dafny and Verus, and I want to check if my specification in Lean is correct and completely reflect the functional correctness requirement for {task_name} and also align with the Dafny and Verus specifications. Here are the codes:\n\nDafny Specification:\n{dafny_code}\n\nVerus Specification:\n{verus_code}\n\nLean Specification:\n{lean_code}\n\nPlease help me verify the Lean specification."

    print(prompt)

if __name__ == "__main__":
    task_name = "topological_sort"
    if len(os.sys.argv) > 1:
        task_name = os.sys.argv[1]
    generate_lean_check_prompt(task_name)