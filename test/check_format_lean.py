import os
import re

data_path = "/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data"

def clean_lean_code(text):
    """
    Removes Lean comments and whitespace to check actual content.
    """
    # Remove block comments /- ... -/
    # pattern matches /- followed by anything (non-greedy) until -/
    text = re.sub(r'/-[\s\S]*?-/', '', text)
    
    # Remove single line comments -- ...
    text = re.sub(r'--.*', '', text)
    
    # Return stripped text
    return text.strip()

def validate_file_structure(content):
    """
    Parses the file to ensure strict order: auxcode -> code -> lemma -> proof.
    Returns (True, None) if valid, or (False, Reason) if invalid.
    """
    
    # Define the markers in strict order
    sections = [
        ("auxcode", "-- !benchmark @start auxcode", "-- !benchmark @end auxcode", "empty"),
        ("code",    "-- !benchmark @start code",    "-- !benchmark @end code",    "sorry"),
        ("lemma",   "-- !benchmark @start lemma",   "-- !benchmark @end lemma",   "empty"),
        ("proof",   "-- !benchmark @start proof",   "-- !benchmark @end proof",   "sorry"),
    ]
    
    current_idx = 0
    
    for name, start_marker, end_marker, requirement in sections:
        # 1. Find start marker (must be after the previous section)
        start_idx = content.find(start_marker, current_idx)
        if start_idx == -1:
            return False, f"Missing or out-of-order start marker: {name}"
            
        # 2. Find end marker (must be after start marker)
        end_idx = content.find(end_marker, start_idx)
        if end_idx == -1:
            return False, f"Missing end marker: {name}"
        
        # 3. Extract content between markers
        # We assume content starts after the newline of the start marker
        # and ends before the end marker.
        raw_section_content = content[start_idx + len(start_marker):end_idx]
        
        cleaned_content = clean_lean_code(raw_section_content)
        
        # 4. Validate Content
        if requirement == "empty":
            if cleaned_content != "":
                return False, f"Section '{name}' must be empty but contains code."
        elif requirement == "sorry":
            # Allows 'sorry' or completely empty (if you consider just comments valid)
            # If you strictly require 'sorry' to be present, change to: if cleaned_content != "sorry":
            if cleaned_content != "sorry" and cleaned_content != "":
                return False, f"Section '{name}' must only contain 'sorry' but contains other code."

        # Update current index to ensure next section appears AFTER this one
        current_idx = end_idx + len(end_marker)

    return True, None

# --- Main Execution ---

counter = 0
total_files = 0
invalid_files = []

if os.path.exists(data_path):
    for dirs in os.listdir(data_path):
        dir_path = os.path.join(data_path, dirs)
        if os.path.isdir(dir_path):
            for file in os.listdir(dir_path):
                if file.endswith("lean_spec.lean"):
                    total_files += 1
                    file_path = os.path.join(dir_path, file)
                    
                    with open(file_path, 'r') as f:
                        content = f.read()
                    
                    is_valid, reason = validate_file_structure(content)
                    
                    if is_valid:
                        counter += 1
                    else:
                        print(f"[Invalid] {file_path}")
                        print(f"    Reason: {reason}")
                        invalid_files.append(file_path)
else:
    print(f"Path not found: {data_path}")

print("-" * 30)
print(f"Total Lean files found: {total_files}")
print(f"Valid formatted files:  {counter}")
print(f"Invalid files:          {len(invalid_files)}")