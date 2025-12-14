import json
import argparse
import sys

def get_file_type(f):
    """
    Peeks at the first non-whitespace character to determine format.
    Returns: 'list' (JSON array), 'lines' (JSONL), or None.
    """
    pos = f.tell() # Remember start position
    try:
        while True:
            char = f.read(1)
            if not char: return None # Empty file
            if not char.isspace():
                if char == '[': return 'list'
                if char == '{': return 'lines'
                return None # Unknown format
    finally:
        f.seek(pos) # Reset file pointer to start

def main():
    parser = argparse.ArgumentParser(description="Extract top N entries from JSON or JSONL files (auto-detected).")
    parser.add_argument("input", help="Input file path")
    parser.add_argument("output", help="Output JSONL file path")
    parser.add_argument("--limit", type=int, default=100, help="Number of entries to extract")
    
    args = parser.parse_args()
    
    entries = []

    try:
        print(f"Inspecting {args.input}...")
        
        with open(args.input, 'r', encoding='utf-8') as f:
            file_type = get_file_type(f)

            if file_type == 'list':
                print("Format detected: Standard JSON Array ( [...] )")
                # We must load the whole array to slice it safely with standard lib
                data = json.load(f)
                if isinstance(data, list):
                    entries = data[:args.limit]
                else:
                    print("Error: JSON file contains a single object, not a list.")
                    sys.exit(1)

            elif file_type == 'lines':
                print("Format detected: JSONL / Line-delimited ( {...}\\n{...} )")
                # Optimization: We only read up to the limit, we don't load the whole file
                count = 0
                for line in f:
                    if count >= args.limit:
                        break
                    line = line.strip()
                    if line:
                        try:
                            entries.append(json.loads(line))
                            count += 1
                        except json.JSONDecodeError:
                            print(f"Warning: Skipping invalid JSON on line {count+1}")

            else:
                print("Error: Could not determine format. File must start with '[' or '{'.")
                sys.exit(1)

        # Write Output
        print(f"Writing {len(entries)} items to {args.output}...")
        with open(args.output, 'w', encoding='utf-8') as f_out:
            for entry in entries:
                f_out.write(json.dumps(entry) + '\n')

        print("Done.")

    except FileNotFoundError:
        print(f"Error: File '{args.input}' not found.")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()