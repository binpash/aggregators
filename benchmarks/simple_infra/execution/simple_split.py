def get_file_len(file_path: str) -> int:
    file_len = 0
    with open(file_path) as f:
        for _ in f:
            file_len += 1
    return file_len

def write_n_lines(input_file, output_path: str, n_lines: int): 
    with open(output_path, "w") as out_file:
        for line_cnt, line in zip(range(n_lines), input_file):
            if (line_cnt == n_lines):
                return
            out_file.write(line)
            
def split_file(file_path: str, split_size: int, out_file_prefix: str): 
    file_sz = get_file_len(file_path)
    lines_per_file, leftover_lines = divmod(file_sz, split_size)
    
    split_files = [f"{out_file_prefix}-{i}" for i in range(split_size)]
    file_line_cnts = [lines_per_file for _ in split_files]
    file_line_cnts[-1] += leftover_lines
    
    with open(file_path) as in_file:
        for out_path, line_cnt in zip(split_files, file_line_cnts):
            write_n_lines(in_file, out_path, line_cnt)
    return split_files

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="File splitter")
    parser.add_argument("--input_file", "-i", type=str)
    parser.add_argument("--split_size", "-n", type=int)
    parser.add_argument("--out_prefix", "-o", type=str)
    
    args = parser.parse_args()
    split_file(args.input_file, args.split_size, args.out_prefix)
    