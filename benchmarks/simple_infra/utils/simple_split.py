def get_file_len(file_path: str) -> int:
    file_len = 0
    with open(file_path, 'rb') as f:
        for _ in f:
            file_len += 1
    return file_len

def write_n_lines(input_file, output_path: str, n_lines: int): 
    with open(output_path, 'wb') as out_file:
        for line_cnt, line in zip(range(n_lines), input_file):
            if (line_cnt == n_lines):
                return
            out_file.write(line)
            
def split_file(file_path: str, split_size: int, out_file_prefix: str): 
    file_sz = get_file_len(file_path)
    lines_per_file, leftover_lines = divmod(file_sz, split_size)
    
    split_files = [f"{out_file_prefix}{i}.txt" for i in range(split_size)]
    file_line_cnts = [lines_per_file for _ in split_files]
    file_line_cnts[-1] += leftover_lines
    with open(file_path, 'rb') as in_file:
        for out_path, line_cnt in zip(split_files, file_line_cnts):
            write_n_lines(in_file, out_path, line_cnt)
   
    return split_files


# encoding='UTF-8', newline='\n'