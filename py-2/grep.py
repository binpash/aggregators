import utilities, sys

def s_grep_combine(parallel_res: list[str]):
    if parallel_res is None or len(parallel_res) == 0:
        return ""
    append_together = ""
    for res in parallel_res:
        if res != "":
            append_together = append_together + res + '\n'
    return append_together.strip() 

def s_combine(output_A, output_B):
    try: 
       utilities.write_file(s_grep_combine(utilities.process_input_to_array(output_A, output_B)))
    except: 
        sys.stderr.write("error with combining grep results " + '\n')
        return False

def m_grep_combine(parallel_res: list[str], full_files: list[str]): 
    if parallel_res is None or len(parallel_res) == 0:
        return ""
    
    file_found_map = {}
    for file in full_files: file_found_map[file] = ""
    
    for res in parallel_res:
        if res != "":
            single_lines = res.split('\n')
            for line in single_lines:
                split_line = line.split(":")
                base_file = utilities.extract_base_file(split_line[0])
                if utilities.extract_base_file(split_line[0]) in file_found_map:
                    new_entry = base_file + ":" + split_line[1]
                    file_found_map[base_file] = file_found_map[base_file] + "\n" + new_entry
    append_together = ""
    for values in file_found_map.values(): append_together = append_together + values
    return append_together.strip() 

def m_combine(output_A, output_B, full_files:list[str]):
    try: 
       utilities.write_file(m_grep_combine(utilities.process_input_to_array(output_A, output_B), full_files))
    except: 
        sys.stderr.write("error with combining grep results " + '\n')
        return False