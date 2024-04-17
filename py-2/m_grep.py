#!/usr/bin/env python3
import utilities

def m_combine(parallel_res: list[str], full_files: list[str]):
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
    return append_together.rstrip('\n') 


all_read = utilities.read_all_w_original_files(); 
read = all_read[0]
full_files = all_read[1]
utilities.write_file(m_combine(read, full_files)) 