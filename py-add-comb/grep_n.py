import math
from typing import Dict
from grep_meta import Grep_Par_Output, Grep_Par_Metadata

def get_line_number_correction(metadata: Grep_Par_Metadata, block_number: int):
    '''
    Adds up the size of blocks before this block for the total number of lines to correct by 

    Returns: 
        add this value to the line to get the corrected line; 
        the corrected line is the line number of this line considering the entire file 
            and not only this parallel output block 
    '''
    line_number_correction: int = 0
    for prev_block_number in range(0, block_number):
        line_number_correction += metadata.size_arr[prev_block_number]
    return line_number_correction


def line_correction_all(blocks: list[Grep_Par_Output], metadata: Grep_Par_Metadata, is_single_file: bool):
    '''
    Correct all lines in a block 
    Expected that all lines in this block comes from the file in metadata 

    Params: 
        blocks: list of grep_par_output, where each contains the parallel grep result and its block order number 
        metadata: must be ONE FILE; contains information on size of all blocks
        is_single_file: to differentiate where the line number is; 
            if only 1 file in grep input: 3:hiHIiii
            if 2+ file in grep input: randomText.txt:3:hiHIiii

    Return: 
        A collective array of all lines with their line number corrected 
    '''
    correction_arr: list[Grep_Par_Output] = []
    line_correction = 0

    # get the number of line (3):
    #   if more than 2+ files (randomText.txt:3:hiHIiii), grab the 1st argument
    #   if only one file (3:hiHIiii), grab the 0th element
    line_num_idx = 0 if is_single_file else 1

    for block in blocks:
        line_correction = get_line_number_correction(
            metadata, block.block_number)
        corrected_block = []
        # correct all lines in this block by adding on the line_correction
        for line in block.parallel_output:
            line_to_arr = line.split(":")
            line_to_arr[line_num_idx] = str(
                int(line_to_arr[line_num_idx]) + line_correction)
            corrected_line = ":".join(line_to_arr)
            corrected_block.append(corrected_line)
        correction_arr.extend(corrected_block)

    return correction_arr

# TODO: error checking for output line number is within bounds of the metadata size
# TODO: error checking for block number is within range of metadata


def grep_in(parallel_res: list[Grep_Par_Output], metadata_list: list[Grep_Par_Metadata]):
    '''
    Combines parallized grep result when used with the -in flag 
    Specifically fit to combine grep results with -n flag by correcting line number on the line 

    Params: 
        parallel_res: list of grep_par_output, where each contains the parallel grep result and its block order number 
        metadata_list: one for each unique file as argument into grep 

    Return: 
       a string result of all grep results concat together and separated by newline 
    '''
    if parallel_res is None or len(parallel_res) == 0:
        return ""

    # determine if only one file is used in grep
    is_single_file = (len(metadata_list) == 1)

    # correct all lines in all blocks
    arr_with_corrected = []
    if is_single_file:
        arr_with_corrected = line_correction_all(
            parallel_res, metadata_list[0], is_single_file)
    else:
        # We need to organize each line to metadata correctly based on its file name
        file_to_outputs: Dict[str, Grep_Par_Output] = {}
        for block in parallel_res:
            for line in block.parallel_output:
                file_name = line.split(":")[0]
                # Easiest would be to make each line a Grep_Par_Output and remain its block number
                # Note: add 1 to block number since constructor subtracts 1 too
                if file_name in file_to_outputs:
                    file_to_outputs[file_name].append(
                        Grep_Par_Output([line], block.block_number+1))
                else:
                    file_to_outputs[file_name] = [
                        Grep_Par_Output([line], block.block_number+1)]

       # correct line number by getting the right metadata
        for key, output in file_to_outputs.items():
            curr_metada: Grep_Par_Metadata = None
            for metada in metadata_list:
                if (metada.file_path == key):
                    curr_metada = metada
            if (curr_metada == None):
                raise ValueError("metadata for file " +
                                 file_name + " not found!")
            arr_with_corrected.extend(
                line_correction_all(output, curr_metada, False))

    # sort based on the line number
    sort_by_line_number = sorted(arr_with_corrected, key=lambda entry: int(
        entry.split(":")[0 if is_single_file else 1]))
    # sort based on the file name if not single_file
    if (is_single_file == False):
        sort_by_file = sorted(sort_by_line_number,
                              key=lambda entry: entry.split(":")[1 if is_single_file else 0])
    else:
        sort_by_file = sort_by_line_number

    # concat result into output + '\n'
    append_together = ""
    for corrected_res in sort_by_file:
        if corrected_res != "":
            append_together = append_together + corrected_res + '\n'

    return append_together.rstrip()

def grep_build_metada_two_blocks(file_name:str, file_content:str): 
    count_lines = len(file_content.split("\n"))
    block_1_size = 0 
    block_2_size = 0
    if count_lines % 2 != 0 : 
        block_1_size = math.floor(count_lines / 2)
        block_2_size = math.floor(count_lines / 2) + 1 
    else : 
        block_1_size = count_lines / 2
        block_2_size = count_lines / 2
    return Grep_Par_Metadata(file_name, number_of_blocks=2, size_arr=[block_1_size, block_2_size])

def grep_in_comb_two(output_A:str, output_B:str, input_files: Dict[str, str]): 
    metadata_list = []
    for file_name, file_content in input_files.items():
        metadata_list.append(grep_build_metada_two_blocks(file_name, file_content))

    parallel_res = []
    if (output_B == None or output_B.strip() == "") and (output_A == None or output_A.strip() == ""):
        raise ValueError('both input cannot be nothing')
    
    if output_A == None or output_A.strip() == "": 
        parallel_res.append(Grep_Par_Output(output_B.split("\n"), 1))
    elif output_B == None or output_B.strip() == "":
        parallel_res.append(Grep_Par_Output(output_A.split("\n"), 1))
    else: 
        parallel_res.append(Grep_Par_Output(output_A.split("\n"), 1))
        parallel_res.append(Grep_Par_Output(output_B.split("\n"), 2))
    return grep_in(parallel_res=parallel_res, metadata_list=metadata_list)

# Run 
files_to_content = {} 
files_to_content["hi.txt"] = "hi 1 gh \nhi 2\nhi3\nhi 4\nhi5\nhi6\nhi7"
files_to_content["bye.txt"] = "hi 1\nhi 2\nhi3\nhi4\nhi 5\nhi 6\nhi 7"
output_A = "bye.txt:1:hi 1\nhi.txt:3:hi 3 2"
output_B = "hi.txt:3:hi 6 g\nbye.txt:1:hi 4\nhi.txt:4:hi7"
print(grep_in_comb_two(output_A, output_B, files_to_content))

# grep -in: displays line count + case insensitive search
#   Multiple files:
# randomText.txt:2:hi
# randomText.txt:3:hiHIiii
# randomText.txt:4:Hiii
# randomText2.txt:2:hi
# randomText2.txt:3:hiHIiii
# randomText2.txt:4:Hiii
# grep -c : counts how many lines there are -- single file: 3
#   Multiple files:
#   # randomText.txt:3
# randomText2.txt:3
