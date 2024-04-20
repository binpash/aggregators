# for line correction, we need the original file 
import utilities

global line_count

# def line_correction_all(blocks: list[Grep_Par_Output], metadata: Grep_Par_Metadata, is_single_file: bool):
#     '''
#     Correct all lines in a block 
#     Expected that all lines in this block comes from the file in metadata 

#     Params: 
#         blocks: list of grep_par_output, where each contains the parallel grep result and its block order number 
#         metadata: must be ONE FILE; contains information on size of all blocks
#         is_single_file: to differentiate where the line number is; 
#             if only 1 file in grep input: 3:hiHIiii
#             if 2+ file in grep input: randomText.txt:3:hiHIiii

#     Return: 
#         A collective array of all lines with their line number corrected 
#     '''
#     correction_arr: list[Grep_Par_Output] = []
#     line_correction = 0

#     # get the number of line (3):
#     #   if more than 2+ files (randomText.txt:3:hiHIiii), grab the 1st argument
#     #   if only one file (3:hiHIiii), grab the 0th element
#     line_num_idx = 0 if is_single_file else 1

#     for block in blocks:
#         line_correction = get_line_number_correction(
#             metadata, block.block_number)
#         corrected_block = []
#         # correct all lines in this block by adding on the line_correction
#         for line in block.parallel_output:
#             line_to_arr = line.split(":")
#             line_to_arr[line_num_idx] = str(
#                 int(line_to_arr[line_num_idx]) + line_correction)
#             corrected_line = ":".join(line_to_arr)
#             corrected_block.append(corrected_line)
#         correction_arr.extend(corrected_block)

#     return correction_arr




read_w_file = utilities.read_all_w_original_files() 
read = read_w_file[0] 
file = read_w_file[1][0]
with open(file, 'r') as file:
    line_count = sum(1 for line in file)

print(line_count)
# utilities.write_file(s_combine(read, file))


    