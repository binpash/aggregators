class Grep_Par_Metadata:
    '''
    A metadata object helpful for line correction on parallel outputs 

    Fields:
        * file_path: the file this represents 
        * number_of_blocks: how many blocks is the entire file divided into for parallel execution 
        * size_arr: an array of line numbers in each block 
    '''

    def __init__(self, file_path: str, number_of_blocks: int, size_arr: list[int]):
        self.file_path = file_path
        self.number_of_blocks = number_of_blocks
        self.size_arr = size_arr


class Grep_Par_Output:
    '''
    Represents one block of parallel execution after grep -n 

    Fields:
        * parallel_ouptut: array that holds parallel outputs where each entry is a line of output 
        * block_number: which parallel order is this current block (maintains order for line count correction)
    '''

    def __init__(self, parallel_output: list[str] or str, block_number: int):
        self.parallel_output = parallel_output
        self.block_number = block_number-1
