import sys 

def read_file(file_path:str):
    file = open(file_path, "r")
    if file == None: raise FileNotFoundError
    return file.read()
  
def file_content_to_str_arr(file_path:str):
    try: 
        content = read_file(file_path=file_path)
        return str(content)
    except (FileNotFoundError, IOError) as e : 
        sys.stderr.write("err: " + e.strerror + " from " + file_path + "\n")
        return None

def process_input_to_array(output_A:str, output_B:str): 
    parallel_res = []
    if (output_B == None or output_B.strip() == "") and (output_A == None or output_A.strip() == ""):
        raise ValueError('both input cannot be nothing')
    
    if output_A == None or output_A.strip() == "": 
        parallel_res.append(file_content_to_str_arr(output_A))
    elif output_B == None or output_B.strip() == "":
        parallel_res.append(file_content_to_str_arr(output_B))
    else: 
        parallel_res.append(file_content_to_str_arr(output_A))
        parallel_res.append(file_content_to_str_arr(output_B))
    print(parallel_res)
    return parallel_res