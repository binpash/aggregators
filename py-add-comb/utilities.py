import sys 

def read_file(file_path):
    file = open(file_path, "r")
    if file == None: raise FileNotFoundError
    return file.read()

def file_content_to_str_arr(file_path):
    try: 
        content = read_file(file_path=file_path)
        # remove final '\n' at the end of the file
        if len(content) > 0 and content[-1].endswith('\n'): content = content[:-1]
        return str(content)
    except (FileNotFoundError, IOError) as e : 
        sys.stderr.write("err: " + e.strerror + " from " + file_path + "\n")
        return None

def process_input_to_array(output_A, output_B): 
    parallel_res = []
    if output_A == None or output_A.strip() == "": 
        parallel_res.append(file_content_to_str_arr(output_A))
    elif output_B == None or output_B.strip() == "":
        parallel_res.append(file_content_to_str_arr(output_B))
    else: 
        parallel_res.append(file_content_to_str_arr(output_A))
        parallel_res.append(file_content_to_str_arr(output_B))
    return parallel_res

def write_file(content:str):
    sys.stdout.write(content + "\n")
    sys.stdout.flush()
