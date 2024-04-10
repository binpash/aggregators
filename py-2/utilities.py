import sys, re 

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

def read_all(): 
  all_contents = []
  for f in sys.argv[1:]:
    contents = file_content_to_str_arr(f)
    all_contents.append(contents)
  return all_contents

def read_all_w_original_files(): 
  all_contents = []
  i = 1 
  try: 
    while sys.argv[i] != "full": 
      contents = file_content_to_str_arr(sys.argv[i])
      all_contents.append(contents)
      i+=1 
  except IndexError:
      sys.stderr.write("missing full files, please add: full [path to full file 1] [path to full file 2] <etc> \n")
      sys.exit
  return [all_contents, sys.argv[i+1:]]

def write_file(content:str):
    sys.stdout.write(content + "\n")
    sys.stdout.flush()

def match_file(full_file, par_file):
    match = full_file.split(".txt")[0]
    pattern = re.escape(match) + '-\d+\.txt'
    return True if (re.search(re.compile(pattern), par_file) != None) else False

def extract_base_file(par_file): 
    if par_file == "total": return par_file
    pattern = re.compile(r'(.+)-\d+\.txt')
    match = re.search(pattern, par_file)
    return (match.group(1)+".txt").strip()