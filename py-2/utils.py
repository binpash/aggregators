import sys, re, io 
from subprocess import check_output

## MORE PRECISE READ (used by curr agg))
EOF_IS_NL = True
def read_file(fname):
  try: 
    return io.open(fname, 'r', encoding='UTF-8-sig', newline='\n').readlines()
  except UnicodeDecodeError: 
    raise UnicodeDecodeError

def read_all(append_NL_end=False): 
  global EOF_IS_NL
  all_contents = []
  for f in sys.argv[1:]:
    try: 
      contents = read_file(f)
      if contents: 
        EOF_IS_NL = EOF_IS_NL and contents[-1].endswith('\n')
        if append_NL_end: 
          if EOF_IS_NL is False: contents[-1] += "\n"
      all_contents.append(contents)
    except IOError as _err:
      # sys.stderr.write(f + ": " + _err.strerror + "\n") 
      continue
  return all_contents

## MORE PRECISE WRITE (used by curr agg)
def out(s):
  # print(s)
  global EOF_IS_NL
  if (not s): 
    sys.stdout.write("")
    return
  if not s.endswith('\n') and EOF_IS_NL:
    sys.stdout.write(s + '\n')
  else:
    sys.stdout.write(s)
  sys.stdout.flush()

def findPadLength(s): 
  return len(s) - len(s.lstrip(' '))

def getExactLocale(): 
  all_locale_setting = check_output(["locale"]).decode(sys.stdout.encoding)
  # sys_locale = all_locale_setting.split('\n')[1].split("=")[1]  
  
  for line in all_locale_setting.split("\n"):
    if line.startswith("LC_COLLATE"):
        lc_collate = line.split("=")[1].strip('"')
  return lc_collate
  assert(all_locale_setting.split('\n')[1].split("=")[0] == "LC_COLLATE") # find sorting weight
  return sys_locale.split('"')[1] # return locale without quotation 

def std_err_print(*args, **kwargs): 
    print(*args, file=sys.stderr, **kwargs)

### MULT. INPUT UTILS (used by multiple input agg [draft]) ###
def read_file_2(file_path):
    file = open(file_path, "r", encoding='utf-8-sig')
    if file == None: raise FileNotFoundError
    return file.read()

def file_content_to_str_arr(file_path):
    try: 
        content = read_file(file_path)
        return str(content)
    except (FileNotFoundError, IOError) as e : 
        sys.stderr.write("err: " + e.strerror + " from " + file_path + "\n")
        return None

def read_all_2(): 
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

# def match_file(full_file, par_file):
#     match = full_file.split(".txt")[0]
#     pattern = re.escape(match) + '-\d+\.txt'
#     return True if (re.search(re.compile(pattern), par_file) != None) else False

def extract_base_file(par_file): 
    if par_file == "total": return par_file
    pattern = re.compile(r'(.+)-\d+\.txt')
    match = re.search(pattern, par_file)
    return (match.group(1)+".txt").strip()