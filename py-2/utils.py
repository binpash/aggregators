import sys, subprocess, os, re, locale, io 

locale.setlocale(locale.LC_ALL, 'en_US.UTF-8')
EOF_IS_NL = True

def read_file(fname):
  try:
    return io.open(fname, 'r', encoding='UTF-8-sig', newline='\n').readlines()
  except IOError as _err:
    # os.path.basename(sys.argv[0]) + ": " + 
    sys.stderr.write(fname + ": " + _err.strerror + "\n")

def read_all(append_NL_end=False): 
  global EOF_IS_NL
  all_contents = []
  for f in sys.argv[1:]:
    contents = read_file(f)
    EOF_IS_NL = EOF_IS_NL and contents[-1].endswith('\n')
    if append_NL_end: 
      if EOF_IS_NL is False: contents[-1] += "\n"
    all_contents.append(contents)
  return all_contents

def read_file_2(file_path):
    file = open(file_path, "r", encoding='utf-8-sig')
    if file == None: raise FileNotFoundError
    return file.read()

def file_content_to_str_arr(file_path):
    try: 
        content = read_file(file_path)
        # remove final '\n' at the end of the file
        # if len(content) > 0 and content[-1].endswith('\n'): content = content[:-1]
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

#def out():
#  if (sys.version_info.major == 2):
#    print **locals(),
#  else:
#    print(**locals(), end=' ')
def out(s):
  global EOF_IS_NL
  if not s.endswith('\n') and EOF_IS_NL:
    sys.stdout.write(s + '\n')
  else:
    sys.stdout.write(s)
  sys.stdout.flush()

def cmd():
  c = sys.argv[0].replace(".py", "").replace("./", "")
  if 'MAP_CMD' in os.environ:
    c = os.environ['MAP_CMD']
  return c

def execute(command, data):
    p = subprocess.Popen([command], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    return p.communicate(data)[0]
    # Python 3 equivalent:
    # p = subprocess.run([cmd], stdout=subprocess.PIPE, input=data, encoding='ascii', check=True)
    # return p.stdout

def help(c=cmd()):
  m = c
  s = ' <(cat 1.t | ' + m + ') <(cat 2.t | ' + m + ') <(cat 3.t | ' + m + ')'
  # if len(sys.argv) < 2:
  #   print 'echo "one\\ntwo\\nthree" > 1.t'
  #   print 'echo "four\\nfive" > 2.t'
  #   print 'echo "one\\ntwo\\nthree" > 3.t'
  #   print sys.argv[0] + s
  #   print '\nTo quickly test equivalence: '
  #   print sys.argv[0] + s + ' > par.txt'
  #   print 'cat 1.t 2.t 3.t | ' + m + ' > seq.txt'
  #   print 'diff {seq,par}.txt'


def findPadLength(s): 
  return len(s) - len(s.lstrip(' '))

def match_file(full_file, par_file):
    match = full_file.split(".txt")[0]
    pattern = re.escape(match) + '-\d+\.txt'
    return True if (re.search(re.compile(pattern), par_file) != None) else False

def extract_base_file(par_file): 
    if par_file == "total": return par_file
    pattern = re.compile(r'(.+)-\d+\.txt')
    match = re.search(pattern, par_file)
    return (match.group(1)+".txt").strip()