#!/usr/bin/env python3
import utils, re 

def s_combine(parallel_res: list[str]):
    # maintain string pad length by splitting when number ends
    r = "\s*\d+" # for measuring padding size
    build_sum = parallel_res[0]
    for res in parallel_res[1:]:
        if res == None or res.strip() == "": continue 
        build_sum = "".join(str(int(x) + int(y)).rjust(len(x)) for x, y in zip(re.findall(r, build_sum), re.findall(r, res)))
    return build_sum

read = utils.read_all_2()
utils.write_file(s_combine(read)) 
