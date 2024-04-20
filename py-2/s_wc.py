#!/usr/bin/env python3
import utilities, re 

def s_combine(parallel_res: list[str]):
    # maintain string pad length by splitting when number ends
    build_sum = parallel_res[0]
    for res in parallel_res[1:]:
        if res == None or res.strip() == "": continue 
        build_sum = "".join(str(int(x) + int(y)).rjust(len(x)) for x, y in zip(re.findall("\s*\d+", build_sum), re.findall("\s*\d+", res)))
    return build_sum

read = utilities.read_all()
utilities.write_file(s_combine(read)) 
