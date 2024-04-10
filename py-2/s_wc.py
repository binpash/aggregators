import utilities

PAD_LEN = 8 

def s_combine(parallel_res: list[str]):
    build_sum = parallel_res[0] 
    for res in parallel_res[1:]:
        if res == None or res.strip() == "": continue
        build_sum = "".join(str(int(x) + int(y)).rjust(PAD_LEN, ' ') for x, y in zip(build_sum.split(), res.split()))
    return build_sum

read = utilities.read_all()
utilities.write_file(s_combine(read)) 