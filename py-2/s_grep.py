import utilities

def s_combine(parallel_res: list[str]):
    if parallel_res is None or len(parallel_res) == 0:
        return ""
    append_together = ""
    for res in parallel_res:
        if res != "":
            append_together = append_together + res + '\n'
    return append_together.strip() 


read = utilities.read_all()
utilities.write_file(s_combine(read)) 