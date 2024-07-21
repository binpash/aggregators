#!/usr/bin/env python3
import utils

def s_combine(parallel_res: list[str]):
    # print(parallel_res)
    if parallel_res is None or len(parallel_res) == 0:
        return ""
    append_together = parallel_res[0]
    for res in parallel_res[1:]:
        append_together = append_together + res
    return append_together.strip("\n")


read = utils.read_all_2()
utils.write_file(s_combine(read)) 