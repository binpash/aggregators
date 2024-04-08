import pytest
from grep_meta import Grep_Par_Metadata, Grep_Par_Output
from combiners.grep_n import grep_in
from combiners.grep_c import grep_c
from combiners.wc import wc_flags_combine, wc_comb_two


def test_wc_combine_no_flags():
    '''
    Test wc_combine with:
        1) different number of paralleled ouputs
        2) no file name if the output were directed to stdout
        3) error input
        4) from same file and from different files
    '''
    assert wc_flags_combine(["4 3 20 hi.txt", "3 2 10 hi.txt",
                             "3 5 100 hi.txt"]) == "10 10 130 hi.txt"
    assert wc_flags_combine(["0 0 0 ", "0 0 0 "]) == "0 0 0 "
    assert wc_flags_combine(["30 54 10000 ", "0 0 0 "]) == "30 54 10000 "
    assert wc_flags_combine(["30 54 10000 bye.txt"]) == "30 54 10000 bye.txt"
    assert wc_flags_combine([]) == ""
    assert wc_flags_combine(["30 54 10000 hi.txt", "10 6 1002 bye.txt", "40 60 11002 total"]
                            ) == "30 54 10000 hi.txt\n10 6 1002 bye.txt\n40 60 11002 total"
    print(wc_flags_combine(["30 54 10000 hi.txt", "40 60 11002 total", "10 6 1002 bye.txt", "20 400 1001 hi.txt", "0 0 0 bye.txt", "20 400 1001 total"]))
    assert wc_flags_combine(["30 54 10000 hi.txt", "40 60 11002 total", "10 6 1002 bye.txt", "20 400 1001 hi.txt", "0 0 0 bye.txt", "20 400 1001 total"]
                            ) == "50 454 11001 hi.txt\n10 6 1002 bye.txt\n60 460 12003 total"
    assert wc_flags_combine(["10 500 1000 bye.txt", "100 100 10000 ", "30 950 8030 ", "20 400 1000 hi.txt", "20 400 1000 bye.txt", "10 6 1002 ", "190 2356 22032 total"]
                            ) == "30 900 2000 bye.txt\n140 1056 19032 \n20 400 1000 hi.txt\n190 2356 22032 total"
    assert wc_flags_combine(["10 500 1000 bye.txt", "100 100 10000 ", "30 950 8030 hi2.txt", "20 400 1000 hi.txt", "180 2350 21030 total", "20 400 1000 bye2.txt"]
                            ) == "10 500 1000 bye.txt\n100 100 10000 \n30 950 8030 hi2.txt\n20 400 1000 hi.txt\n20 400 1000 bye2.txt\n180 2350 21030 total"
    assert wc_flags_combine(["30 54 10000 hi.txt", "0 0 0 bye.txt", "10 6 1002 bye.txt", "40 60 11002 total"]
                            ) == "30 54 10000 hi.txt\n10 6 1002 bye.txt\n40 60 11002 total"


def test_wc_combine_flags():
    '''
    Test wc_combine with:
        1) single, double, and triple flags (sample such as -c, -cl, -lm...)
    '''
    # test single flag
    assert wc_flags_combine(["4 hi.txt", "3 hi.txt",
                             "3 hi.txt", "1 hi.txt"]) == "11 hi.txt"
    assert wc_flags_combine(["30 hi.txt", "10 bye.txt", "40 total", "20 hi.txt", "0 bye.txt", "20 total"]
                            ) == "50 hi.txt\n10 bye.txt\n60 total"
    assert wc_flags_combine(["30 hi.txt", "10 bye.txt", "20 hi.txt", "130 total", "30 hi.txt", "40 apples.txt"]
                            ) == "80 hi.txt\n10 bye.txt\n40 apples.txt\n130 total"

    # test two flags
    assert wc_flags_combine(["4 2 hi.txt", "3 0 hi.txt",
                             "3 10 hi.txt", "1 5 hi.txt"]) == "11 17 hi.txt"
    assert wc_flags_combine(["30 20 hi.txt"]
                            ) == "30 20 hi.txt"
    assert wc_flags_combine(["30 100 hi.txt", "10 300 bye.txt", "130 1760 total","20 200 hi.txt", "30 520 hi.txt", "40 640 apples.txt"]
                            ) == "80 820 hi.txt\n10 300 bye.txt\n40 640 apples.txt\n130 1760 total"
    assert wc_flags_combine(["30 100 hi.txt", "10 300 bananas.txt", "130 1760 total", "20 200 hi.txt", "30 520 hi.txt", "40 640 apples.txt"]
                            ) == "80 820 hi.txt\n10 300 bananas.txt\n40 640 apples.txt\n130 1760 total"

    # test three flags
    assert wc_flags_combine(["4 2 2 hi.txt", "3 0 1 hi.txt",
                             "3 10 0 hi.txt", "1 5 2 hi.txt"]) == "11 17 5 hi.txt"
    assert wc_flags_combine(["30 20 60 hi.txt"]
                            ) == "30 20 60 hi.txt"
    assert wc_flags_combine(["30 100 0 hi.txt","0 0 0 apples.txt","0 0 0 bye.txt", "30 100 0 total", "10 300 1 bye.txt", "20 200 2 hi.txt", "0 0 0 apples.txt", "30 500 3 total", "30 520 500 hi.txt", "0 0 0 bye.txt", "40 640 600 apples.txt", "70 1160 1100 total"]
                            ) == "80 820 502 hi.txt\n40 640 600 apples.txt\n10 300 1 bye.txt\n130 1760 1103 total"
    assert wc_flags_combine(["30 100 30 hi.txt", "10 300 9 bananas.txt", "20 200 10000 hi.txt", "30 520 23023 hi.txt", "130 1760 43062 total", "40 640 10000 apples.txt"]
                            ) == "80 820 33053 hi.txt\n10 300 9 bananas.txt\n40 640 10000 apples.txt\n130 1760 43062 total"

def test_wc_two_combine():
    output_A = "30 100 0 hi.txt\n0 0 0 apples.txt\n0 0 0 bye.txt\n30 100 0 total"
    output_B = "10 300 1 bye.txt\n20 200 2 hi.txt\n0 0 0 apples.txt\n30 500 3 total"
    assert wc_comb_two(output_A, output_B) == "50 300 2 hi.txt\n0 0 0 apples.txt\n10 300 1 bye.txt\n60 600 3 total"

    output_A2 = "4 2 hi.txt"
    output_B2 = "3 0 hi.txt"
    assert wc_comb_two(output_A2, output_B2) == "7 2 hi.txt"

def test_grep_in_one_file():
    # 2 blocks
    hi_metadata = Grep_Par_Metadata("hi.txt", 2, [100, 5])
    hi_1 = Grep_Par_Output(["2:hi how are you", "1:HihiIIhi", "3:Hihi"], 2)
    hi_0 = Grep_Par_Output(["3:hiHiiHI", "5:hi today's a nice day"], 1)
    assert (grep_in([hi_0, hi_1], [hi_metadata]) ==
            "3:hiHiiHI\n5:hi today's a nice day\n101:HihiIIhi\n102:hi how are you\n103:Hihi")

    # sequential execution (1 block only)
    bye_metadata = Grep_Par_Metadata("hi.txt", 1, [5])
    bye_1 = Grep_Par_Output(
        ["2:hi how are you", "5:hi today's a nice day", "3:Hihi"], 1)
    assert (grep_in([bye_1], [bye_metadata]) ==
            "2:hi how are you\n3:Hihi\n5:hi today's a nice day")

    # 3 blocks
    hi_metadata = Grep_Par_Metadata("hi.txt", 3, [30, 101, 2])
    hi_1 = Grep_Par_Output(["101:hi how are you", "80:HihiIIhi", "23:Hihi"], 2)
    hi_2 = Grep_Par_Output(["1:HihiIIhi", "2:Hihi"], 3)
    hi_0 = Grep_Par_Output(["29:hiHiiHI"], 1)
    assert (grep_in([hi_0, hi_2, hi_1], [hi_metadata]) ==
            "29:hiHiiHI\n53:Hihi\n110:HihiIIhi\n131:hi how are you\n132:HihiIIhi\n133:Hihi")


def test_grep_in_two_plus_file():
    # 2 files
    grape_metadata = Grep_Par_Metadata("grapes.txt", 4, [100, 40, 5, 0])
    pear_metadata = Grep_Par_Metadata("pear.txt", 4, [4, 120, 10, 20])
    block_1 = Grep_Par_Output(
        ["grapes.txt:99:fruits are the best", "pear.txt:2:the best Ffruit is pear", "grapes.txt:100:fruits are the best"], 1)
    block_2 = Grep_Par_Output(
        ["grapes.txt:32:the best FFFFfruit", "pear.txt:20:hi this is a fruitt", "pear.txt:1:fruitsssS", "grapes.txt:5:fruits are the best"], 2)
    block_3 = Grep_Par_Output(
        ["pear.txt:10:fruits", "grapes.txt:2:fruit-s"], 3)
    block_4 = Grep_Par_Output(
        ["pear.txt:10:fruits", "pear.txt:2:the best Ffruit is pear"], 4)
    assert (grep_in([block_1, block_3, block_4, block_2],
                    [grape_metadata, pear_metadata]) == "grapes.txt:99:fruits are the best\ngrapes.txt:100:fruits are the best\ngrapes.txt:105:fruits are the best\ngrapes.txt:132:the best FFFFfruit\ngrapes.txt:142:fruit-s\npear.txt:2:the best Ffruit is pear\npear.txt:5:fruitsssS\npear.txt:24:hi this is a fruitt\npear.txt:134:fruits\npear.txt:136:the best Ffruit is pear\npear.txt:144:fruits")

    # 3 files
    bye_metadata = Grep_Par_Metadata("bye.txt", 3, [100, 40, 5])
    apple_metadata = Grep_Par_Metadata("apple.txt", 3, [10, 100, 30])
    hi_metadata = Grep_Par_Metadata("hi.txt", 3, [1, 1, 0])
    block_one = Grep_Par_Output(
        ["apple.txt:3:hi", "bye.txt:5:hi when do you", "hi.txt:1:hiiiii"], 1)
    block_two = Grep_Par_Output(["hi.txt:1:hi", "bye.txt:3:hi"], 2)
    block_three = Grep_Par_Output(
        ["bye.txt:3:the word hi is", "bye.txt:6:Hihiiii"], 3)
    print(grep_in([block_one, block_two, block_three],
                  [bye_metadata, hi_metadata, apple_metadata]))
    assert (grep_in([block_one, block_two, block_three],
                    [bye_metadata, hi_metadata, apple_metadata]) ==
            "apple.txt:3:hi\nbye.txt:5:hi when do you\nbye.txt:103:hi\nbye.txt:143:the word hi is\nbye.txt:146:Hihiiii\nhi.txt:1:hiiiii\nhi.txt:2:hi")


def test_grep_c_one_file():
    hi_1 = Grep_Par_Output(["5"], 2)
    hi_0 = Grep_Par_Output(["3"], 1)
    hi_3 = Grep_Par_Output(["0"], 3)
    hi_4 = Grep_Par_Output(["500"], 3)
    assert (grep_c([hi_0, hi_1, hi_3]) == "8")
    assert (grep_c([hi_3]) == "0")
    assert (grep_c([hi_3, hi_4, hi_1]) == "505")
    assert (grep_c([hi_3, hi_4, hi_0]) == "503")


def test_grep_c_two_plus_files():
    bye_0 = Grep_Par_Output(["hi.txt:3", "bye.txt:4", "total:7"], 1)
    hi_1_d = Grep_Par_Output(
        ["hi.txt:2", "bye.txt:10", "total:12"], 2)
    hi_0_d = Grep_Par_Output(
        ["hi.txt:60", "bye.txt:400", "apples.txt:10", "total:470"], 3)
    assert (grep_c([bye_0, hi_1_d, hi_0_d]) ==
            "hi.txt:65\nbye.txt:414\napples.txt:10\ntotal:489")

    block_1 = Grep_Par_Output(
        ["hi.txt:3", "bye.txt:4", "apples.txt:100", "pears.txt: 200", "total:307"], 1)
    block_2 = Grep_Par_Output(
        ["bye.txt:20", "hi.txt:0", "pears.txt:0", "apple.txt:10", "total:30"], 2)
    print(grep_c([block_1, block_2]))
    assert (grep_c([block_1, block_2]) ==
            "hi.txt:3\nbye.txt:24\napples.txt:100\npears.txt:200\napple.txt:10\ntotal:337")
