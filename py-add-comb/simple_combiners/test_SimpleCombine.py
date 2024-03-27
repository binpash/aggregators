import pytest

from simple_combiners.simple_combine import sort_combine, grep_combine, wc_combine


def test_wc_combine():
    '''
    Test wc_combine with:
        1) different number of paralleled ouputs
        2) no file name if the output were directed to stdout
        3) error input
        4) from same file and from different files
    '''
    assert wc_combine(["4 3 20 hi.txt", "3 2 10 hi.txt",
                       "3 5 100 hi.txt"]) == "10 10 130 hi.txt"
    assert wc_combine(["0 0 0 ", "0 0 0 "]) == "0 0 0 "
    assert wc_combine(["30 54 10000 ", "0 0 0 "]) == "30 54 10000 "
    assert wc_combine(["30 54 10000 bye.txt"]) == "30 54 10000 bye.txt"
    assert wc_combine([]) == ""
    with pytest.raises(ValueError):
        wc_combine([""])
    with pytest.raises(ValueError):
        wc_combine(["hi", []])
    with pytest.raises(ValueError):
        wc_combine("hi")
    assert wc_combine(["30 54 10000 hi.txt", "10 6 1002 bye.txt"]
                      ) == "30 54 10000 hi.txt\n10 6 1002 bye.txt\n40 60 11002 total"
    assert wc_combine(["30 54 10000 hi.txt", "10 6 1002 bye.txt", "20 400 1001 hi.txt"]
                      ) == "50 454 11001 hi.txt\n10 6 1002 bye.txt\n60 460 12003 total"
    assert wc_combine(["10 500 1000 bye.txt", "100 100 10000 ", "30 950 8030 ", "20 400 1000 hi.txt", "20 400 1000 bye.txt", "10 6 1002 "]
                      ) == "30 900 2000 bye.txt\n140 1056 19032 \n20 400 1000 hi.txt\n190 2356 22032 total"
    assert wc_combine(["10 500 1000 bye.txt", "100 100 10000 ", "30 950 8030 hi2.txt", "20 400 1000 hi.txt", "20 400 1000 bye2.txt"]
                      ) == "10 500 1000 bye.txt\n100 100 10000 \n30 950 8030 hi2.txt\n20 400 1000 hi.txt\n20 400 1000 bye2.txt\n180 2350 21030 total"
    assert wc_combine(["30 54 10000 hi.txt", "0 0 0 bye.txt", "10 6 1002 bye.txt"]
                      ) == "30 54 10000 hi.txt\n10 6 1002 bye.txt\n40 60 11002 total"


def test_grep_combine():
    '''
    Test grep_combine with: 
        1) Test multiple lines 
        2) Test nothing found 
    '''
    assert grep_combine([]) == ""
    assert grep_combine(["hi this is\nhi\nhi 3 4 2 bye then\nwhen\nthe\nhi",
                         "hi this is\nhi\nhi 3 4 2 bye then"]) == "hi this is\nhi\nhi 3 4 2 bye then\nwhen\nthe\nhi\nhi this is\nhi\nhi 3 4 2 bye then"
    assert grep_combine(["", "hi this is\nthere hi\n hi how are you"]
                        ) == "hi this is\nthere hi\n hi how are you"
    assert grep_combine(["apples are green\nthere are green apples", "selling apples", "", "apples appl appl"]
                        ) == "apples are green\nthere are green apples\nselling apples\napples appl appl"
    assert grep_combine(["", "", "", "", ""]
                        ) == ""
    assert grep_combine(["hi today is monday"]) == "hi today is monday"


def test_sort_combine():
    '''
    Test sort_combine with: 
        1) Test with mix of single letters / number -- include repeated
        2) Test longer phrases
        3) isSmToBig and !isSmToBig
        4) empty ""
    '''
    assert sort_combine([], False) == ""
    assert sort_combine(
        ["a\nz\nw\nf\n3\n1", "h\n2\n10\nf\n10\nh\nc", "8\n10\nf\n10\nh\nc"], True) == "1\n10\n10\n10\n10\n2\n3\n8\na\nc\nc\nf\nf\nf\nh\nh\nh\nw\nz"
    assert sort_combine(
        ["a\nz\nw\nf\n3\n1", "h\n2\n10\nf\n10\nh\nc", "8\n10\nf\n10\nh\nc"], False) == "z\nw\nh\nh\nh\nf\nf\nf\nc\nc\na\n8\n3\n2\n10\n10\n10\n10\n1"
    assert sort_combine(["apple\npears\ngrape\nbanana",
                         "3001\n22\n100\n1003"], True) == "100\n1003\n22\n3001\napple\nbanana\ngrape\npears"
    assert sort_combine(["3001\n22\n100\n1003", "apple\npears\ngrape\nbanana"],
                        False) == "pears\ngrape\nbanana\napple\n3001\n22\n1003\n100"
    assert sort_combine(["3001\n22\n100\n1003", ""],
                        False) == "3001\n22\n1003\n100\n"
    assert sort_combine(["-3j4tj\npears\n30\nbanana",
                        "3\n2\ngood morning today is wednesday", "z\na\ne\nhi how are you"], True) == "-3j4tj\n2\n3\n30\na\nbanana\ne\ngood morning today is wednesday\nhi how are you\npears\nz"
    assert sort_combine(["banana is the best fruit",
                        "the best fruit is banana", "what is the best fruit", "the best fruit is not banana"], True) == "banana is the best fruit\nthe best fruit is banana\nthe best fruit is not banana\nwhat is the best fruit"
    assert sort_combine(["banana is the best fruit",
                        "the best fruit is banana", "what is the best fruit", "the best fruit is not banana"], False) == "what is the best fruit\nthe best fruit is not banana\nthe best fruit is banana\nbanana is the best fruit"
    assert sort_combine(["banana is the best fruit",
                        "the   best fruit is banana", " what is the best fruit", "the best fruit is not banana"], False) == "the best fruit is not banana\nthe   best fruit is banana\nbanana is the best fruit\n what is the best fruit"
    assert sort_combine(
        ["\n hi good morning\nwhat's for dinner", " 3   hi good morning\nbye good night \nzebra", " 100 2000"], True) == "\n 100 2000\n 3   hi good morning\n hi good morning\nbye good night \nwhat's for dinner\nzebra"
