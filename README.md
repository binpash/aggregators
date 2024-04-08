# Aggregators

Currently aggregators are WIP. The new ones are in `cpp/bin`. They are automatically built during `setup_pash.sh` and the unit tests in `cpp/tests` are run during `run_tests.sh`. The interface is like the following:

```sh
aggregator inputFile1 inputFile2 args
```

Where `args` are the arguments that were passed to the command that produced the input files. The aggregator outputs to `stdout`.

## Adding new aggregators

Let's assume that the aggregator being implemented is for a command called `cmd`.

1. Create a folder named `cmd` inside `cpp/aggregators`

2. For each `OS` supported by PaSh:

   2.1 Create a file named `OS-agg.h` inside that folder

   2.2. Implement the aggregator inside that file using the instructions provided in `cpp/common/main.h` or use a different aggregator as an example. Remember about the include guard.

   2.3 You may create additional files in the aggregator directory. This can be used to share code between aggregator implementations for different `OS`es. When `#include`ing, assume that the aggregator directory is in the include path.

3. Add unit tests for the created aggregator in `cpp/tests/test-OS.sh` for each `OS`. Consult the instructions in that file. Remember to test all options and flags of the aggregator.

Note: after completing these steps the aggregator will automatically be built by the `Makefile` with no changes to it required.

# Aggregators in ./py-2

## Overview

- After running Linux terminal commands on file inputs using parallelization with PaSh, we must find a way to combine those parallel outputs correctly so the parallel execution of command produced matches the sequential execution
- The format of the response is important as to

## Running Aggregators

- Currently, the aggregator scripts written in Python must run in a conda environment (included when running tests)

## Single File Argument Aggregators

### Overview

- Aggregates parallel results when commands are applied to single file input.
- Single input to a command looks like: `wc hi.txt`
- To use an aggregator, please

| File        | Aggregator | Description                                                                                                                                                                   | Notes                                                                                                              |
| ----------- | ---------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| `wc.py`     | `s_wc`     | <li>Combines count results from parallel outputs </li><li>Supports flags `-l, -c, -w, -m`</li>                                                                                | Discripancy with combining byte size (might be due to manually splitting file to create parallel input in testing) |
| `grep.py`   | `s_grep`   | <li> Combines `grep` results from concat. parallel outputs</li>                                                                                                               |
| `grep_c.py` | `s_grep_c` | <li> Combines `grep -c` results from adding found line count</li>                                                                                                             |
| `grep_n.py` | `s_grep_n` | <li> Combines `grep -n` results by first making line corrections and then concat results</li> <li>Requires info on entire file before splitting to for line number correction | Under development, requires info. on                                                                               |

### Testing

- testing scripts produce all relevant files directed to `/outputs` when given files in `/inputs` to produce sequential / parallel results on
- Run `./test-single.sh`:
  1. manually split file into 2 -- put in `/input `
  2. apply command to entire file for sequential output (expected)
  3. apply command to file-1 > output/output-1
     apply command to file-2 > output/output-2
  4. apply aggregators to combine output/output-1 output/output-2 for parallel outpus
  5. eye check that parallel outputs = sequential output
     NOTE: use `s_combine` from the [cmd].py file as aggregators

### Performance

## Multiple File Argument Aggregators

- Commands when ran on single file input vs. multiple file input often produce different results as file name often gets appended to the result
- Multiple inputs to a command looks like: `wc hi.txt bye.txt`

| File    | Aggregator | Description | Sample Input + Output | Performance | Notes |
| ------- | ---------- | ----------- | --------------------- | ----------- | ----- |
| `wc.py` | `m_wc`     |             | ` `                   |

### Testing

- testing scripts produce all relevant files directed to `/outputs` when given files in `/inputs` to produce sequential / parallel results on
- Run `./test-mult.sh`:
  1. manually split files (multiple) into 2 -- put in `/input `
  2. apply command to entire file for sequential output (expected)
  3. apply command to file-1 > output/output-1
     apply command to file-2 > output/output-2
  4. apply aggregators to combine output/output-1 output/output-2 for parallel outpus (requires path of the full files for functions such as line correction in `grep -n`)
  5. eye check that parallel outputs = sequential output
     NOTE: use `m_combine` from the [cmd].py file as aggregators
