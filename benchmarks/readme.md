## How to Run:

- Ensure `benchmarks` directory is current root directory. If not, use from directory root,

```bash
cd `benchmarks`
```

- Main run script: `./simple_infra/infra_run.py`
- Run `./simple_infra/infra_run.py -h` for flags and options.
- Test and measure aggregator performance with,
  - [Run all available benchmark sets](#run-all-available-benchmark-sets)
  - [From one benchmark set](#run-with-benchmark-set)
  - [One script and input](#run-with-custom-scripts--inputs)
- [Explaination of files generated from run](#files-youll-see-after-running)

### Run all available benchmark sets: 
First, download all inputs.  
```bash
./run-all.sh --inputs # Download all input files.
```

Here are the configurations to the scripts. 
* `--small`: use small input 
* `--inf`: input inflation between stages
* `--all`: use lean and python aggregators 
* `--lean`: use lean aggregators (default is python aggregators)

For example, to run all benchmarks with python and lean aggregators with input inflation on smaller input, 
```bash
./run.sh --small --all --inf
```

Cleanup all intermediate files.
```bash
./run-all.sh --clean 
```

### Run with one benchmark set:

Below, we show how to run the `oneliners` benchmark only. First `cd` into the benchmark set and download input:

```bash
cd oneliners
./inputs.sh # Download input files.
```

Example configuration to run suite with.

```bash
./run.sh --small # Run with default python on 1M input without input inflation.
./cleanup.sh # Remove all intermediate files.
```

Other configurations. Ensure to save results and use clean up script before running new configuration.

```bash
./run.sh --small --all # Run with both lean and python aggregators on 1M input without input inflation.
./run.sh --small --all --inf # Run with both lean and python aggregators on 1M input with input inflation.
```

### Run with custom scripts + inputs

Running from one directory ensures all intermediate files are organized. Here, we will create and run from the `run` directory.

```bash
# Use python aggregator without input inflation.
mkdir run
cd run
../simple_infra/infra_run.py -n 2 -i ../oneliners/inputs/1M.txt -s ../oneliners/scripts/sort.sh -id 1 -agg python -o out.txt
```

```bash
# Use lean aggregator with input inflation.
mkdir run
cd run
../simple_infra/infra_run.py -n 2 -i ../oneliners/inputs/1M.txt -s ../oneliners/scripts/sort.sh -inflate -id 1 -agg lean -o out.txt
```

```bash
# Use specified aggregator without input inflation.
mkdir run
cd run
../simple_infra/infra_run.py -n 2 -i ../oneliners/inputs/1M.txt -s ../oneliners/scripts/sort.sh -id 1 -agg ../../py-2/s_sort.py -o out.txt
```

### Files you'll see after running

1. infra_metrics.csv: CSV file with main metric results; Header is as follows: **script,input,input size,adj input size,cmd,agg,agg time,agg correct,cmd seq time**
2. infra_debug.log: more detailed execution log
3. inputs-s-[ID]: org: split files; cmd: files after applying current command instance (parallel partials)
4. outputs-temp: agg-[ID] parallel output files per command instance; seq-check-[ID] sequential output files per command instance (to check aggregator correctness)
5. <output.txt> : output file produced after running entire script with this infrastructure (provided as last argument to ../infra_run.py)

### Pipeline for [Running with Benchmark](#run-with-benchmark-sets)

![alt text](./simple_infra/infra.png)
