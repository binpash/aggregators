

script_file=$1
input_file=$2 
output_file=$3
time_file=$4
ID=$5
benchmark=$6
all_res_file=$7

export SUITE_DIR=$(realpath $(dirname $benchmark))
export TIMEFORMAT=%R
cd $SUITE_DIR

# Set which aggregators we are using. 
if [[ "$@" == *"--all"* ]]; then
    agg_set=all
elif [[ "$@" == *"--lean"* ]]; then
    agg_set=lean
else
    agg_set=python
fi

# Set if we need input inflation between stages. 
if [[ "$@" == *"--inf"* && "$input_file" == *".txt" ]]; then
    set_inf=1
else
    set_inf=0
fi

# Run aggregator with configurations. 
if [[ "$input_file" == *"all_cmds"* && $set_inf == 1 ]]; then
    { time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file; } 2>"$time_file" 
elif [[ $set_inf == 1 ]]; then
    { time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file -inflate; } 2>"$time_file" 
else 
    { time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file; } 2>"$time_file" 
fi

echo "$input_file $script_file $(cat "$time_file")" | tee -a $all_res_file

