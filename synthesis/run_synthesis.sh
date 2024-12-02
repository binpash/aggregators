#!/bin/bash

# Exit immediately if a command exits with a non-zero status
set -e

# Measure the start time (with nanoseconds)
start_time=$(date +%s.%N)

# Ensure annotations.json exists
if [ ! -f "annotations.json" ]; then
  echo "Error: annotations.json not found!"
  exit 1
fi

# Run the Python synthesizer
echo "Running synthesizer..."
python3 synthesizer.py annotations.json

cd ../lean4/

# Ensure the generated Lean file exists
if [ ! -f "Main.lean" ]; then
  echo "Error: Lean file not generated!"
  exit 1
fi

# Run lake build
echo "Building Lean project with lake..."
lake build Main

# Measure the end time (with nanoseconds)
end_time=$(date +%s.%N)

# Calculate the total time (in seconds, with fractional precision)
execution_time=$(echo "$end_time - $start_time" | bc)

# Success message with execution time
echo "Synthesizer and build completed successfully!"
echo "Total execution time: ${execution_time} seconds"
