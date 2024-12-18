#!/bin/bash

docker build -t agg .
docker run -dit agg
timestamp=$(date +"%Y-%m-%d %H:%M:%S")
echo "[$timestamp] Container started."
