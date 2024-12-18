#!/bin/bash

docker build -t agg -f docker/Dockerfile .
docker run -it agg
timestamp=$(date +"%Y-%m-%d %H:%M:%S")
echo "[$timestamp] Container started."
