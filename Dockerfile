# Use the official Ubuntu base image
FROM ubuntu:latest

ENV DEBIAN_FRONTEND=noninteractive

# Update and install basic packages
RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    git \
    wget \
    dos2unix \ 
    bsdextrautils \
    locales-all \ 
    sudo \ 
    bash \ 
    software-properties-common \
    && rm -rf /var/lib/apt/lists/*

# Add deadsnakes PPA and install Python 3.10
RUN add-apt-repository ppa:deadsnakes/ppa && \
    apt-get update && \
    apt-get install -y python3.10 python3.10-venv && \
    rm -rf /var/lib/apt/lists/*

# Set Python 3.10 as the default python3
RUN update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.10 1

# Install pip for Python 3.10
RUN python3 -m ensurepip --upgrade

# Verify Python and pip versions
RUN python3 --version && pip3 --version

# Set the working directory in the container
ADD . /home/aggregators
WORKDIR /home/aggregators
RUN pwd

# The command the container will run by default
SHELL ["/bin/bash", "-c"]

ENTRYPOINT ["./linux-build.sh"]

