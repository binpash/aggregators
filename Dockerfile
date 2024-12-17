# Use the official Ubuntu base image
FROM ubuntu:latest

# Update and install basic packages
RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    git \
    wget \
    dos2unix \ 
    bsdextrautils \
    locales-all \ 
    software-properties-common \
    sudo \ 
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

# Install Lean
RUN wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && \
    bash install_debian.sh ; rm -f install_debian.sh && \
    source ~/.profile 

# Set the working directory in the container
WORKDIR /home/aggregators

ADD . /home/aggregators

# The command the container will run by default
SHELL ["/bin/bash", "-c"]

CMD ["/bin/bash"]
ENTRYPOINT [ "" ]
