FROM ubuntu:22.04

RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    zlib1g-dev \
    python3 \
    python3-pip \
    python3-dev \
    libarchive-dev \
    clang \
    && rm -rf /var/lib/apt/lists/*

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

ENV LIBRARY_PATH=/usr/lib/x86_64-linux-gnu

WORKDIR /workspace

CMD ["sh", "-c", "\
    echo 'Installing Lean toolchain...' && \
    elan toolchain install $(cat lean-toolchain) && \
    echo 'Building KLR project...' && \
    lake build && \
    echo 'Creating output directory...' && \
    mkdir -p bin_linux && \
    echo 'Copying klr binary to host...' && \
    cp .lake/build/bin/klr klr_linux && \
    echo 'Build complete! Binary available at ./klr_linux' \
"]
