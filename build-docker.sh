#!/bin/bash -i
shopt -s expand_aliases # some people alias their podman to docker

echo "Building KLR Docker image..."
docker build -t klr-builder .

echo "Running build container..."
docker run --rm --cpus=8 -v "$(pwd):/workspace" klr-builder

echo "Build complete!"
if [ -f "./klr_linux" ]; then
    echo "KLR binary is available at: ./klr_linux"
    ls -la ./klr_linux
else
    echo "Error: Binary not found at ./klr_linux"
    exit 1
fi
