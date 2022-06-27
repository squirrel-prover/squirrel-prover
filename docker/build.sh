#!/usr/bin/env bash
# call in top-level dir
DOCKER_BUILDKIT=1 docker build -t sp/squirrel-prover -f docker/Dockerfile .
