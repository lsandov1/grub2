#!/bin/bash

set -eu
set -o pipefail
set -x

cd $CI_PROJECT_DIR
./bootstrap
./configure
make
make check
