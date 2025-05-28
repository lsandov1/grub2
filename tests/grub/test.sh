#!/bin/bash

set -eu
set -o pipefail

cd $CI_PROJECT_DIR
./bootstrap
./configure
make
make check
