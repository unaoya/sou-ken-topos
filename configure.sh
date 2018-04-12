#!/bin/sh
set -eux
coq_makefile -f _CoqProject -o Makefile
