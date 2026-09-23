#!/bin/sh
# Renders architecture.dot to architecture.svg.  Run from this directory after
# Architecture.lean has told you the .dot changed.
cd "$(dirname "$0")" && dot -Tsvg architecture.dot -o architecture.svg && echo "architecture.svg updated"
