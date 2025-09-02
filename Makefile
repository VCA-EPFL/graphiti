.PHONY: help
help:
	@echo "make setup: setup mathlib 4 cache."
	@echo "make build: build the proof."
	@echo "make build-exe: build the executable.  This requires cargo to be installed."

.PHONY: setup
setup:
	lake exe cache get

.PHONY: build
build:
	lake build

.PHONY: build-exe
build-exe: bin/graphiti_oracle
	lake build graphiti

bin/graphiti_oracle:
	@mkdir -p bin
	cargo install --git https://github.com/VCA-EPFL/OracleGraphiti --locked --root .
