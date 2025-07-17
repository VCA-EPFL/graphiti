.PHONY: help
help:
	@echo "make setup: setup build and runtime dependencies."
	@echo "make build: build the proof."
	@echo "make build-exe: build the executable."

.PHONY: setup
setup:
	cargo install --git https://github.com/VCA-EPFL/OracleGraphiti --locked
	lake exe cache --repo=leanprover-community/mathlib4-nightly-testing get

.PHONY: build
build:
	lake build

.PHONY: build-exe
build-exe:
	lake build graphiti
