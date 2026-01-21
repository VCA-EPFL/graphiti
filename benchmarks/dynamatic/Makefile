export GRAPHITI_REPO := ../..

.PHONY: all
all: gemm-ooo.dot mvt-ooo.dot matvec-ooo.dot gsum_single-ooo.dot gsum_many-ooo.dot

%-ooo.dot: %.dot %.json
	$(GRAPHITI_REPO)/.lake/build/bin/graphiti --output $@ --mids $(shell jq -r '."mux-ids" | join(" ")' $(word 2,$^)) --tag-nums $(shell jq -r '."tags"' $(word 2,$^)) -- $<

.PHONY: clean
clean:
	rm *-ooo.dot
