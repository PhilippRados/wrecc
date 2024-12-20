.PHONY: unit-tests snapshot-tests fuzzer

help:  ## Display this help
	@awk 'BEGIN {FS = ":.*##"; printf "Usage:\n  make \033[36m<target>\033[0m\n"} /^[a-zA-Z_-]+:.*?##/ { printf "  \033[36m%-15s\033[0m %s\n", $$1, $$2 } /^##@/ { printf "\n\033[1m%s\033[0m\n", substr($$0, 5) } ' $(MAKEFILE_LIST)

unit-tests: ## Run rust unit-tests
	cargo t --workspace

snapshot-tests: ## Run snaphot-tests located in tests/
	bash tests/snapshot_tests.sh

fuzzer: ## Launch cargo-afl fuzzer
	cd fuzzer && \
	cargo afl build && \
	cargo afl fuzz -i inputs -o outputs target/debug/fuzz_target
