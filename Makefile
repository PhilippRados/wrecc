.PHONY: unit-tests snapshot-tests fuzzer c-testsuite

help:  ## Display this help
	@awk 'BEGIN {FS = ":.*##"; printf "Usage:\n  make \033[36m<target>\033[0m\n"} /^[a-zA-Z_-]+:.*?##/ { printf "  \033[36m%-15s\033[0m %s\n", $$1, $$2 } /^##@/ { printf "\n\033[1m%s\033[0m\n", substr($$0, 5) } ' $(MAKEFILE_LIST)

unit-tests: ## Run rust unit-tests
	cargo t --workspace

snapshot-tests: ## Run snapshot-tests located in tests/
	bash tests/snapshot_tests.sh

c-testsuite: ## Requires c-testsuite (https://github.com/c-testsuite/c-testsuite) and env-var C_TESTSUITE set to its path
	bash tests/c_testsuite.sh

fuzzer: ## Launch afl.rs fuzzer
	cd fuzzer && \
	cargo afl build && \
	cargo afl fuzz -i inputs -o outputs target/debug/fuzz_target
