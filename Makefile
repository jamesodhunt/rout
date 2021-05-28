# Copyright (c) 2021 James O. D. Hunt.
#
# SPDX-License-Identifier: Apache-2.0
#

ifneq ($(DEBUG),)
    CARGO_TEST_ARGS = -vv -- --nocapture
    # XXX: Note: don't quote the value, or it won't work!
    export RUSTFLAGS=-D warnings
endif

default: build check

build:
	cargo build

check: test

test: unit-test test-coverage

test-coverage:
	cargo tarpaulin -v

unit-test:
	cargo test $(CARGO_TEST_ARGS)

clean:
	cargo clean
	rm -f tarpaulin-report.html

.PHONY: check
.PHONY: clean
.PHONY: default
.PHONY: test
.PHONY: test-coverage
.PHONY: unit-test
