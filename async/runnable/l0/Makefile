# The honest L0 socket FFI (trusted): build the shared library the tester
# loads.  The programs linking it come with L1 (design/36 §8).
CC ?= cc
BUILD = build

all: $(BUILD)/libsocket_ffi_l0.dylib

$(BUILD)/libsocket_ffi_l0.dylib: socket_ffi_l0.c
	mkdir -p $(BUILD)
	$(CC) -Wall -Wextra -O2 -shared -fPIC -o $@ $<

PLATFORM ?= $(shell uname -s | tr A-Z a-z)

# Conformance tests (design/36 §4.3): every run must be a behaviour of the
# L0 world (async/honest-l0).  On a new platform, run this first.
probes: all
	python3 -I tester/probes.py --lib $(BUILD)/libsocket_ffi_l0.dylib --out tester/probes-$(PLATFORM).txt

conformance: probes
	python3 -I tester/mutants.py tester/probes-$(PLATFORM).json
	python3 -I tester/random_test.py --lib $(BUILD)/libsocket_ffi_l0.dylib --seeds 100 --steps 200

clean:
	rm -rf $(BUILD)
