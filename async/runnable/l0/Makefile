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

# D20: a real CakeML byte array passes sys_poll's alignment check (the
# pollfd entries at offset 16).  CAKE_DIR: a CakeML release (cake, basis_ffi.c).
CAKE_DIR ?= $(HOME)/toolchains/cakeml-release/v3479/x64/cake-x64-64
align: socket_ffi_l0.c tester/align/align.cml
	$(CAKE_DIR)/cake < tester/align/align.cml > $(BUILD)/align.S
	$(CC) -O2 $(BUILD)/align.S $(CAKE_DIR)/basis_ffi.c socket_ffi_l0.c -o $(BUILD)/align -lm
	$(BUILD)/align
