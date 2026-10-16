# The honest L0 socket FFI (trusted): build the shared library the tester
# loads.  The programs linking it come with L1 (design/36 §8).
CC ?= cc
BUILD = build

all: $(BUILD)/libsocket_ffi_l0.dylib

$(BUILD)/libsocket_ffi_l0.dylib: socket_ffi_l0.c
	mkdir -p $(BUILD)
	$(CC) -Wall -Wextra -O2 -shared -fPIC -o $@ $<

probes: all
	python3 tester/probes.py --lib $(BUILD)/libsocket_ffi_l0.dylib

clean:
	rm -rf $(BUILD)
