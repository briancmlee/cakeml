# Build the verified HTTP-bodies server on the select-on-interest loop
# (option C) with the CakeML release compiler.
#   1. Holmake      (exports http_quiet.sexp; a copy is committed)
#   2. make         (compiles it, linking the trusted socket FFI)
#   3. make demo    (the bodies demo of ../http-bodies against it)
#   4. make cpu     (CPU usage: idle, after an invalid request, idle again)
CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build
FFI = ../socket_ffi.c

all: $(BUILD)/http_quiet

$(BUILD)/http_quiet.S: http_quiet.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/http_quiet: $(BUILD)/http_quiet.S $(FFI)
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

demo: $(BUILD)/http_quiet
	PORT=7870 sh ../http-bodies/http_bodies_demo.sh $(BUILD)/http_quiet > demo-transcript.txt 2>&1; cat demo-transcript.txt

clean:
	rm -rf $(BUILD)

$(BUILD)/spin: ../echo-blocking/spin.c
	mkdir -p $(BUILD)
	$(CC) -O2 -o $@ $<

../http-bodies/build/http_server_pb:
	$(MAKE) -C ../http-bodies

cpu: $(BUILD)/http_quiet $(BUILD)/spin ../http-bodies/build/http_server_pb
	python3 http_cpu_bench.py --out cpu-results.txt --calibrate $(BUILD)/spin \
	  $(BUILD)/http_quiet ../http-bodies/build/http_server_pb
