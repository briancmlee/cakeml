# Build the verified BLOCKING echo servers, and the polling build they are
# compared with, using the CakeML release compiler (as ../echo).
#
#   1. Holmake      (exports echo_blocking.sexp and echo_live.sexp; copies
#                    are committed)
#   2. make         (compiles the servers below)
#   3. make demo    (both blocking servers, 3 concurrent clients + a late one)
#   4. make cpu     (CPU usage, idle and under light load; cpu-results.txt)
#
# build/echo_live            the blocking program that selects on the live
#                            connections only (echo_live_spec): it sleeps
#                            only in sock_select
# build/echo_blocking        the first blocking program (run_b), which selects
#                            on the whole interest list (it spins once a
#                            client has disconnected: see design note 24)
# build/echo_polling         the polling headline program (run_i); sock_poll
#                            never waits (as the model's poll), so it
#                            busy-polls when idle
# build/spin                 calibration: a C busy-polling loop
#
# socket_ffi.c is the trusted C (one file, ../socket_ffi.c): it does exactly
# what the model says; sock_poll is a single poll(2) with timeout 0.

CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build
FFI = ../socket_ffi.c

all: $(BUILD)/echo_live $(BUILD)/echo_blocking $(BUILD)/echo_polling $(BUILD)/spin

$(BUILD)/echo_live.S: echo_live.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/echo_blocking.S: echo_blocking.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/echo_polling.S: ../../programs/echo/echo_server.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/echo_live: $(BUILD)/echo_live.S $(FFI)
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/echo_blocking: $(BUILD)/echo_blocking.S $(FFI)
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/echo_polling: $(BUILD)/echo_polling.S $(FFI)
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/spin: spin.c
	mkdir -p $(BUILD)
	$(CC) -O2 -o $@ $<

demo: $(BUILD)/echo_blocking $(BUILD)/echo_live
	python3 ../echo/demo_clients.py --server $(BUILD)/echo_blocking --log demo-transcript.txt
	python3 ../echo/demo_clients.py --server $(BUILD)/echo_live --port 7778 --log demo-transcript-live.txt

cpu: all
	python3 cpu_bench.py --out cpu-results.txt --calibrate $(BUILD)/spin \
	  $(BUILD)/echo_live $(BUILD)/echo_blocking $(BUILD)/echo_polling

clean:
	rm -rf $(BUILD)
