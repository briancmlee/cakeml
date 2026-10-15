# Build the verified BLOCKING echo server, and the two polling builds it is
# compared with, using the CakeML release compiler (as ../runnable).
#
#   1. Holmake      (exports echo_blocking.sexp from asyncEchoBlkExportScript.sml)
#   2. make         (compiles the three servers below)
#   3. make demo    (blocking server, 3 concurrent clients + a late one)
#   4. make cpu     (CPU usage, idle and under light load; cpu-results.txt)
#
# build/echo_blocking        the blocking program (run_b), socket_ffi.c with
#                            -DNO_IDLE_WAIT: sock_poll never waits; the
#                            program sleeps only in sock_select
# build/echo_polling         #23's polling program (run_i), socket_ffi.c as
#                            in #23 (with its unverified idle-wait heuristic)
# build/echo_polling_nowait  the same polling program with -DNO_IDLE_WAIT,
#                            i.e. poll exactly as the model's (no wait)
# build/spin                 calibration: a C busy loop (what "one core fully
#                            busy" measures as here)

CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build
FFI = ../runnable/socket_ffi.c

all: $(BUILD)/echo_blocking $(BUILD)/echo_polling $(BUILD)/echo_polling_nowait $(BUILD)/spin

$(BUILD)/echo_blocking.S: echo_blocking.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/echo_polling.S: ../runnable/echo_server.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/echo_blocking: $(BUILD)/echo_blocking.S $(FFI)
	$(CC) -O2 -DNO_IDLE_WAIT -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/echo_polling: $(BUILD)/echo_polling.S $(FFI)
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/echo_polling_nowait: $(BUILD)/echo_polling.S $(FFI)
	$(CC) -O2 -DNO_IDLE_WAIT -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/spin: spin.c
	mkdir -p $(BUILD)
	$(CC) -O2 -o $@ $<

demo: $(BUILD)/echo_blocking
	python3 ../runnable/demo_clients.py --server $(BUILD)/echo_blocking --log demo-transcript.txt

cpu: all
	python3 cpu_bench.py --out cpu-results.txt --calibrate $(BUILD)/spin \
	  $(BUILD)/echo_blocking $(BUILD)/echo_polling $(BUILD)/echo_polling_nowait

clean:
	rm -rf $(BUILD)
