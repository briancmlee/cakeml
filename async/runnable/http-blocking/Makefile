# Build the verified BLOCKING HTTP server (live-fd select loop) and the
# polling HTTP server it is compared with, using the CakeML release
# compiler (as ../echo-blocking).
#
#   1. Holmake      (exports http_live.sexp; a copy is committed)
#   2. make         (compiles the servers below)
#   3. make demo    (the blocking server, with the curl demo of ../http)
#   4. make cpu     (CPU usage: idle, light load, idle again, and after an
#                    invalid request whose client closes; cpu-results.txt)
#
# build/http_live     the blocking HTTP program (http_blk_spec): it sleeps
#                     only in sock_select, on the listener and live fds
# build/http_polling  the polling HTTP program (http_prog_h_spec): sock_poll
#                     never waits (as the model's), so it busy-polls when idle

CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build
FFI = ../socket_ffi.c

all: $(BUILD)/http_live $(BUILD)/http_polling $(BUILD)/spin

$(BUILD)/http_live.S: http_live.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/http_polling.S: ../../programs/http-h/http_server_h.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

$(BUILD)/http_live: $(BUILD)/http_live.S $(FFI)
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/http_polling: $(BUILD)/http_polling.S $(FFI)
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c $(FFI) -lm

$(BUILD)/spin: ../echo-blocking/spin.c
	mkdir -p $(BUILD)
	$(CC) -O2 -o $@ $<

demo: $(BUILD)/http_live
	PORT=7860 sh ../http/http_headers_demo.sh $(BUILD)/http_live > demo-transcript.txt 2>&1; cat demo-transcript.txt

cpu: all
	python3 http_cpu_bench.py --out cpu-results.txt --calibrate $(BUILD)/spin \
	  $(BUILD)/http_live $(BUILD)/http_polling

clean:
	rm -rf $(BUILD)
