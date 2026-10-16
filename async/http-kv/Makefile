# Build and demo the verified key-value server with the CakeML release compiler
# (as runnable/Makefile does for echo).
#   1. Holmake      (exports kv_server.sexp from asyncKvMainScript.sml)
#   2. make         (cake --sexp=true --target=arm8; link the FFI)
#   3. make demo    (writes kv-demo-transcript.txt)
CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build

all: $(BUILD)/kv_server

$(BUILD)/kv_server.S: kv_server.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

# the release's basis_ffi.c, unmodified; the trusted socket FFI of runnable/
$(BUILD)/kv_server: $(BUILD)/kv_server.S ../runnable/socket_ffi.c
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c ../runnable/socket_ffi.c -lm

demo: $(BUILD)/kv_server
	./kv_demo.sh $(BUILD)/kv_server > kv-demo-transcript.txt 2>&1; cat kv-demo-transcript.txt

clean:
	rm -rf $(BUILD)
