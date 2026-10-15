# Build and demo the verified HTTP server with the CakeML release compiler
# (as runnable/Makefile does for echo).
#   1. Holmake      (exports http_server.sexp from asyncHttpMainScript.sml)
#   2. make         (cake --sexp=true --target=arm8; link the FFI)
#   3. make demo    (writes http-demo-transcript.txt)
CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build

all: $(BUILD)/http_server

$(BUILD)/http_server.S: http_server.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

# the release's basis_ffi.c, unmodified; the trusted socket FFI of runnable/
$(BUILD)/http_server: $(BUILD)/http_server.S ../runnable/socket_ffi.c
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c ../runnable/socket_ffi.c -lm

demo: $(BUILD)/http_server
	./http_demo.sh $(BUILD)/http_server > http-demo-transcript.txt 2>&1; cat http-demo-transcript.txt

clean:
	rm -rf $(BUILD)
