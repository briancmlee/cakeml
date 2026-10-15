# Build and demo the verified header-tolerant HTTP server with the CakeML release compiler
# (as ../echo/Makefile does for echo).
#   1. Holmake in ../../programs/http-h (exports http_server_h.sexp from
#      asyncHttpMainHScript.sml; a copy is committed)
#   2. make         (cake --sexp=true --target=arm8; link the FFI)
#   3. make demo    (writes http-headers-demo-transcript.txt)
CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build

all: $(BUILD)/http_server_h

$(BUILD)/http_server_h.S: ../../programs/http-h/http_server_h.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

# the release's basis_ffi.c, unmodified; the trusted socket FFI of runnable/
$(BUILD)/http_server_h: $(BUILD)/http_server_h.S ../socket_ffi.c
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c ../socket_ffi.c -lm

demo: $(BUILD)/http_server_h
	./http_headers_demo.sh $(BUILD)/http_server_h > http-headers-demo-transcript.txt 2>&1; cat http-headers-demo-transcript.txt

clean:
	rm -rf $(BUILD)
