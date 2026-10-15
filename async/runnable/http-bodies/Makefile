# Build and demo the verified bodies HTTP server with the CakeML release compiler
# (as ../echo/Makefile does for echo).
#   1. Holmake in ../../programs/http-b (exports http_server_b.sexp from
#      asyncHttpMainBScript.sml; a copy is committed)
#   2. make         (cake --sexp=true --target=arm8; link the FFI)
#   3. make demo    (writes http-bodies-demo-transcript.txt)
CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build

all: $(BUILD)/http_server_b

$(BUILD)/http_server_b.S: ../../programs/http-b/http_server_b.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

# the release's basis_ffi.c, unmodified; the trusted socket FFI (../socket_ffi.c)
$(BUILD)/http_server_b: $(BUILD)/http_server_b.S ../socket_ffi.c
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c ../socket_ffi.c -lm

demo: $(BUILD)/http_server_b
	sh ./http_bodies_demo.sh $(BUILD)/http_server_b > http-bodies-demo-transcript.txt 2>&1; cat http-bodies-demo-transcript.txt

clean:
	rm -rf $(BUILD)
