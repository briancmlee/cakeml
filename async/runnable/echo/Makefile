# Build the verified echo server with the CakeML release compiler.
#
#   1. Holmake in ../../programs/echo (exports echo_server.sexp from
#      asyncEchoMainScript.sml; a copy is committed)
#   2. make              (compiles it with the release's cake, links the FFI)
#   3. make demo         (runs the server and three concurrent clients)
#
# CAKE_DIR: the extracted release cake-arm8-64 (v3479), with `cake` built in
# it by its own Makefile.  On an M1 Mac the arm8 target runs natively.

CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build

all: $(BUILD)/echo_server

$(BUILD)/echo_server.S: ../../programs/echo/echo_server.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

# basis_ffi.c is the release's, unmodified; socket_ffi.c adds the sockets
$(BUILD)/echo_server: $(BUILD)/echo_server.S ../socket_ffi.c
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c ../socket_ffi.c -lm

demo: $(BUILD)/echo_server
	python3 demo_clients.py --server $(BUILD)/echo_server --log demo-transcript.txt

clean:
	rm -rf $(BUILD)
