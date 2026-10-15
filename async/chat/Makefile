# Build and demo the verified chat server with the CakeML release compiler
# (as runnable/Makefile does for echo).
#   1. Holmake      (exports chat_server.sexp from asyncChatMainScript.sml)
#   2. make         (cake --sexp=true --target=arm8; link the FFI)
#   3. make demo    (writes chat-demo-transcript.txt)
CAKE_DIR ?= $(HOME)/.cache/cakeml-release/v3479/arm8/cake-arm8-64
CAKE = $(CAKE_DIR)/cake
TARGET ?= arm8
BUILD = build

all: $(BUILD)/chat_server

$(BUILD)/chat_server.S: chat_server.sexp
	mkdir -p $(BUILD)
	$(CAKE) --sexp=true --target=$(TARGET) < $< > $@

# the release's basis_ffi.c, unmodified; the trusted socket FFI of runnable/
$(BUILD)/chat_server: $(BUILD)/chat_server.S ../runnable/socket_ffi.c
	$(CC) -O2 -o $@ $< $(CAKE_DIR)/basis_ffi.c ../runnable/socket_ffi.c -lm

demo: $(BUILD)/chat_server
	python3 chat_demo.py --server $(BUILD)/chat_server > chat-demo-transcript.txt 2>&1; cat chat-demo-transcript.txt

clean:
	rm -rf $(BUILD)
