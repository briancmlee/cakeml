#!/bin/sh
# Demo of the verified HTTP server (not trusted: it only drives the server).
# HttpSpec's request subset is exactly "GET <path> HTTP/1.0\r\n\r\n", so curl's
# default headers are removed with -H 'Name:' (curl then sends exactly that).
SERVER=${1:-build/http_server}
PORT=${PORT:-7830}
CURL="curl -s -m 3 --http1.0 -H Host: -H User-Agent: -H Accept: -i"
CAKE_ECHO_PORT=$PORT $SERVER 2>/dev/null </dev/null &
PID=$!
sleep 0.5
step() { echo; printf '$ %s\n' "$*"; }

step $CURL http://127.0.0.1:$PORT/
$CURL http://127.0.0.1:$PORT/

step $CURL http://127.0.0.1:$PORT/index.html
$CURL http://127.0.0.1:$PORT/index.html

step $CURL http://127.0.0.1:$PORT/no-such-file
$CURL http://127.0.0.1:$PORT/no-such-file

step "three concurrent curls (/, /about, /index.html), outputs in order of completion"
PIDS=""
for p in / /about /index.html; do
  ( out=$($CURL http://127.0.0.1:$PORT$p | head -1); echo "  $p -> $out" ) &
  PIDS="$PIDS $!"
done
wait $PIDS

step "printf 'GET /about HTTP/1.0\\r\\n\\r\\nGET / HTTP/1.0\\r\\n\\r\\n' | nc -w 1 127.0.0.1 $PORT    # two pipelined requests"
printf 'GET /about HTTP/1.0\r\n\r\nGET / HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT

step "printf 'GET / HTTP/1.0\\r\\nHost: x\\r\\n\\r\\n' | nc -w 1 127.0.0.1 $PORT    # a header: outside HttpSpec's subset"
printf 'GET / HTTP/1.0\r\nHost: x\r\n\r\n' | nc -w 1 127.0.0.1 $PORT
echo "  (no response: the parser reports Invalid and the handler stops, 18-http-model.md §7.3)"

kill $PID
