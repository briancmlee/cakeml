#!/bin/sh
# Demo of the verified header-tolerant HTTP server (spec/HttpSpecHeaders),
# with plain curl: no header stripping.  Not trusted: it only drives the server.
SERVER=${1:-build/http_server_h}
PORT=${PORT:-7840}
CAKE_ECHO_PORT=$PORT $SERVER 2>/dev/null </dev/null &
PID=$!
sleep 0.5
step() { echo; printf '$ %s\n' "$*"; }

step curl -s -i http://127.0.0.1:$PORT/
curl -s -m 3 -i http://127.0.0.1:$PORT/

step curl -s -i http://127.0.0.1:$PORT/index.html
curl -s -m 3 -i http://127.0.0.1:$PORT/index.html

step curl -s -i http://127.0.0.1:$PORT/no-such-file
curl -s -m 3 -i http://127.0.0.1:$PORT/no-such-file

step curl -s -i -H "X-Custom: anything at all" -A "MyAgent/1.0" http://127.0.0.1:$PORT/about
curl -s -m 3 -i -H "X-Custom: anything at all" -A "MyAgent/1.0" http://127.0.0.1:$PORT/about

step curl -s --http1.0 -i http://127.0.0.1:$PORT/    "# HTTP/1.0 with headers"
curl -s -m 3 --http1.0 -i http://127.0.0.1:$PORT/

step "three concurrent curls (/, /about, /index.html), in order of completion"
PIDS=""
for p in / /about /index.html; do
  ( out=$(curl -s -m 3 -i http://127.0.0.1:$PORT$p | head -1); echo "  $p -> $out" ) &
  PIDS="$PIDS $!"
done
wait $PIDS

step "printf 'GET /about HTTP/1.1\r\nHost: x\r\n\r\nGET / HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT    # pipelined, with and without headers"
printf 'GET /about HTTP/1.1\r\nHost: x\r\n\r\nGET / HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT

step "printf 'GET / HTTP/1.1\r\nno colon here\r\n\r\n' | nc -w 1 127.0.0.1 $PORT    # malformed header line"
printf 'GET / HTTP/1.1\r\nno colon here\r\n\r\n' | nc -w 1 127.0.0.1 $PORT
echo "  (no response: the parser reports HInvalid and the handler stops)"

step "printf 'GET / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello' | nc -w 1 127.0.0.1 $PORT    # a body-framing header"
printf 'GET / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello' | nc -w 1 127.0.0.1 $PORT
echo "  (no response: the subset has no request bodies, so Content-Length and"
echo "   Transfer-Encoding make a request invalid; the handler stops)"

kill $PID
