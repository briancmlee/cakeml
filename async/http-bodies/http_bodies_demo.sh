#!/bin/sh
# Demo of the verified HTTP server with request bodies (spec/HttpSpecBodies),
# with plain curl.  Not trusted: it only drives the server.
SERVER=${1:-build/http_server_b}
PORT=${PORT:-7850}
CAKE_ECHO_PORT=$PORT $SERVER 2>/dev/null </dev/null &
PID=$!
# wait until the server accepts connections
for i in $(seq 1 50); do nc -z 127.0.0.1 $PORT 2>/dev/null && break; sleep 0.1; done
step() { echo; printf '$ %s\n' "$*"; }

step curl -s -i http://127.0.0.1:$PORT/
curl -s -m 3 -i http://127.0.0.1:$PORT/

step curl -s -i -d hello http://127.0.0.1:$PORT/echo
curl -s -m 3 -i -d hello http://127.0.0.1:$PORT/echo

step "curl -s -i --data-binary @- http://127.0.0.1:$PORT/echo   # a body that looks like a request"
printf 'GET /a HTTP/1.0\r\n\r\n' | curl -s -m 3 -i --data-binary @- http://127.0.0.1:$PORT/echo

step "head -c 20000 /dev/zero | tr '\\0' x | curl -s --data-binary @- http://127.0.0.1:$PORT/echo | wc -c   # a 20 kB body, many reads"
head -c 20000 /dev/zero | tr '\0' x | curl -s -m 5 --data-binary @- http://127.0.0.1:$PORT/echo | wc -c

UA="Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/129.0.0.0 Safari/537.36 Edg/129.0.0.0 ExtraLongToken"
step "time curl -s -i -A '<${#UA}-character User-Agent>' -d hello http://127.0.0.1:$PORT/echo   # long header value (linear-time parsing)"
START=$(python3 -c 'import time; print(time.time())')
curl -s -m 5 -i -A "$UA" -d hello http://127.0.0.1:$PORT/echo
END=$(python3 -c 'import time; print(time.time())')
python3 -c "print('  (took %.3f s)' % ($END - $START))"

step curl -s -i -d ignored http://127.0.0.1:$PORT/other
curl -s -m 3 -i -d ignored http://127.0.0.1:$PORT/other

step "printf 'POST /echo HTTP/1.1\r\nContent-Length: 3\r\n\r\nabcGET / HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT   # pipelined after a body"
printf 'POST /echo HTTP/1.1\r\nContent-Length: 3\r\n\r\nabcGET / HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT

step "printf 'POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT   # chunked: out of scope"
printf 'POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT
echo "  (no response: Transfer-Encoding makes the request invalid)"

step "printf 'POST /echo HTTP/1.1\r\nContent-Length\t: 19\r\n\r\nGET /a HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT   # tab before the colon"
printf 'POST /echo HTTP/1.1\r\nContent-Length\t: 19\r\n\r\nGET /a HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT
echo "  (no response: a header name must be an RFC 9110 token, so the request is invalid;"
echo "   the 19 body bytes are not answered as a second request)"

kill $PID
