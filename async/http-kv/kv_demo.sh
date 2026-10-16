#!/bin/sh
# Demo of the verified key-value server (spec/HttpKvSpec), with plain curl.
# Not trusted: it only drives the server.  Keys are paths; the store starts
# empty; GET answers 200 with the value or 404; POST stores its body and
# answers 200 with an empty body.  All connections share one store.
SERVER=${1:-build/kv_server}
PORT=${PORT:-7860}
CAKE_ECHO_PORT=$PORT $SERVER 2>/dev/null </dev/null &
PID=$!
# wait until the server accepts connections
for i in $(seq 1 50); do nc -z 127.0.0.1 $PORT 2>/dev/null && break; sleep 0.1; done
step() { echo; printf '$ %s\n' "$*"; }
URL=http://127.0.0.1:$PORT

step curl -s -i $URL/greeting "   # the store starts empty"
curl -s -m 3 -i $URL/greeting

step curl -s -i -d hello $URL/greeting "   # client 1 stores a value"
curl -s -m 3 -i -d hello $URL/greeting

step curl -s -i $URL/greeting "   # client 2, on another connection, reads it"
curl -s -m 3 -i $URL/greeting

step curl -s -i -d bonjour $URL/greeting "   # overwrite"
curl -s -m 3 -i -d bonjour $URL/greeting
curl -s -m 3 -i $URL/greeting

step "two concurrent clients, each POSTs its own key; then a third reads both"
( curl -s -m 3 -o /dev/null -w '  client A: POST /a -> %{http_code}\n' -d from-A $URL/a ) &
A=$!
( curl -s -m 3 -o /dev/null -w '  client B: POST /b -> %{http_code}\n' -d from-B $URL/b ) &
B=$!
wait $A $B
printf '  client C: GET /a -> %s\n' "$(curl -s -m 3 $URL/a)"
printf '  client C: GET /b -> %s\n' "$(curl -s -m 3 $URL/b)"

step "a slow client holds a half-sent request open while another client is served"
( printf 'GET /a HTTP/1.0\r\n'; sleep 1; printf '\r\n' ) | nc -w 2 127.0.0.1 $PORT > slow.out &
S=$!
sleep 0.2
printf '  fast client: GET /b -> %s   (answered while the slow request is pending)\n' "$(curl -s -m 3 $URL/b)"
wait $S
printf '  slow client: %s\n' "$(head -1 slow.out)"
rm -f slow.out

step "printf 'POST /k HTTP/1.1\r\nContent-Length: 2\r\n\r\nv1GET /k HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT   # pipelined: write then read"
printf 'POST /k HTTP/1.1\r\nContent-Length: 2\r\n\r\nv1GET /k HTTP/1.0\r\n\r\n' | nc -w 1 127.0.0.1 $PORT
echo

UA="Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/129.0.0.0 Safari/537.36 Edg/129.0.0.0 ExtraLongToken"
step "time curl -s -i -A '<${#UA}-character User-Agent>' $URL/greeting   # long header value (linear-time parsing)"
START=$(python3 -c 'import time; print(time.time())')
curl -s -m 5 -i -A "$UA" $URL/greeting
echo
END=$(python3 -c 'import time; print(time.time())')
python3 -c "print('  (took %.3f s)' % ($END - $START))"

step curl -s -i -X DELETE $URL/greeting "   # only GET and POST"
curl -s -m 2 -i -X DELETE $URL/greeting
echo "  (no response: HttpKvSpec has only GET and POST)"

kill $PID
