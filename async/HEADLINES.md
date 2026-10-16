# Layer H: the headlines

Every end-product theorem of the series is stated here in full. The trusted definitions each one mentions are expanded next to it, and each has a plain-English reading and the bites showing that it rejects broken servers. The list of what is trusted is at the end. There are no proofs and no intermediate lemmas. Read this first, to judge the *target*; the rest of the series proves it.

**Levels:**
- **L0, core:** simple sockets, no close.
- **L1, lifetimes:** close and fd reuse.
- **L2, peers:** clients, proxies, backpressure.
- **L3, the real kernel.**

Each level opens with the one theorem that links it to the level above, and a reader can stop after any level.

**Status:**
- ✅ proved in the layer named; every layer of the series builds green with no cheats;
- ⏳ not proved yet (see section 10).

Names are the final ones; `design/NAMES.md` maps them to the spike names.

## Contents

1. [The world every theorem lives in](#1-the-world)
2. [Echo: `echo_prog_spec`](#2-echo) (L0) ✅
3. [HTTP with bodies: `http_prog_spec`](#3-http) (L0) ✅
4. [Quiescence: `echo_blocking_quiet`, `http_blocking_quiet`](#4-quiescence) (L0) ✅
5. [A key-value store: `kv_spec`](#5-kv) (L0): liveness ✅, safety ⏳
6. [Lifetimes: `echo_episodes_prog_spec`](#6-close) (L1) ✅
7. [Peers](#7-peers) (L2): partly ⏳
8. [The real kernel](#8-kernel) (L3) ⏳
9. [What is trusted](#9-trusted)
10. [Not yet proved](#10-pending)
- [Appendix: the chat server](#appendix-chat)

---

<a id="1-the-world"></a>
## 1. The world every theorem lives in

Every headline has the same shape:

> for every fair world `sk` with one listener `lfd`, the CakeML program's
> I/O trace (from CakeML's own semantics, `semantics_prog`) is safe and live.

The world is a pure logical model of sockets (`world/sockets/socketWorld`). The program talks to it only through four FFI calls, plus a fifth, `«sock_select»`, in the quiescence statements.

### The state

```
Datatype:
  arrival = Connect word64 word64      (* Connect l c: connection c is pending on listener l *)
          | Data word64 (word8 list)   (* bytes arrive on connection c *)
          | Eof word64                 (* the peer of c closes its side *)
End

Datatype:
  conn = <| incoming : word8 list      (* arrived, not yet read *)
          ; peer_closed : bool         (* EOF after the incoming bytes *)
          ; outgoing : word8 list      (* everything written so far *)
          |>
End

Datatype:
  sockets = <| listeners : (word64 # word64 list) list   (* listener, its pending connections *)
             ; conns : (word64 # conn) list
             ; sched : arrival list llist                (* the future: one list of arrivals per round *)
             |>
End
```

### Time and readiness

Time is the schedule. A poll first delivers the next round of arrivals, then reports which fds are ready.

```
tick s = case LHD s.sched of
         | NONE => s
         | SOME arrivals => deliver (s with sched := THE (LTL s.sched)) arrivals

is_ready s fd ⇔
    (case ALOOKUP s.listeners fd of SOME q => q ≠ [] | NONE => F) ∨
    (case ALOOKUP s.conns fd of SOME cn => cn.incoming ≠ [] ∨ cn.peer_closed | NONE => F)
```

### The four calls

The model's own versions are below. The FFI wrappers `ffi_sock_*` only encode fds as 8 bytes and statuses as one byte. A call that returns `NONE` (misuse) fails the program.

```
sock_poll fds s   = (FILTER (is_ready (tick s)) fds, tick s)
sock_accept l s   = oldest pending connection on l, or "would block"
sock_read c n s   = SOME (SOME (TAKE n incoming)) | SOME (SOME []) at EOF | SOME NONE (would block)
sock_write c bs s = append bs to c's outgoing log        (writes always succeed in full)
```

### The FFI oracle

The oracle runs these on the world's state. Any other call ends the program with `FFI_failed` (`EchoSpec.socket_oracle`, `socket_ffi`).

### The worlds the servers run in

```
server_world lfd sk ⇔ sk.listeners = [(lfd, [])] ∧ sk.conns = [] ∧ sched_wf sk
```

### Fairness

This is the only assumption on the future (`socketFair`): no arrival is ever silently dropped.

```
sched_wf s ⇔ ∀n. step_ok (ticks n s) (next_step (ticks n s))

step_ok s [] = T
step_ok s (a::as) = (arrival_ok s a ∧ step_ok (deliver1 s a) as)

arrival_ok s (Connect l c) ⇔ is_listener s l ∧ ¬is_listener s c ∧ ¬is_conn s c
arrival_ok s (Data c bs)   ⇔ ∃cn. ALOOKUP s.conns c = SOME cn ∧ ¬cn.peer_closed
arrival_ok s (Eof c)       ⇔ ∃cn. ALOOKUP s.conns c = SOME cn ∧ ¬cn.peer_closed
```

**Plain reading:**
- Clients connect, send bytes, and close, on a schedule we know nothing about.
- Every arrival makes sense: data comes only on known, still-open connections, and new connections get fresh fds.
- The theorems hold for every such schedule, including infinite ones and ones that never stop.

### The trace projections

Every spec below is phrased on these (`EchoSpec`):

```
bytes_read_from c evs  = FLAT (MAP (event_read c) evs)      (* the data «sock_read» on c returned *)
bytes_written_to c evs = FLAT (MAP (event_written c) evs)   (* the data «sock_write» on c sent *)
sent_upto c n sk = the Data bytes for c in the first n rounds of sk.sched
```

`LPREFIX (fromList evs) io` says that `evs` is a finite prefix of the (possibly infinite) trace `io`.

---

<a id="2-echo"></a>
## 2. Echo (L0) ✅

**Theorem** (theory `echoHeadline`; L0, layer final/07):

```
Theorem echo_prog_spec:
  echo_spec 3w echo_prog
```

**The program.** `echo_prog` (`programs/echo/echoMain`):

```
fun main u = run_i ([3], server 3);
```

This is the async event loop running the echo server on listener 3.


**The spec, expanded** (`spec/EchoSpec`):

```
echo_spec lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            echo_safe io ∧ echo_live sk io

echo_safe io ⇔
  ∀evs c. LPREFIX (fromList evs) io ⇒ bytes_written_to c evs ≼ bytes_read_from c evs

echo_live sk io ⇔
  ∀c n. ∃evs. LPREFIX (fromList evs) io ∧ sent_upto c n sk ≼ bytes_written_to c evs
```

**Plain reading.** In every fair world, the program:
- runs forever, without crashing and without an FFI failure;
- at every moment, has written back on each connection a prefix of what it read from that connection;
- eventually echoes every byte every client sent.

There are many clients at once, interleaved arbitrarily.

**Bites** (`spec/EchoSpecBite`): the spec rejects broken servers.
- `broken_swaps_clients`: the server sends client 1's bytes to client 2.
- `broken_drops_a_byte` and `broken_duplicates_a_byte`.
- `broken_writes_before_reading`.
- `broken_never_echoes`: this one violates liveness.
- Non-vacuity: `server_world_exists` (a fair world exists) and `ideal_trace_safe_and_live`.

---

<a id="3-http"></a>
## 3. HTTP with request bodies (L0) ✅

**Theorem** (theory `httpSemantics`; L0, layer final/09):

```
Theorem http_prog_spec:
  http_spec 3w demo_files http_prog
```


**The program.** `http_prog` (`programs/http-pb/httpProg`) is the generic protocol server, instantiated with the bodies parser and responder:

```
fun main u = proto_main b_parse bresp_demo u;
```

**The demo's files.** `demo_files` is three paths: `/`, `/index.html` and `/about`. Each maps to a fixed string.

**The spec, expanded** (`spec/HttpSpec`, with layer 1's tchar and H-CHARS changes):

```
http_spec lfd files prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            http_safe files io ∧ http_live files sk io

http_safe files io ⇔
  ∀evs c rs rest.
    LPREFIX (fromList evs) io ∧ EVERY valid_brequest rs ∧
    bytes_read_from c evs = brequests rs ++ rest ∧ no_full_brequest rest ⇒
    bytes_written_to c evs ≼ bresponses files rs

http_live files sk io ⇔
  ∀c n rs.
    EVERY valid_brequest rs ∧ brequests rs ≼ sent_upto c n sk ⇒
    ∃evs. LPREFIX (fromList evs) io ∧ bresponses files rs ≼ bytes_written_to c evs

no_full_brequest rest ⇔ ∀r. valid_brequest r ⇒ ¬(brequests [r] ≼ rest)
```

**Requests and their validity:**

```
Datatype: brequest = Req string string string ((string # string) list) string
                       (* method, path, version, headers, body *)

valid_brequest (Req m p ver hs b) ⇔
  valid_method m ∧ valid_path p ∧ EVERY uri_char p ∧ valid_version ver ∧
  EVERY valid_bheader hs ∧ ¬EXISTS is_te hs ∧ framed hs b

valid_method m  ⇔ m = "GET" ∨ m = "POST"
valid_path p    ⇔ p ≠ [] ∧ EVERY (λc. c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") p
valid_version v ⇔ v = "1.0" ∨ v = "1.1"
valid_bheader (n, v) ⇔ n ≠ [] ∧ EVERY tchar n ∧ EVERY field_char v
```

**Framing.** The body is framed by Content-Length (matched case-insensitively):

```
framed hs b ⇔ case FILTER is_cl hs of
                [] => b = ""
              | [(n, v)] => v = num_to_dec_string (LENGTH b)
              | _ => F
is_cl (n, v) ⇔ MAP toLower n = "content-length"
is_te (n, v) ⇔ MAP toLower n = "transfer-encoding"
```

**Character sets** (the RFC 9110 and RFC 3986 sets):

```
tchar c      ⇔ isAlpha c ∨ isDigit c ∨ EXISTS (λd. c = d) "!#$%&'*+-._|~" ∨ c = CHR 94 ∨ c = CHR 96
field_char c ⇔ (33 ≤ ORD c ∧ ORD c ≤ 126) ∨ 128 ≤ ORD c ∨ c = #" " ∨ c = #"\t"
uri_char c   ⇔ isAlpha c ∨ isDigit c ∨ EXISTS (λd. c = d) "-._~:/?[]@!$&'()*+,;=%"
```

**Printing:**

```
print_brequest (Req m p ver hs b) =
  m ++ " " ++ p ++ " HTTP/" ++ ver ++ "\r\n" ++ FLAT (MAP print_header hs) ++ "\r\n" ++ b
print_header (n, v) = n ++ ": " ++ v ++ "\r\n"
brequests rs        = bytes (FLAT (MAP print_brequest rs))           (bytes s = MAP (n2w o ORD) s)
bresponses files rs = bytes (FLAT (MAP (print_response o bhandle files) rs))
```

**What the server answers:**

```
bhandle files (Req m p ver hs b) =
  if m = "POST" then (if p = "/echo" then Ok b else NotFound)
  else handle files (Get p)
handle files (Get p) = case ALOOKUP files p of SOME body => Ok body | NONE => NotFound

print_response (Ok body) =
  "HTTP/1.0 200 OK\r\nContent-Length: " ++ num_to_dec_string (LENGTH body) ++ "\r\n\r\n" ++ body
print_response NotFound = "HTTP/1.0 404 Not Found\r\nContent-Length: 0\r\n\r\n"
```

**Plain reading.** In every fair world, the program runs forever. On each connection:
- whenever the bytes read so far are some complete valid requests followed by an incomplete tail, the bytes written are a prefix of the responses to those requests, in order;
- every response to requests a client sent is eventually written.

So the server never answers early, never answers the wrong request, never treats a body as a request, and never stops answering.

**Bites** (`spec/HttpSpecBite`):
- `broken_body_as_request`: answering a request-shaped body as a second request.
- `broken_answers_before_body`.
- `broken_tab_header`: reading `"Content-Length\t:"` as a header and then answering the body.
- `broken_never_answers_b`.
- `rfc_chars_bites`: a tab in a path, or a NUL in a header value, is invalid.
- Uniqueness: `print_brequest_unique` (framing is unique).
- Real clients are covered: `curl_post_request` (curl's `-d hello` request is valid).
- Non-vacuity: `ideal_b_trace_safe_and_live`.

**Agreement with RFC 9112**. This is a checked trust item, `spec-rfc/` (the reference `rfc9112Framing` cites the RFC clause by clause):

```
Theorem rfc_frames_exactly_valid:
  valid_brequest r ⇒
  (rfc_request (print_brequest r ++ rest) m rest' ⇔ m = reading r ∧ rest' = rest)
```

- `rfc_frames_list_exactly_valid` / `rfc_octets_frames_exactly_valid` say the same for lists of requests on the wire.
- `rfc_subset_exact`: our subset is exactly the RFC messages with:
  - method GET or POST;
  - version 1.0 or 1.1;
  - a space right after every field colon;
  - a canonical Content-Length value.

**Stricter than the RFC, on purpose:** the space after each colon, a canonical Content-Length, no Transfer-Encoding, and only GET or POST. See the examples `host_no_space_rfc` and `host_no_space_not_ours`.

**Known limitation.** `Expect: 100-continue` is not supported. Safety forbids interim 1xx responses, so curl waits about 1 s before sending a large body.

---

<a id="4-quiescence"></a>
## 4. Quiescence: no busy-waiting, CPU included (L0) ✅

EchoSpec and HttpSpec say nothing about CPU: a server that busy-polls meets them. QuietSpec adds a blocking `«sock_select»` and requires the program to go to sleep when the world goes quiet.

### The select call and the world with select (`spec/QuietSpec`)

```
sel_wait fds s =
  if ∃n. EXISTS (is_ready (ticks (SUC n) s)) fds
  then SOME (LEAST n. EXISTS (is_ready (ticks (SUC n) s)) fds)
  else NONE                                         (* nothing will ever be ready: block forever *)

sel_ok s fds ⇔ EVERY (λfd. is_listener s fd ∨ is_conn s fd) fds

ffi_select conf bytes s =
  if bytes = [] ∧ sel_ok s (bytes_fds conf) then
    case sel_wait (bytes_fds conf) s of
    | NONE => SOME FFIdiverge
    | SOME k => SOME (FFIreturn [] (ticks k s))
  else NONE                                         (* selecting on a non-socket fails *)
```

`select_ffi sk` is `socket_ffi sk` with `«sock_select» ↦ ffi_select`. A select that blocks forever ends the program with CakeML's `FFI_diverged`.

### Quiet worlds and sleeping programs

```
arrivals_finite sk ⇔ ∃N. ∀m. N ≤ m ⇒ arrivals_upto m sk.sched = arrivals_upto N sk.sched

asleep b io ⇔ ∃conf. b = Terminate (FFI_outcome (Final_event (ExtCall «sock_select») conf [] FFI_diverged)) io
```

### The statements

```
echo_quiet lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃b. semantics_prog (init_state (select_ffi sk)) init_env prog b ∧
           ((∃io. b = Diverge io ∧ echo_safe io ∧ echo_live sk io) ∨
            (∃io. asleep b io ∧ echo_safe (fromList io) ∧ echo_live sk (fromList io))) ∧
           (arrivals_finite sk ⇒ ∃io. asleep b io)

http_quiet lfd files prog ⇔   (* the same, with http_safe / http_live *)
  ∀sk. server_world lfd sk ⇒
       ∃b. semantics_prog (init_state (select_ffi sk)) init_env prog b ∧
           ((∃io. b = Diverge io ∧ http_safe files io ∧ http_live files sk io) ∨
            (∃io. asleep b io ∧ http_safe files (fromList io) ∧ http_live files sk (fromList io))) ∧
           (arrivals_finite sk ⇒ ∃io. asleep b io)
```

**Plain reading.** The program stays safe and live in every fair world. If only finitely many things ever arrive, its run is finite: it ends blocked forever in select, having answered everything. A busy-polling server, or one that spins in select on an fd it never reads, runs forever in such a world and fails.

### The theorems

**Echo** (theory `echoQuiet`; L0, layer final/10):

```
Theorem echo_blocking_quiet:
  echo_quiet 3w echo_blocking_main          (* echo_blocking_main = SNOC (main_call «main») echo_blocking_prog *)
```

`echo_blocking_prog` is the shipped blocking echo (`programs/echo-blocking/echoBlockingMain`):

```
fun main u = run_l ([3], [3], server 3);
```


**HTTP with bodies** (theory `httpQuietHeadline`; L0, layer final/10):

```
Theorem http_blocking_quiet:
  http_quiet 3w demo_files (SNOC (main_call «main») http_blocking_prog)
```

`http_blocking_prog` is the same protocol server at Level 2, on the loop that selects on what the computation declares it waits for (option C):

```
fun main u = run_q ([3], proto_server2 b_parse bresp_demo 3);
```

Both are unconditional. The generic protocol server's stability after the last arrival is proved once, for every protocol (`proto_stable`, theory `protoStable`).


**Bites** (`spec/QuietSpecBite`):
- `broken_runs_forever` / `_b`: any program that runs forever in a quiet fair world fails.
- `spin_worlds_quiet`: the worlds that made the #27 and #56 servers spin are quiet fair worlds.
- `broken_sleeps_early`: going to sleep before answering fails liveness.
- `select_stdin_fails`: selecting on a non-socket such as fd 0 fails.
- Non-vacuity: `hello_world_quiet`, `close_world_quiet`, `ideal_quiet_b`.

**What it does not say:**
- nothing about CPU while arrivals keep coming;
- nothing about how soon the program sleeps. The statement is qualitative.

---

<a id="5-kv"></a>
## 5. A key-value store over HTTP (L0): liveness ✅, safety ⏳

**The spec** (`spec/KvSpec`; approved by the user):

```
kv_spec lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            kv_safe io ∧ kv_live sk io

kv_step st (Req m k ver hs b) =
  if m = "POST" then (Ok "", (k =+ SOME b) st)
  else ((case st k of SOME v => Ok v | NONE => NotFound), st)
kv_run st [] = []
kv_run st (r :: rs) = let (a, st') = kv_step st r in a :: kv_run st' rs
reply_bytes as = bytes (FLAT (MAP print_response as))

is_order rss order ⇔ ∀c. MAP SND (FILTER (λx. FST x = c) order) = COUNT_LIST (LENGTH (rss c))
earlier order x y ⇔ ∃l1 l2 l3. order = l1 ++ [x] ++ l2 ++ [y] ++ l3
replies rss order c =
  MAP SND (FILTER (λ((d, i), a). d = c)
                  (ZIP (order, kv_run (λk. NONE) (MAP (λ(d, i). EL i (rss d)) order))))
precedes rss order evs (c, i) (d, j) ⇔
  ∃evs1. evs1 ≼ evs ∧
         reply_bytes (TAKE (SUC i) (replies rss order c)) ≼ bytes_written_to c evs1 ∧
         bytes_read_from d evs1 ≼ brequests (TAKE j (rss d))

kv_safe io ⇔
  ∀evs rss rests.
    LPREFIX (fromList evs) io ∧
    (∀c. EVERY valid_brequest (rss c) ∧ no_full_brequest (rests c) ∧
         bytes_read_from c evs = brequests (rss c) ++ rests c) ⇒
    ∃order. is_order rss order ∧
            (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
                   precedes rss order evs x y ⇒ earlier order x y) ∧
            ∀c. bytes_written_to c evs ≼ reply_bytes (replies rss order c)

kv_live sk io ⇔
  ∀c n rs. EVERY valid_brequest rs ∧ brequests rs ≼ sent_upto c n sk ⇒
           ∃evs ans. LPREFIX (fromList evs) io ∧ LENGTH ans = LENGTH rs ∧
                     reply_bytes ans ≼ bytes_written_to c evs
```

**Plain reading.** The requests are HttpSpec' requests. `POST k` with body v stores v under k, and `GET k` returns the stored value or 404. Safety is **linearizability**:
- the answers are those of one sequential run of all clients' requests, in some interleaving that keeps each client's order;
- the interleaving respects real time: if one request was answered before another was read, it comes first.

Liveness says every request is eventually answered. What the answer contains is safety's business.

**Liveness ✅:**

```
Theorem kv_live_rounds:          (* theory kvLive; L0, layer final/09 *)
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧ sched_wf s0 ⇒
  kv_live s0 (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
                (srelabel (kv_server lfdn)) s0 i)) NONE))
```


**Safety ⏳.** The headline will be:

```
kv_spec 3w kv_prog
```

The model-level order construction `kv_comp_safe` is proved. The CakeML side (`kv_semantics_prog` → `kv_prog_safe`) is in progress, and this layer waits for it.

The program is `fun main u = run_i ([3], kv_server 3);`, with `kv_server lfd = with_store kv_delta (λk. NONE) (kv_inner lfd)`.


**Bites** (`spec/KvSpecBite`):
- `broken_loses_write`.
- `broken_store_per_connection`: Dekker's example; it fails even sequential consistency.
- `broken_stale_read`: this one is sequentially consistent (`stale_read_sc`) but not linearizable.
- `broken_never_answers_kv`.
- Uniqueness: `parse_unique`.
- Non-vacuity: `both_trace_safe_and_live`.

---

<a id="6-close"></a>
## 6. Lifetimes: close and fd reuse (L1) ✅

**Theorem** (theory `echoEpisodesHeadline`; L1):

```
Theorem echo_episodes_prog_spec:
  echo_episodes_spec 3w echo_episodes_prog
```

**The world.** A second world model (`socket-v2/lifetimeWorld`):
- clients are numbered in the order they connect;
- the kernel gives an accepted connection a free fd, under any allocation policy that satisfies `alloc_ok`;
- `«sock_close»` frees an fd for reuse.

**The spec.** It is stated per episode: episode j is the life of the j-th accepted connection, from its accept to the close of its fd.

```
echo_episodes_spec lfd prog ⇔
  ∀sk. lifetime_world lfd sk ⇒
       ∃io. semantics_prog (init_state (lifetime_ffi sk)) init_env prog (Diverge io) ∧
            echo_episodes_safe io ∧ echo_episodes_live sk io ∧ echo_episodes_closes io

lifetime_world lfd sk ⇔ sk.listening = [(lfd, [])] ∧ sk.clients = [] ∧ sk.open_fds = [] ∧
                       alloc_ok sk.alloc ∧ lifetime_fair sk
echo_episodes_safe io     ⇔ ∀evs j. LPREFIX (fromList evs) io ⇒ ep_written j evs ≼ ep_read j evs
echo_episodes_live sk io  ⇔ ∀j n. ∃evs. LPREFIX (fromList evs) io ∧ sent2_upto j n sk ≼ ep_written j evs
echo_episodes_closes io   ⇔ ∀evs j. LPREFIX (fromList evs) io ∧ ep_eof_read j evs ⇒
                            ∃evs'. LPREFIX (fromList evs') io ∧ ep_closed j evs'
```


`ep_read` and `ep_written` are the reads and writes on episode j's fd, between its accept and its close (`spec-v2/EchoEpisodesSpec`, `ep_events`).

**Plain reading.** These are EchoSpec's safety and liveness, per client. In addition, every connection whose client has closed is eventually closed. So:
- data of an old connection can never reach a new client on a reused fd (bite: `EchoEpisodesSpecBite`);
- a server that never closes, and so never frees fds, fails.

**Linked to L0** by the simulation (`hrun_sim`, theory `lifetimeSimRun`): round by round, the handle loop has the core loop's history, so L0's proofs are reused unchanged.

---

<a id="7-peers"></a>
## 7. Peers: clients, proxies, backpressure (L2), partly ⏳

The peer world (`peerWorld`, `peerFair`) is POSIX-shaped:
- channels come from accept or connect;
- any fd can read, write, send part of its data, poll for writability, shut down and close;
- fds are reused;
- the environment is reactive, backpressure is a world parameter, and connects are three-way.

Specs in this world have the rely/guarantee form:

```
rg_spec cls guar (prog : dec list) ⇔
  ∀w. cls w ∧ ep_rely w ⇒
      ∃io. semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io) ∧ guar w io
```

**Scope.** The servers' peer-world specs hold in the SIMPLE CLASS ONLY:

    cls w = ep_server_world cs lfd a w ∧ no_backpressure w ∧ open_loop w ∧ nonsat1 lfd a w

They do not hold over all peer worlds. Our servers write with the full `«sock_write»`, and under backpressure a full write that doesn't fit is a misuse (it fails). So a server spec over every peer world is **false** for `echo_episodes_prog`, `http_prog` and `kv_prog`. Backpressure, fd limits and errors are meant to be absorbed by L3's verified wrappers (section 8), not by the servers.

The class is now `nonsat1` (user-approved: the converse directions need one more fd slot than `nonsat` leaves). The headline claims are drafted on `final/L2-00-statements`.

**What the simple class leaves out, and where each piece is covered** (user condition, 2026-10-16: the simple-class scope is acceptable *provided* these are covered later). Status as of 2026-10-17:

| excluded behaviour | covered where | statement or section | status |
|---|---|---|---|
| **backpressure and partial writes** (a server's full write that doesn't fit) | L3: the prefetching L1 wrappers buffer each fd's writes in an outbox, retry partial sends, and pause reading a fd whose outbox is above the high-water mark | design/36 §5.1 (write row) and §6; safety: R1-safe `l1pf_refines_hl` (`honestL1PFRefine`); liveness: R1-live (`fetch_progress`), with per-server obligations S3/S4 (D15) | R1-safe **proved** (model level); `fetch_progress` **proved**; live-data (D16) **in progress** |
| **cross-fd backpressure** (proxies and clients: stop reading A while B's outbox is full) | the moonshot: an L1 pause-policy parameter (`pol_self` for servers, `pol_never` for proxy and client), plus an outbox-level query | design/45 §2.2 (decision Q1 = P2, approved), §2.3 (`S4_relay`), §2.6 (the no-deadlock lemma) | design **approved**; not proved |
| **fd exhaustion** (EMFILE/ENFILE, `fd_limit`) | L3: the L0 world's `fd_limit`, and L1's `exhausted` state (the listener isn't polled until a close frees an fd, which fixes the spin); the moonshot's launch-time `fds_ok` | design/36 §4 (`fd_limit`), §5.1 (accept row), R1-live's connection half under [F3] (D14); design/45 §4.2 (`fds_ok`) | model and wrapper **built** (`exhausted_quiet`); liveness for new connections **in progress** |
| **errors and resets** (ECONNRESET, EPIPE; transient EINTR/ENOBUFS/ENOMEM) | L3: L1 absorbs them (a reset reads as EOF and marks the fd `gone`; transient failures retry). The specs move to the raw trace, so errors stay visible | design/36 §5.1, D16 (live data unless a hard error was observed, plus a corollary with no spurious hard errors), [F1] (D11, weak fairness on transient failures) | R1-safe **proved**; D16 **in progress**; the broken-fd-error gap is **decided**: [F1] restated on observed outcomes (D11′, design/36 §9; for poll, any failure counts) |
| **clients that are not open loop** (reactive peers, the environment reacting to what the server sends) | the moonshot's client, proxy and system theorems (the client never pauses its reads, so it is the sink that makes the waits well-founded) | design/45 §2.5 (the client), §3 (the shared kernel `l0sys`), §4 (system safety; liveness under fairness) | statements **drafted**; not proved |
| **filling the fd space** (`nonsat1`: fewer than 2^64 − reserved − 4 connections in all) | not covered, by design: a model bound far above any real `fd_limit`, which is the real constraint (row 3) | — | permanent idealisation (harmless) |


**Linked to L1 (proved):**
- `v2_instance_thm`: the lifetimes world is an exact instance of the peer world;
- `echo2_sym_equiv_thm`, in the simple class: the peer-world echo spec there is equivalent to the lifetimes echo spec (the converse also needs `nonsat`).

**Also proved:**
- fd discipline (`echo_prog_disciplined`, `echo2_prog_disciplined`);
- buffer closure:
  ```
  relay_safety : relay_closed P ∧ (∀t. P (FST (inside t)) (SND (inside t))) ∧
                 (∀t. relays (inside t) (outside t)) ⇒ ∀t. P (FST (outside t)) (SND (outside t))
  ```
  with `echo_relay_closed`, `http_relay_closed` and `kv_relay_closed`;
- the bites `never_polls_bite` and `refusal_bite`.

**⏳ Stated, not proved:**
- the HTTP and KV spec equivalences. These are expected to need `nonsat` and `ticks_forever`. For KV, `kv_live_rounds`' round bound must be restated in peer-world ticks;
- `v1_instance_disc`: the core world as an instance, for fd-disciplined programs with a bounded number of connects;
- `client_server_compose`;
- `http_prog_disciplined` for the series' `http_prog`. The old generic lemma should apply to the protocol skeleton, but this is not yet checked.

L2's statements are shown with their spike names; they are renamed when L2 is folded.

<a id="8-kernel"></a>
## 8. The real kernel (L3), ⏳

**Plan** (design/36): a minimal, honest C FFI (L0: one syscall per call, a total errno table), verified CakeML wrappers over it (the L1 FFI), and a refinement (R1–R4) from the kernel to the **lifetimes** world. Proved so far: the L0 C, its world, the L1 wrapper core and its never-fails invariant. R1 (safe) is at model level; R2–R4 are open.

**What is expected to transfer, and in what form.** Not "every headline":

| headline | reaches the kernel? | form | needs |
|---|---|---|---|
| `echo_episodes_prog_spec` (L1) | planned | safety; liveness *eventually* | R1/R4 under the fairness assumptions F1, F2, D(c), S1–S4, F3 and D16; a startup contract for the listener fd; fewer than 2^64 connections; a "listen failed" disjunct |
| HTTP and KV on the lifetimes world | planned, once their L1 proofs exist | the same | the same |
| L0 headlines (`echo_prog_spec`, `http_prog_spec`, `kv_spec`, `echo_blocking_quiet`, `http_blocking_quiet`) | **no** | — | the core-world runnables are retired (D5′); `echo_live` in the core world is false at a 256-fd limit |
| round bounds (`chat_spec_timely`, `kv_live_rounds`, `server_v_live` within N rounds) | only as *eventually* | — | the delay from kernel arrival to L1's fetch is unbounded |
| quiescence (QuietSpec) | **open** | — | a blocking variant of R1, and the HUP problem: `poll(2)` always reports POLLHUP/POLLERR, so a paused or closing fd can make a blocking poll return at once forever |
| chat | **open** | — | dropping slow clients (D7) changes its spec; chat is never quiescent |

"No server proof changes" holds at the **model level** only. At the whole-program level, each server's CakeML main theorem is re-based on the L1 loop's translation chain.

**Coverage of what L2 leaves out.** Backpressure, fd exhaustion, errors and reactive clients are covered here at L3 and in the moonshot. Section 7's coverage table gives, for each, the statement or design section and its status.

**Statements to write first** (from the transfer-claim review):
1. `l1pf_simple`, the new R2 for the prefetching L1. In simple worlds with at most one connect per tick and small data, the abstract world equals `sk_of w0`; otherwise it is an explicit *delay* of it. The trace relation is a fetch-placement relation, not a renaming.
2. `l0_echo2_spec`, the R4 template for the echo with close and fd reuse. It includes the hypotheses `reserved_ok`, fewer than 2^64 connections, and a listen-failure disjunct.
3. `quiet_on_kernel`: the blocking-variant transfer, with its side condition on paused, closing and HUP fds, or an L1 change that keeps such fds out of the blocking set. Plus its bite, `hup_spin_bite`.
4. The class stated in each L2 headline (above), and this table kept current.

<a id="9-trusted"></a>
## 9. What is trusted

1. **CakeML's semantics.** `semantics_prog` and FFI I/O events are imported from CakeML. The statements are about the source program. CakeML's compiler correctness theorem could carry them to machine code, but that step is not instantiated here.
2. **The spec files.** These are definitions only, and short:
   - `spec/KvSpec` (section 5);
   - `spec/EchoSpec`;
   - `spec/HttpSpec` (with HttpGetSpec and HttpHeadersSpec for the printer and responses);
   - `spec/QuietSpec`;
   - `EchoEpisodesSpec` for section 6 (L1).
3. **The socket world model and its fairness assumption:**
   - `socketWorld`, `socketFair` (`sched_wf`);
   - for section 6, `lifetimeWorld` and `lifetimeFair` (`lifetime_fair`, `alloc_ok`).
4. **The C implementation of the FFI calls** (`socket_ffi.c`) is assumed to behave like the model. **Known gap, being fixed:**
   - writes block until all bytes are sent, so a client that stops reading can stall the whole server;
   - a write to a departed peer silently drops data;
   - connection resets are reported as end-of-file;
   - accept failures such as running out of file descriptors are reported as "would block";
   - socket errors are reported as "readable".

   The model has none of these behaviours, so the theorems don't see them. A redesign is in progress (L3, section 8): a minimal, honest FFI (about one syscall per call), verified CakeML wrappers that absorb the raw semantics, and refinement proofs so the theorems about the lifetimes world (close and fd reuse) carry over.
5. **The RFC reference** `spec-rfc/rfc9112Framing`. It is trusted only as a reading aid: the agreement theorems check HttpSpec against it.

Nothing else is trusted: the async library, its CF refinement, the event loops, the scheduler and the protocol pipeline are all proved.

---

<a id="10-pending"></a>
## 10. Not yet proved (⏳)

- **The real kernel (L3):** R2–R4 and the whole-program corollaries for the lifetimes-world headlines (section 8). The L0 headlines are not planned to transfer; quiescence and round bounds are open.
- **HTTP in the lifetimes world (L1):** HttpSpec with close and fd reuse. The spec is written; the program proof is at the CakeML step.
- **KV safety** (`kv_prog_safe`; the model-level `kv_comp_safe` is proved, and the CakeML side is in progress) and the combined `kv_spec 3w kv_prog`. Liveness is proved (section 6b). The KV spec is approved (75af705c3).
- **Peers (L2):** the HTTP and KV spec equivalences, `v1_instance_disc`, `client_server_compose` (section 7).

---

<a id="appendix-chat"></a>
## Appendix: the chat server (not reviewed in the series)

By the user's decision, chat is an appendix until its revised spec gets an independent review.


**Theorem, eventual form** (`spike/chat-live`, #83):

```
Theorem chat_prog_spec:
  chat_spec 3w chat_prog
```


**Theorem, bounded-latency form** (`spike/chat-timely-fix`, #106). It is unconditional. The same holds for the bounded-memory GC hub: `gc_prog_timely : chat_spec_timely 4 3 4 3w chat_prog_gc`.

```
Theorem chat_prog_timely:
  chat_spec_timely 4 3 4 3w chat_prog
```


**The program.** `chat_prog` (`async/chat/asyncChatMain`):

```
fun main u = run_i ([3], chat_server 3);
```

**The spec, expanded** (`spec/ChatSpec`):

```
chat_spec lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            chat_safe io ∧ chat_live sk io

whole_lines bs   = REVERSE (dropWhile (λb. b ≠ 10w) (REVERSE bs))        (* up to the last newline *)
completes evs e  = the complete lines that event e (a read on fd (event_fd e)) finishes
relayed evs      = FLAT (GENLIST (λk. completes (TAKE k evs) (EL k evs)) (LENGTH evs))
                   (* every completed line, from every client, in the order the server read them *)
event_accepts d e ⇔ e is a «sock_accept» that returned d
owed d evs       = case SPLITP (event_accepts d) evs of
                   | (before, []) => []
                   | (before, acc) => DROP (LENGTH (relayed before)) (relayed evs)
                   (* the lines completed since d was accepted *)
connects_upto d n sk ⇔ ∃l. MEM (Connect l d) (arrivals_upto n sk.sched)

chat_safe io ⇔ ∀evs d. LPREFIX (fromList evs) io ⇒ bytes_written_to d evs ≼ owed d evs

chat_live sk io ⇔
  (∀d n. connects_upto d n sk ⇒ ∃evs. LPREFIX (fromList evs) io ∧ EXISTS (event_accepts d) evs) ∧
  (∀c n. ∃evs. LPREFIX (fromList evs) io ∧ whole_lines (sent_upto c n sk) ≼ bytes_read_from c evs) ∧
  (∀d evs. LPREFIX (fromList evs) io ⇒
           ∃evs'. LPREFIX (fromList evs') io ∧ owed d evs ≼ bytes_written_to d evs')
```

`completes`, written out:

```
completes evs e = DROP (LENGTH (whole_lines (bytes_read_from (event_fd e) evs)))
                       (whole_lines (bytes_read_from (event_fd e) (evs ++ [e])))
```

**The timely strengthening** (`spec/ChatSpecTimely`). The clock is the server's own polls, `polls evs = LENGTH (FILTER is_poll evs)`.

```
chat_spec_timely B A R lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            chat_safe io ∧ chat_live_open sk io ∧
            chat_prompt B io ∧ chat_accept_prompt A sk io ∧ chat_read_prompt R sk io
```

The clauses:
- `owed_open d evs = owed d (FST (SPLITP (event_eof d) evs))`. A departed client is owed only the lines completed before its EOF was read.
- `chat_live_open` is `chat_live` with `owed_open` in the delivery clause.
- `chat_prompt B io` ⇔ ∀evs d. LPREFIX (fromList evs) io ⇒ ∃evs'. LPREFIX (fromList evs') io ∧ polls evs' ≤ polls evs + B ∧ owed_open d evs ≼ bytes_written_to d evs'.
- `chat_accept_prompt A sk io` ⇔ ∀d n evs0. connects_upto d n sk ∧ LPREFIX (fromList evs0) io ∧ polls evs0 = n ∧ (evs0 ≠ [] ⇒ is_poll (LAST evs0)) ⇒ ∃evs. LPREFIX (fromList evs) io ∧ polls evs ≤ n + A * (nconnects n sk − naccepts evs0) ∧ EXISTS (event_accepts d) evs.
- `chat_read_prompt R sk io` ⇔ ∀c n. ∃evs. LPREFIX (fromList evs) io ∧ polls evs ≤ n + R * (1 + nconnects n sk + LENGTH (sent_upto c n sk)) ∧ whole_lines (sent_upto c n sk) ≼ bytes_read_from c evs.

**Plain reading.** Every complete line any client sends is relayed to every connected client, in one global order: the order in which the server read them. Each client gets only lines completed after it joined, and nothing is invented, duplicated, dropped or sent half-finished. In the timely form, each client:
- is accepted within 3 polls per connection waiting ahead of it;
- has its lines read within 4 polls per connection and per byte;
- gets what it is owed within 4 polls.

**Bites** (`spec/ChatSpecBite`):
- `broken_drops_a_line`, `broken_duplicates_a_line`.
- `broken_reorders_between_clients`.
- `broken_consistent_but_against_real_time`: all clients see the same order, but not the order the server read.
- `broken_relays_before_newline`, `broken_invents_a_newline`.
- `broken_sends_backlog`: a new client gets lines from before it joined.
- `broken_writes_unaccepted`.
- `broken_starves_a_client`, `broken_never_accepts`, `broken_never_reads`.
- Non-vacuity: `chat_spec_satisfiable`.

`ChatSpecTimelyBite` proves what each timely clause rules out.
