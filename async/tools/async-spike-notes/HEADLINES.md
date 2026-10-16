# Headlines: what is proved, stated in full

*async-spike, 2026-10-16. An interim document for reading before any proof. Every statement below is copied from the theory files, with the branch and commit it was taken from. The trusted definitions each one mentions are expanded next to it. There are no proofs and no intermediate lemmas.*

**✅ means the theory was built green at the stated commit; statement text alone doesn't count.** Each entry gives its evidence ("verified: …"): a built theory that `Holmake -n` reports up to date at that commit, with no `cheat` oracle tag in the theorem's `.dat`, or the author's green-build statement in the PR.

**Status markers:**
- ✅ **proved, unconditional**: no hypotheses, no cheats, built green (evidence given).
- 🟡 **proved, pending fold**: proved on a spike branch, and not yet in the review series.
- ⏳ **pending**: not proved yet.

## Contents

1. [The world every theorem lives in](#1-the-world)
2. [Echo: `echo_prog_spec`](#2-echo) ✅
3. [HTTP with bodies: `http_prog_pb_spec`](#3-http) ✅
4. [Quiescence: `echo_l_quiet`, `http_q_quiet`](#4-quiescence) ✅ (spike) / 🟡 (fold)
5. [Close and fd reuse: `echo2_prog_spec`](#5-close) ✅ (old series)
6. [Chat ✅ (spike) and KV (liveness ✅; safety ⏳)](#6-chat-kv)
7. [What is trusted](#7-trusted)
8. [Not yet proved](#8-pending)

---

<a id="1-the-world"></a>
## 1. The world every theorem lives in

Every headline has the same shape:

> for every fair world `sk` with one listener `lfd`, the CakeML program's
> I/O trace (from CakeML's own semantics, `semantics_prog`) is safe and live.

The world is a pure logical model of sockets (`world/sockets/ffiSpikeSocketFFI`). The program talks to it only through four FFI calls, plus a fifth, `«sock_select»`, in the quiescence statements.

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

This is the only assumption on the future (`ffiSpikeSocketFair`): no arrival is ever silently dropped.

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
## 2. Echo ✅

**Theorem.** `review-v2/07` (#90) and later; quoted from `review-v2/10-http-proto` @ `c4b80b0ca`, `async/headline/asyncM4EchoSpecScript.sml`:

```
Theorem echo_prog_spec:
  echo_spec 3w echo_prog
```

**The program.** `echo_prog` (`programs/echo/asyncEchoMain`):

```
fun main u = run_i ([3], server 3);
```

This is the async event loop running the echo server on listener 3.

*Verified:* built from `c4b80b0ca`'s tracked sources in `cakeml-worktrees/review-v2-11` (no tracked file modified; the layer-11 additions are new directories), with no cheat tag.

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
## 3. HTTP with request bodies ✅

**Theorem.** `review-v2/10-http-proto` @ `c4b80b0ca` (#100), `async/programs/http-pb/asyncProtoSemBScript.sml`:

```
Theorem http_prog_pb_spec:
  http_spec_b 3w demo_files http_prog_pb
```

*Verified:* built at `c4b80b0ca` in `cakeml-worktrees/review-v2-10` (`Holmake -n` up to date; no cheat tag). The RFC agreement (`rfc_frames_exactly_valid`, `rfc_subset_exact`) built the same way, from `c4b80b0ca`'s sources in `review-v2-11`, with no cheat tag.

**The program.** `http_prog_pb` (`programs/http-pb/asyncProtoProgB`) is the generic protocol server, instantiated with the bodies parser and responder:

```
fun main u = proto_main b_parse bresp_demo u;
```

**The demo's files.** `demo_files` is three paths: `/`, `/index.html` and `/about`. Each maps to a fixed string.

**The spec, expanded** (`spec/HttpSpecBodies`, with layer 1's tchar and H-CHARS changes):

```
http_spec_b lfd files prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            http_safe_b files io ∧ http_live_b files sk io

http_safe_b files io ⇔
  ∀evs c rs rest.
    LPREFIX (fromList evs) io ∧ EVERY valid_brequest rs ∧
    bytes_read_from c evs = brequests rs ++ rest ∧ no_full_brequest rest ⇒
    bytes_written_to c evs ≼ bresponses files rs

http_live_b files sk io ⇔
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

**Bites** (`spec/HttpSpecBodiesBite`):
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
## 4. Quiescence: no busy-waiting, CPU included

EchoSpec and HttpSpecBodies say nothing about CPU: a server that busy-polls meets them. QuietSpec adds a blocking `«sock_select»` and requires the program to go to sleep when the world goes quiet.

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

http_quiet_b lfd files prog ⇔   (* the same, with http_safe_b / http_live_b *)
  ∀sk. server_world lfd sk ⇒
       ∃b. semantics_prog (init_state (select_ffi sk)) init_env prog b ∧
           ((∃io. b = Diverge io ∧ http_safe_b files io ∧ http_live_b files sk io) ∨
            (∃io. asleep b io ∧ http_safe_b files (fromList io) ∧ http_live_b files sk (fromList io))) ∧
           (arrivals_finite sk ⇒ ∃io. asleep b io)
```

**Plain reading.** The program stays safe and live in every fair world. If only finitely many things ever arrive, its run is finite: it ends blocked forever in select, having answered everything. A busy-polling server, or one that spins in select on an fd it never reads, runs forever in such a world and fails.

### The theorems

**Echo.** ✅ on the spike; 🟡 being folded into `review-v2/11`. It was first proved on `spike/quiet-echo` (#77), quoted here from `spike/option-c-int` @ `65799d592`, `quiet/echo/asyncEchoQuietScript.sml`.

```
Theorem echo_l_quiet:
  echo_quiet 3w echo_l_main          (* echo_l_main = SNOC (main_call «main») echo_l_prog *)
```

`echo_l_prog` is the shipped blocking echo (`programs/echo-blocking/asyncM4LiveMain`):

```
fun main u = run_l ([3], [3], server 3);
```

*Verified:* built at `65799d592` in `cakeml-worktrees/quiet-echo` (`Holmake -n` up to date; no cheat tag). It also built green in the layer-11 fold (`cakeml-worktrees/review-v2-11`, not yet committed).

**HTTP with bodies.** ✅ on the spike; 🟡 being folded. It is proved on `spike/option-c-int` @ `65799d592`, `option-c-final/asyncOCQuietFinalScript.sml`, and is being folded into `review-v2/11` (`programs/http-quiet/`).

```
Theorem http_q_quiet:
  http_quiet_b 3w demo_files (SNOC (main_call «main») http_q_prog)
```

`http_q_prog` is the same protocol server at Level 2, on the loop that selects on what the computation declares it waits for (option C):

```
fun main u = run_q ([3], proto_server2 b_parse bresp_demo 3);
```

It is unconditional: the earlier hypothesis PROTO_STABLE is discharged by cf-actions' `proto_stable` (#93).

*Verified:* built at `65799d592` in `cakeml-worktrees/quiet-echo` (`Holmake -n` up to date; no cheat tag). It also built green in the layer-11 fold (`review-v2-11`, not yet committed).

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

<a id="5-close"></a>
## 5. Close and fd reuse ✅ (old series; to be folded as review-v2/13)

**Theorem.** `review/12-close-v2` @ `4b1f802bf` (#68), `async/headline/asyncHLEchoSpec2Script.sml`:

```
Theorem echo2_prog_spec:
  echo_spec2 3w echo2_prog
```

**The world.** A second world model (`socket-v2/socketV2FFI`):
- clients are numbered in the order they connect;
- the kernel gives an accepted connection a free fd, under any allocation policy that satisfies `alloc_ok`;
- `«sock_close»` frees an fd for reuse.

**The spec.** It is stated per episode: episode j is the life of the j-th accepted connection, from its accept to the close of its fd.

```
echo_spec2 lfd prog ⇔
  ∀sk. server_world2 lfd sk ⇒
       ∃io. semantics_prog (init_state (socket2_ffi sk)) init_env prog (Diverge io) ∧
            echo_safe2 io ∧ echo_live2 sk io ∧ echo_closes2 io

server_world2 lfd sk ⇔ sk.listening = [(lfd, [])] ∧ sk.clients = [] ∧ sk.open_fds = [] ∧
                       alloc_ok sk.alloc ∧ sched_wf2 sk
echo_safe2 io     ⇔ ∀evs j. LPREFIX (fromList evs) io ⇒ ep_written j evs ≼ ep_read j evs
echo_live2 sk io  ⇔ ∀j n. ∃evs. LPREFIX (fromList evs) io ∧ sent2_upto j n sk ≼ ep_written j evs
echo_closes2 io   ⇔ ∀evs j. LPREFIX (fromList evs) io ∧ ep_eof_read j evs ⇒
                            ∃evs'. LPREFIX (fromList evs') io ∧ ep_closed j evs'
```

*Verified:* PR #68's description states a green `Holmake -j1` with no cheat. It also built at `fbe3f0a71` (`spike/close-v2-sim`, #63) in `cakeml-worktrees/close-v2` (`Holmake -n` up to date; no cheat tag); there, `asyncHLEchoSpec2Script.sml` and `EchoSpec2Script.sml` are byte-identical to those at `4b1f802bf`.

`ep_read` and `ep_written` are the reads and writes on episode j's fd, between its accept and its close (`spec-v2/EchoSpec2`, `ep_events`).

**Plain reading.** These are EchoSpec's safety and liveness, per client. In addition, every connection whose client has closed is eventually closed. So:
- data of an old connection can never reach a new client on a reused fd (bite: `EchoSpec2Bite`);
- a server that never closes, and so never frees fds, fails.

Per the user's decision, the final series will present this as the *lifetimes* zoom level, linked to section 2 by a simulation theorem, with no "2" in the names.

---

<a id="6-chat-kv"></a>
## 6. Chat and KV

### 6a. Chat: every line to everyone, promptly ✅ (spike; not in the review series)

**Theorem, eventual form.** `spike/chat-live` @ `7eb3da6b1` (#83), `async/chat/asyncChatLiveHeadlineScript.sml`. It is unconditional, and the branch has no cheats.

```
Theorem chat_prog_spec:
  chat_spec 3w chat_prog
```

*Verified:* PR #83 states green through `asyncChatLiveHeadlineTheory` with no cheats. Also built in `cakeml-worktrees/chat` at `927009604`, a descendant of #83 and #106 (`Holmake -n` up to date; no cheat tag).

**Theorem, bounded-latency form.** `spike/chat-timely-fix` @ `b923a7fbe` (#106; SPEC CHANGE, approved per the PR), `async/chat/asyncChatTimelyHeadlineScript.sml`. It is unconditional. The same holds for the bounded-memory GC hub: `gc_prog_timely : chat_spec_timely 4 3 4 3w chat_prog_gc`.

```
Theorem chat_prog_timely:
  chat_spec_timely 4 3 4 3w chat_prog
```

*Verified:* PR #106 states green with no cheats. In `cakeml-worktrees/chat`, `asyncChatTimelyHeadline` and `asyncChatGCSemantics` were built at 12:23, just before `b923a7fbe` was committed (12:25). Neither `.dat` has a cheat tag. The only later change, `927009604`, edits a comment in ChatSpecTimely, so they await a rebuild there.

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

### 6b. KV store over HTTP: liveness ✅; safety ⏳ (in progress)

**The spec** (`spec/HttpKvSpec`, on `spike/http-kv` #52 and `spike/kv-live`; APPROVED by the user 2026-10-16, 75af705c3):

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

**Plain reading.** The requests are HttpSpecBodies' requests. `POST k` with body v stores v under k, and `GET k` returns the stored value or 404. Safety is **linearizability**:
- the answers are those of one sequential run of all clients' requests, in some interleaving that keeps each client's order;
- the interleaving respects real time: if one request was answered before another was read, it comes first.

Liveness says every request is eventually answered. What the answer contains is safety's business.

**Liveness ✅:**

```
Theorem kv_live_rounds:          (* spike/kv-live @ 5a72181db (#95), async/kv-live/asyncKvLiveScript.sml *)
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧ sched_wf s0 ⇒
  kv_live s0 (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
                (srelabel (kv_server lfdn)) s0 i)) NONE))
```

*Verified:* built at `5a72181db` (`spike/kv-live`, #95) in `cakeml-worktrees/library-liveness` (`Holmake -n` up to date; no cheat tag).

**Safety ⏳ (NOT proved).** `async/http-kv/asyncKvHeadlineScript.sml` at `spike/http-kv-impl` `cc172b4fd` contains the statement and a proof script for

```
kv_prog_safe : ∀sk. server_world 3w sk ⇒
                    ∃io. semantics_prog (init_state (socket_ffi sk)) init_env kv_prog (Diverge io) ∧ kv_safe io
```

It depends on `kv_semantics_prog` and `asyncKvSafe`, which are unbuilt and uncommitted. Update: the model-level order construction `kv_comp_safe` is now green (c102c2aad, draft #111, per the coordinator). The CakeML side (`kv_semantics_prog` → `kv_prog_safe`) is in progress. *(An earlier version of this document wrongly marked it ✅.)*

The program is `fun main u = run_i ([3], kv_server 3);`, with `kv_server lfd = with_store kv_delta (λk. NONE) (kv_inner lfd)`.

**Pending (⏳):**
- KV safety, CakeML side: `kv_semantics_prog` and `kv_prog_safe` (`kv_comp_safe` is green, #111).
- The combination `kv_spec 3w kv_prog`. `kv_live_rounds` is about the model's trace; joining it to the program's trace is done for chat by `chat_live_trace`.

**Bites** (`spec/HttpKvSpecBite`):
- `broken_loses_write`.
- `broken_store_per_connection`: Dekker's example; it fails even sequential consistency.
- `broken_stale_read`: this one is sequentially consistent (`stale_read_sc`) but not linearizable.
- `broken_never_answers_kv`.
- Uniqueness: `parse_unique`.
- Non-vacuity: `both_trace_safe_and_live`.

---

<a id="7-trusted"></a>
## 7. What is trusted

1. **CakeML's semantics.** `semantics_prog` and FFI I/O events are imported from CakeML. The statements are about the source program. CakeML's compiler correctness theorem could carry them to machine code, but that step is not instantiated here.
2. **The spec files.** These are definitions only, and short:
   - for chat and KV, `spec/ChatSpec`, `spec/ChatSpecTimely` and `spec/HttpKvSpec` (on their spike branches);
   - `spec/EchoSpec`;
   - `spec/HttpSpecBodies` (with HttpSpec and HttpSpecHeaders for the printer and responses);
   - `spec/QuietSpec`;
   - `spec-v2/EchoSpec2` for section 5.
3. **The socket world model and its fairness assumption:**
   - `world/sockets/ffiSpikeSocketFFI`, `ffiSpikeSocketFair` (`sched_wf`);
   - for section 5, `socket-v2/socketV2FFI` and `socketV2Fair` (`sched_wf2`, `alloc_ok`).
4. **The C implementation of the FFI calls** (`socket_ffi.c`) is assumed to behave like the model. **Known gap, being fixed:**
   - writes block until all bytes are sent, so a client that stops reading can stall the whole server;
   - a write to a departed peer silently drops data;
   - connection resets are reported as end-of-file;
   - accept failures such as running out of file descriptors are reported as "would block";
   - socket errors are reported as "readable".

   The model has none of these behaviours, so the theorems don't see them. A redesign is in progress (design/36, #94, #96, #98): a minimal, honest FFI (about one syscall per call), verified CakeML wrappers that absorb the raw semantics, and refinement proofs so the theorems about the lifetimes world (close and fd reuse) carry over.
5. **The RFC reference** `spec-rfc/rfc9112Framing`. It is trusted only as a reading aid: the agreement theorems check HttpSpecBodies against it.

**Bite evidence.** The bite lemmas are proved in the `*Bite` theories:
- ChatSpecBite is built and up to date at `927009604` (`cakeml-worktrees/chat`).
- ChatSpecTimelyBite, HttpKvSpecBite and EchoSpec2Bite were built (no cheat tag), but `Holmake -n` now reports 1–2 theories to rebuild because of later commits, so they await a rebuild.
- EchoSpecBite, HttpSpecBodiesBite and QuietSpecBite: built green from `c4b80b0ca`'s sources in `cakeml-worktrees/review-v2-11`, with no cheat tag.

Nothing else is trusted: the async library, its CF refinement, the event loops, the scheduler and the protocol pipeline are all proved.

---

<a id="8-pending"></a>
## 8. Not yet proved (⏳)

- **The honest FFI's L1 wrappers and refinement** (design/36): the theorems above, restated on the real kernel's semantics (#94 design; #96 and #98 the L0 C and world, green; #107 and #110 the L1 wrapper core and its never-fails invariant, green; the R1/R2 refinement in progress).
- **HTTP in the lifetimes world:** HttpSpecBodies with close and fd reuse. The spec is written first, for review (#105); there is no program proof yet.
- **KV safety** (`kv_prog_safe`; the model-level `kv_comp_safe` is green, #111, and the CakeML side is in progress) and the combined `kv_spec 3w kv_prog`. Liveness is proved (section 6b). The KV spec is approved (75af705c3).
- **Endpoint world** (#67, #104): clients and proxies as programs. The statements are written, for review.
