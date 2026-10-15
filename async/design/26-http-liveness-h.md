# 26: The header-tolerant HTTP program meets HttpSpecHeaders (safety and liveness)

Status: see §5. Branch `spike/http-liveness`, which merges
`origin/spike/http-headers` (cf-actions' header-tolerant pipeline, which
brings http-safety, presentation and HttpSpecHeaders) and
`origin/spike/m4-liveness` (the echo liveness route). No merged files were
edited. New files are in `async/http-liveness-h/`.

The coordinator relayed the user's decision: the HTTP headline is the
header-tolerant spec. This note is the program-level counterpart of 25,
which is model-level and for the strict HTTP spec.

## 1. The result

```
(* MAIN *)
Theorem http_prog_h_spec:
  http_spec_h 3w demo_files http_prog_h
```

`http_spec_h` is HttpSpecHeaders' trusted statement, unchanged:

```
http_spec_h lfd files prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            http_safe_h files io ∧ http_live_h files sk io
```

`http_prog_h` is cf-actions' header-tolerant program (`asyncHttpMainH`):
the basis, the socket and Async modules, the dynamic-interest event loop
`run_i`, and `fun main u = run_i ([3], http_server_h demo_files 3)`.

The proof follows spike/m4-liveness's `echo_prog_spec`:
1. `http_semantics_prog_headers` (cf-actions) gives divergence with the
   loop's trace, and safety.
2. `http_live_h_rounds` (this branch) gives liveness on the same trace.

## 2. The chain (liveness)

| step | theorem | file |
|---|---|---|
| invalid header-tolerant input stays invalid when extended | `parse_hrequest_invalid_ext`, `parse_all_h_invalid_ext` | asyncHttpParseHExt |
| the handler as a three-state machine (port of 25's) | `hmachine_inv`, `hmachine_trans_TAKE`, … | asyncHttpMachineH |
| **machine-level liveness when reads may be partial** | `hmachine_live_p` | asyncHttpDrainH |
| the model transcript vs the world's log; every connection is handed out (generic `server_with hf`) | `TSg_accepted`, `TSg_eof`, `TSg_read_none`, `sw_conn_accepted` | asyncSWSock |
| the handler of an accepted c on the loop's rounds | `http_h_view` | asyncHttpLiveH |
| **liveness on an accepted connection** | `http_accepted_live_h` | asyncHttpLiveH |
| **HttpSpecHeaders' `http_live_h` for the loop's trace** | `http_live_h_rounds` | asyncHttpLiveH |
| the whole program | `http_prog_h_spec` | asyncHttpSpecH |

### 2.1 Why not 25's model theorem directly

25's world model (`asyncWorld`) reads everything that has arrived in one
read. The socket world (`ffiSpikeSocketFFI`) reads at most `bufsz = 4096`
bytes per read, and no lemma relates the two closed loops. So, like
spike/m4-liveness for echo, the argument is redone on the socket rounds
(`gstate`/`gperf`/`ghist`). 25's per-connection machine and its
model-level `server_with` facts carry over: `sw_handler_view` and
`sw_accept_progress` are used unchanged.

### 2.2 Machine-level liveness with partial reads (asyncHttpDrainH)

`hmachine_live_p`: let D be the data to answer. Assume:
- what has been read and D are always comparable;
- if the handler waits with an incomplete buffer while fd is not reported
  readable, everything has been read;
- a read, unless D is already read, reads all of D or reads something;
- stopping at end-of-file means D has been read.

Then the handler writes the responses to all complete requests of D. The
proof is by induction on the unread length of D. Each cycle answers at
most K buffered requests, waits one round and reads, so it takes at most
K + 3 rounds and either reads all of D or reads at least one more byte.
The other ways it can end are an invalid buffer (D's requests have all
been answered, `stopped_invalid`) or end-of-file (D has been read).

### 2.3 The socket world provides the assumptions (asyncHttpLiveH)

`http_h_view` puts c's handler on its own history g, starting at the
round a where c was handed out (`sw_handler_view` on
`MAP sfs (ghist …)`). At round a + j:
- the bytes of what it has read are `pread_all c (gperf … (a + j))`;
- the bytes of what it has written are `bytes_written_to c` of the events
  of rounds 0..a + j (`gen_rounds_bytes`).

Accounting (`grounds_acct`) gives `sent_upto c k = read ++ incoming`. The
four assumptions then come from:
1. comparable: both are prefixes of `sent_upto c (a + j)` (`bytes` is
   injective, `bytes_prefix`);
2. not readable ⇒ c is not ready in the next world (`ready_EL_ghist`,
   `interest_accepted`) ⇒ nothing is unread;
3. a read: the handler's outstanding read is a socket read of c
   (`hmachine_reading`, `TSg_read_none`). If D is not all read, c has
   unread data, so the read reads something (`sock_acts_read_nonempty`);
4. end-of-file is a read that returned nothing (`hmachine_eof`,
   `TSg_eof`), after which nothing is unread (`grounds_eof`).

`http_live_h_rounds` puts it together. If requests rs were sent on c by
round n, then c is a connection, so it is handed out at some round N0
(`sw_conn_accepted`). From round n + N0, `http_accepted_live_h` with
D = the printed requests gives the responses, and `parse_all_h` of
printed requests is those requests (`parse_all_h_printed`).

## 3. Reuse

- asyncSWSock's lemmas are for any `server_with hf` with `hok hf` and
  `uses_ok`, so they also serve the strict HTTP server (and echo-like
  servers).
- 25's strict pieces (`async/http-liveness/`) are kept. The strict
  program-level link is not done; it is now optional/archive.

## 4. Assumptions made

1. **Copies over generalisation.** asyncHttpMachineH and asyncHttpDrainH
   are mechanical ports of 25's strict files (rename the parser, requests
   and handler). I did not make them parametric in the parser. That keeps
   both readable on their own, at the cost of duplication.
2. **No bound in the program-level statement.** HttpSpecHeaders' liveness
   is "eventually". The machine-level bound (D's length plus 2, times
   K + 3) only serves to pick a long enough history.
3. **Merges.** spike/http-headers and spike/m4-liveness were merged
   whole (both clean).

## 5. Status

**Done.** `http_prog_h_spec : ⊢ http_spec_h 3w demo_files http_prog_h` is
proved. `Holmake -j2` is green in `async/http-liveness-h/` (it builds the
whole program from ../http-headers), and there are no cheats. The
theorem's only tag is `DISK_THM`, so it depends on no oracle.
