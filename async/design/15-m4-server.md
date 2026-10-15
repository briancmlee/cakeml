# 15: The concurrent echo server in CakeML (M4 step 1)

Status: **tasks 1 and 2 done; task 3 partly proved, the rest stated.** No
cheats; `Holmake -j2` in `async/m4-server/` is green. Branch
`spike/m4-server`, stacked on `spike/cf-reactive`, with
`spike/async-echo-server` (the model server, `08-echo-server.md`) merged
in.

Background: `05-cf-actions.md` (the representation `(acts, residual)`,
`STEPA`/`COMP`, the library specs), `08-echo-server.md` (the model server
and `echo_server_safety`), `10-cf-reactive.md`.

Files (`async/m4-server/`):

| file | contents |
|---|---|
| `asyncM4ApproxScript.sml` | depth-indexed approximation `STEPAd`/`COMPd`, the limit lemma, depth-n specs of poll/skip/bind/both |
| `asyncM4ServerProgScript.sml` | the CakeML code (model types as CakeML datatypes, `readable`, `map`, `handler`, `server`), `readable_spec`, `map_spec_d` |
| `asyncM4ServerSpecScript.sml` | `handler_spec`, `server_spec` (MAIN) |
| `asyncM4ServerUsesScript.sml` | the server only reads/writes fds it accepted (model; for `srun_ok`) |
| `asyncM4RelabelScript.sml` | relabelling a computation's vocabulary (model; the bridge to M3's socket vocabulary) |

## 1. The CakeML server

The code mirrors `asyncServerScript.sml` line for line. Recursion is
ordinary CakeML recursion:

```sml
fun readable fd =
  wait (fn w => case w of (rdy, t, res) =>
    if has_readable fd rdy then Some () else None);

fun map f c = bind c (fn x => return (f x));

fun handler fd =
  bind (readable fd) (fn u =>
  bind (emit (Read fd)) (fn res =>
    case res of
      Data d => bind (emit (Write fd d)) (fn w => handler fd)
    | Eof => return ()
    | _ => handler fd));

fun server lfd =
  bind (readable lfd) (fn u =>
  bind (emit (Accept lfd)) (fn res =>
    case res of
      Accepted fd => map (fn p => ()) (both (handler fd) (server lfd))
    | _ => server lfd));
```

Calling `handler fd` or `server lfd` terminates at once: each recursive call
sits in a continuation of `bind`, which `bind` only calls after a poll.
The model's `event`, `action` and `response` types are CakeML datatypes
as they are (`register_type`), with refinement relations
`ASYNCSERVER_ACTION_TYPE` and `ASYNCSERVER_RESPONSE_TYPE`. A snapshot's ready
set is a CakeML list of events: `EVENTS s v ⇔ ∃es. s = set es ∧ LIST_TYPE
ASYNCSERVER_EVENT_TYPE es v`. `has_readable` is translated by the
translator.

## 2. The specs (MAIN), verbatim

With `ACTION = ASYNCSERVER_ACTION_TYPE`, `SNAP = SNAPSHOT EVENTS
ASYNCSERVER_RESPONSE_TYPE` (overloads in `asyncM4ServerSpec`):

```
(* MAIN: the CakeML echo handler implements the model's handler: for a
   connection fd, handler fd returns a computation value that, round by
   round, emits exactly the model's actions (Read fd, Write fd d, ...) and
   finishes exactly when the model's handler fd does. *)
Theorem handler_spec:
  NUM fd fdv ⇒
  app (p:'ffi ffi_proj) handler_v [fdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (handler fd) v)

(* MAIN: the CakeML concurrent echo server implements the model's server:
   for a listener lfd, server lfd returns a computation value that, round
   by round, emits exactly the model's actions (Accept lfd, and the
   actions of every accepted connection's handler) and never finishes,
   exactly as the model's server lfd. *)
Theorem server_spec:
  NUM lfd lfdv ⇒
  app (p:'ffi ffi_proj) server_v [lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (server lfd) v)
```

`handler fd` and `server lfd` on the right are **the model's own
fix-defined computations** (`asyncServer`), not copies. `COMP` is
cf-actions' predicate: by `run_spec` (05/10), a loop that polls this value
performs exactly the model's action log.

### How recursion is proved

The model defines `server = fix server_body`. The CakeML function calls
itself. The bridge is the model's unfolding equation (`server_unfold`, from
`fix_unfold` and contractivity), together with an approximation argument:

1. **A depth-indexed predicate** `STEPAd n` (`asyncM4Approx`): the residual
   implements the model for its next `n` polls, and the residual after
   them has the right shape (Done with a related result, or Pending).
   cf-actions' `STEPAn 0 = T` is too weak here. The library code inspects
   residuals (bind's case split, skip, both's case split), so a
   combinator applied to a depth-0 value must still know its shape.
   `COMPd n m v = POLL_RESULT ACT (STEPAd n) m v`.
2. **Depth-n specs of the combinators**, whose *hypotheses* are also only
   up to depth n:

   ```
   (* MAIN (helper): bind up to depth n. *)
   Theorem bind_spec_d:
     ∀n m mv.
       wf m ∧ COMPd p ACT A (SNAPSHOT READY R) n m mv ∧
       (∀x xv. A x xv ⇒
          returns p gv [xv]
            (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
       app (p:'ffi ffi_proj) bind_v [mv; gv] emp
         (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) n
                     (bind m g) v)

   (* MAIN (helper): a guarded bind gains one level of depth. *)
   Theorem bind_guarded_spec_d:
     wf m ∧ (m []).result = NONE ∧ COMPd p ACT A (SNAPSHOT READY R) (SUC n) m mv ∧
     (∀x xv. A x xv ⇒
        returns p gv [xv]
          (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
     app (p:'ffi ffi_proj) bind_v [mv; gv] emp
       (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) (SUC n)
                   (bind m g) v)

   (* MAIN (helper): both up to depth n. *)
   Theorem both_spec_d:
     ∀n m1 m2 c1 c2.
       wf m1 ∧ wf m2 ∧
       COMPd p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) n m1 c1 ∧
       COMPd p ACT B (SNAPSHOT READY R) n m2 c2 ⇒
       app (p:'ffi ffi_proj) both_v [c1; c2] emp
         (POSTv v. &COMPd p (ACT : 'act -> v -> bool) (PAIR_TYPE A B)
                     (SNAPSHOT READY R) n (both m1 m2) v)
   ```

   Also `poll_spec_d` (a poll consumes one level), `skip_spec_d`,
   `bind_guarded_spec_0`, `map_spec_d`, and `COMP_IMP_COMPd` (the full
   predicate gives every depth).
3. **Induction on the depth** (`handler_spec_d`, `server_spec_d`): unfold
   once, use `bind_guarded_spec_d` at the outer `bind (readable fd) …`
   (`readable` cannot finish before a poll). Its continuation is then needed
   only up to depth n, and inside it the recursive calls are the induction
   hypothesis. `bind_spec_d`, `both_spec_d` and `map_spec_d` carry the
   depth through the rest. For the server, the accepted connection's
   handler comes from `handler_spec`, at full depth.
4. **The limit**:

   ```
   (* MAIN: the limit argument for recursive computations *)
   Theorem app_COMP_of_approxd:
     args ≠ [] ∧
     (∀n. app p f args H (POSTv v. &COMPd p ACT RES WORLD n m v)) ⇒
     app (p:'ffi ffi_proj) f args H (POSTv v. &COMP p ACT RES WORLD m v)
   ```

   (via `STEPAd n ⇒ STEPAn n` and cf-actions' `app_COMP_of_approx`).

No bridging lemma between `fix` and CakeML recursion beyond
`handler_unfold` / `server_unfold` was needed. The approximation argument
does the work that contractivity does in the model. The recipe is generic:
any recursive library computation whose recursive calls are behind a
guarded bind can be specified this way, at about 80 lines of CF per
function.

## 3. The program-level theorem M4 will deliver (statement, not proved)

### 3.1 The pieces

- **M3** (spike/m3-assembly, `asyncM3World`/`asyncM3Loop`): for a
  computation `m` over the socket vocabulary (`sact`: `Accept l`, `Read c n`,
  `Write c bs`; `sresp`: `Accepted (word64 option)`, `Got (bytes option)`,
  `Wrote`), with `COMP p SACT SRESP … m cv`, `wf m` and `srun_ok fds m s0`,
  the event loop diverges, and the actions in its I/O trace are `m`'s action
  log on the history `shist fds m s0 n` the socket world generates
  (`strace_actions_rounds`).
- **This note**: `server_spec` (CF) and `server_uses_accepted` (model).
- **08**: `echo_server_safety` (model), on every history.

### 3.2 Bridge 1: the vocabulary

The server speaks the model's vocabulary (num fds, strings, `Readable`
events). M3 speaks the socket model's. The bridge is a relabelling
(`asyncM4Relabel`, proved):

```
relabel fa fs m h = m (MAP fs h), with its actions mapped by fa

(* MAIN *) Theorem wf_relabel:  wf m ⇒ wf (relabel fa fs m)

(* MAIN: transcripts of a relabelled computation *)
Theorem trans_relabel:
  (∀s. (fs s).results = MAP fr s.results) ⇒
  MAP (λ(a, r). (fa a, r)) (trans m (MAP fs h)) =
  MAP (λ(a, r). (a, OPTION_MAP fr r)) (trans (relabel fa fs m) h)
```

The proposed instance (definitions for M4 step 2; not in HOL yet, since
they need M3's types):

```
fa (Accept l)    = Accept (n2w l)
fa (Read fd)     = Read (n2w fd) N              (N: a fixed buffer size, 0 < N < 256**8)
fa (Write fd d)  = Write (n2w fd) (MAP (n2w o ORD) d)
fr (Accepted (SOME c)) = Accepted (w2n c)       fr (Accepted NONE) = NoConn
fr (Got (SOME []))     = Eof                    fr (Got NONE)      = WouldBlock
fr (Got (SOME bs))     = Data (MAP (CHR o w2n) bs)   (bs ≠ [])
fr Wrote               = Written
fs s = <| ready := IMAGE (Readable o w2n) s.ready; now := s.now;
          results := MAP fr s.results |>
```

Round trips hold where they are needed: fds that the server uses come from
`w2n` of socket fds, so `n2w (w2n c) = c`; bytes go through `CHR o w2n` and
back through `n2w o ORD`. On the CakeML side this needs a library
combinator `relabel` (poll the inner computation with `fs w`, map `fa` over
its actions) and a CF spec `COMP … m c ⇒ COMP … (relabel fa fs m)
(relabel_v …)`. This is the same shape as `map`, about 100 lines (estimate).

### 3.3 Bridge 2: no misuse (`srun_ok`)

At the model level this is proved, on every history and with no world
assumption:

```
(* MAIN: the echo server uses the socket API correctly, on every history:
   it accepts only on the listener lfd, and it reads or writes a
   connection fd only after the response Accepted fd. *)
Theorem server_uses_accepted:
  ∀h. accepts_on lfd (trans (server lfd) h) ∧
      ∀fd. acc_first fd (trans (server lfd) h)
```

Here `accepts_on lfd tr` says every `Accept` in `tr` is `Accept lfd`, and
`acc_first fd tr` says no read or write of fd comes before the pair
`(Accept _, SOME (Accepted fd))`. `acc_first_MEM` restates it by positions.

To turn this into M3's `srun_ok fds (relabel fa fs (server lfd)) s0`, the
remaining world-side lemmas are (not proved, they need the socket model and
M3's `srounds`):

1. `sock_do` succeeds on `Accept l` iff `l` is a listener, on `Read c n`
   (with `0 < n < 256**8`) and `Write c bs` iff `c` is a connection
   (from `sock_accept_def`, `sock_read_def`, `sock_write_def`).
2. **Listeners and connections only grow**: `deliver1`, `tick`,
   `sock_accept`, `sock_read`, `sock_write` and `sock_poll` never remove a
   listener or a connection. (By cases on the definitions; there is no
   `close`.)
3. **An accepted fd is a connection**: if `sock_accept l s = SOME (SOME c,
   s')` then `is_conn s' c`. (`deliver1 (Connect l c)` adds `c` to the
   listener's queue and to `conns` together, and only queued fds are
   handed out. Invariant: every queued fd is a connection.)
4. **The transcript is the world's**: on `shist fds m s0 n`, the pair
   `(fa a, r)` in m's transcript is an action performed in the run with
   the world's response `r`. This is M3's construction (`srounds`
   records exactly `sock_acts`' responses as the snapshot's results),
   restated as a transcript lemma: `trans m (shist fds m s0 n)` paired
   with the `sock_acts` results, round by round.
5. `lfd` is a listener in `s0` (a precondition of the program).

With 1–5, induction on rounds gives `srun_ok` from `server_uses_accepted`
and `trans_relabel`. Every action in round n is `Accept (n2w lfd)` (a
listener by 2 and 5), or a read or write of `n2w fd` where
`Accepted fd` came earlier, i.e. `sock_accept` returned `c` with `w2n c = fd` (4).
Then `c` is a connection (3) and still is one (2).

### 3.4 Bridge 3: transcripts and per-connection streams

The socket model keeps, per connection `c`, `incoming` (arrived, unread),
`peer_closed` and `outgoing` (everything written). Define from the
schedule `delivered c s0 s` = the bytes of the `Data c bs` arrivals the
run has delivered so far (before any `Eof c`). The bookkeeping lemmas:

6. **Writes**: in a run, `outgoing c` (final) = `outgoing c` (initial) ++
   FLAT of the byte strings of the `Write c bs` actions, in order.
7. **Reads**: `FLAT (bytes read from c) ++ incoming c = delivered c` (for
   a connection that starts empty). Reads remove a prefix of `incoming`
   (`sock_read`: `TAKE n` returned, `DROP n` kept). `tick` appends
   arrivals to `incoming`.
8. **The transcript's view**: under the relabelling, `read (w2n c) tr`
   mapped back to bytes is the list of bytes read from `c`, and `written
   (w2n c) tr` mapped back is the list of bytes written to `c`. This
   follows from 4 and the definitions of `fa`/`fr`.
9. **Freshness**: the socket world hands out distinct connections
   (`deliver1 (Connect l c)` requires `c` not already a connection or
   listener, and a connection is accepted at most once, since it is
   removed from the queue). So `fresh (trans (server lfd) (MAP fs h))`.

### 3.5 The statement

For the compiled program `server_prog lfd` (the loop of M3 running
`relabel fa fs (server lfd)`) in a socket world started in `s0`, with all
connections initially empty and `lfd` a listener:

```
(* PROPOSED MAIN (M4): the compiled echo server, run against the socket
   model, diverges; and after every round n, for every connection c,
   everything the server has written to c, followed by everything still
   unread on c, is exactly the data the client has sent on c so far. *)
∀n c. is_conn s_n c ⇒
   (conn s_n c).outgoing ++ (conn s_n c).incoming = delivered c s0 s_n
```

where `s_n = SND (srounds fds m s0 n)` and `m = relabel fa fs (server lfd)`.
It holds because:

- M3 + `server_spec` + `wf_server` + `wf_relabel` give the trace;
- `server_uses_accepted` + 1–5 give `srun_ok`;
- `echo_server_safety` on the history `MAP fs (shist …)`, with 9 for
  `fresh`, gives `written fd = read fd`;
- 6–8 turn `written = read` into `outgoing c = FLAT (bytes read from c)`,
  and 7 gives `… ++ incoming c = delivered c`.

Read as: **no client ever receives another client's data, data is echoed
in order, and nothing that has been read is held back.** At the end of
every round, the bytes not yet echoed are exactly the bytes not yet read.
Liveness (unread bytes are eventually read) needs the schedule fairness
assumptions of 08 §4 and is separate.

## 4. What wasn't done, and estimates

1. **CakeML `relabel` and its spec** (§3.2): about 100 lines; same shape as
   `map_spec_d`.
2. **World-side lemmas 1–9** (§3.3, §3.4): mostly case analysis on the
   socket model's definitions plus one invariant (queued ⇒ connection),
   and the transcript restatement of `srounds` (4). Estimate 300–500
   lines, on top of M3's branch.
3. **The program-level theorem** (§3.5): assembling the above with M3's
   whole-program theorem once it exists (M3 task 2).

## 5. Assumptions made

1. **Vocabulary**: the CakeML server uses the model's own types as CakeML
   datatypes (`register_type`), and the ready set is a CakeML list of
   events. This is the most faithful choice for "implements the model's
   server". The translation to M3's socket vocabulary is a separate
   relabelling (§3.2), not a change to the server or the model.
2. **A new approximation `STEPAd`** instead of cf-actions' `STEPAn`
   (§2), because `STEPAn 0 = T` is too weak for code that inspects
   residuals. It is additive: `STEPAd n ⇒ STEPAn n`, so the existing limit
   lemma is reused.
3. **`map` is written as `bind c (fn x => return (f x))`**, specified via
   the model's `map_as_bind` (needs `wf`).
4. **Specs are per-function, not a generic "guarded recursion" CF lemma**.
   With `bind_guarded_spec_d` the per-function induction is short, and a
   generic lemma would need a quantification over CakeML function bodies
   that is harder to read.
5. **Task 3 is stated as a design-note theorem.** The model-level pieces
   that don't depend on M3 are proved (`server_uses_accepted`,
   `trans_relabel`, `wf_relabel`). The rest needs M3's definitions and the
   socket model, which this branch deliberately does not merge.
6. **No `fresh` in `server_uses_accepted`**: the ordering property holds
   on every history.
