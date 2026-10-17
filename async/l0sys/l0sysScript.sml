(*
  l0sys: THE MULTI-PROCESS L0 MODEL (trusted; design/45 §3.1, for the
  user's review).  A STATEMENT: nothing here is proved.

  n processes on one host, each running a CakeML program over the L0 C
  (async/runnable/l0/socket_ffi_l0.c), and one kernel.  Each process's
  calls are answered by ITS OWN L0 state, by honestL0World's l0_call,
  unchanged: what the per-process model says about one call (its errors,
  its choices) holds here as it is.  What is new is only what links the
  processes: the shared port namespace, the kernel's pairing of the two
  ends of a loopback connection, the bytes moving between them, and
  close-on-exit.  Everything else between processes comes from outside
  (the environment: other processes on the host or elsewhere).

  ANCHORED ON THE STANDARDS, as honestL0World (design/36 §4.3):
    [P]  POSIX.1-2024 (IEEE Std 1003.1-2024, Issue 8): XBD 3 (File
         Descriptor), XSH 2.6, 2.10.6 (Socket Types), connect(), listen(),
         bind(), setsockopt() (SO_REUSEADDR), poll(), _Exit().
    [T]  RFC 9293 (TCP).
  Rules (as design/36 §4.3): where a standard is specific the model
  follows it; where it is loose or silent the model is NONDETERMINISTIC
  (a step may or may not happen; a value is the world's choice), so every
  permitted behaviour is a model behaviour.  No platform behaviour is a
  justification; the conformance probes (design/45 §3.1) are TESTS of the
  [A..] assumptions on each platform we run, Linux included.

  THE STATE (sysstate):
   - procs k: process k's L0 state (honestL0World's l0world: its
     listeners, channels, fd table, reserved fds, fd limit, choices, call
     history).  Per process [P XBD 3]: "File Descriptor: A per-process
     unique, non-negative integer used to identify an open file".  The
     choices (ch) are functions of k's own call history; since each run
     is fixed and k's history prefixes are distinct within it, any
     behaviour of a real run is matched by some choice functions.
   - alive k: k has not exited.
   - the links: target (k, j) is the port k's connect j asked for; peer
     (k, j) = SOME (k', j') pairs two ENDS (process, channel) of one
     connection; moved, acked and finned record how far each end's stream
     has reached its peer.
   - backlog k p: the length limit of the listen queue of k's listener on
     port p [P listen: the backlog is "a hint to the implementation which
     the implementation shall use to limit the number of outstanding
     connections"; the limit itself is the implementation's]: any value.

  THE STEPS (sys_step), one per label:
   - Call k nm conf bytes out: process k's L0 call, answered by l0_call on
     procs k.  A blocking sys_poll returns only once a requested fd is
     ready (or a transient error happens) [P poll: "shall block until at
     least one of the requested events" or interrupted], when the
     scheduler next runs k.  A sys_connect that the L0 state says
     connected AT ONCE was paired atomically with a listener of the system
     on the port, or reached an outside process.
   - Kern (Handshake k j k'): k's pending connect j completes with k''s
     listener on its port, if that listener's queue has room: k sees
     LConnUp j, k' a new queued channel (LIncoming), and the two ends are
     paired [T §3.5: a SYN to a LISTEN socket].  SEVERAL listeners may be
     on one port: the C sets SO_REUSEADDR, and [P setsockopt] says the
     bind rules then "should allow reuse of local addresses, if this is
     supported by the protocol", so the model does not exclude it, and a
     connect may reach any of them.
   - Kern (Move k j n): the next n bytes of end (k, j)'s stream (what k's
     sends accepted, c.sent) reach its peer's inbox, in order and
     unchanged [P 2.10.6: SOCK_STREAM "provides sequenced, reliable,
     bidirectional, connection-mode byte streams"; T §3.4 sequence
     numbers].  Kern (Ack k j n): n of the moved bytes are acknowledged
     to k (LDrain: in flight no more) [T §3.4]; never more than moved.
   - Kern (Fin k j): once end (k, j) is shut (shutdown or close) and all
     its bytes have moved, its peer sees the EOF [T §3.6: the FIN follows
     the data in sequence space].
   - Kern (Break k j e keep): end (k, j) breaks with e, at any moment: a
     RST (sent when a peer closes with unread input, [T §3.6.1], or a
     listener with queued connections closes), a user timeout [T §3.8.4],
     a resource failure.  [P recv, send] list ECONNRESET and ETIMEDOUT;
     neither standard says a connection cannot break, so the model lets
     any end break at any time.
   - Kern (ConnFail k j e): k's pending connect j fails with e, at any
     moment [P connect: ECONNREFUSED "The target address was not
     listening for connections or refused the connection request",
     ETIMEDOUT "The attempt to connect timed out before a connection was
     made"].
   - Env (EIncoming k p): an outside process connects to k's listener on
     port p (if its queue has room).  Env (EConnUp k j): k's pending
     connect j completes with an outside process (one that also listens
     on the port, under SO_REUSEADDR, or holds a port the system does
     not).  Env (EArrive k a): on an end with NO peer in the system, the
     outside peer sends bytes (LData), its EOF (LEof), or reads (LDrain).
     [A1] An end with a peer in the system gets bytes only from that
     peer: the system's processes do not share their sockets with any
     other process (the L0 C neither forks nor passes fds), and a
     SOCK_STREAM connection's bytes are those its peer sent [P 2.10.6].
   - Exit k: k ends (its program finished, failed, or ran out of memory;
     a signal): [P _Exit: "All of the file descriptors ... open in the
     calling process shall be closed"]; abnormal termination closes them
     as well [P 2.4.3, "as if by _exit"].  Its channels and listeners are
     closed as by close (FIN after the data, or a break of the peer).

  THE RUN (l0sys_run S rs): rs is a finite interleaving of labels from an
  initial state with one fresh L0 state per program of S; each label is a
  step; and each process's calls are exactly what its program makes when
  answered as recorded (prog_makes, with a replay oracle).  Fairness is
  NOT in the model (design/45 [F0], liveness only): a process may never
  be scheduled again, a byte never move.
*)
Theory l0sys
Ancestors
  ffi semantics ml_prog llist alist mlstring Marshalling honestL0
  honestL0World honestL0Rely
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The state *)

(* An end of a connection: process k's channel j *)
Type cend = “:num # num”

Datatype:
  sysstate = <| procs : l0world list          (* process k's L0 state *)
              ; alive : num -> bool            (* process k has not exited *)
              ; target : cend -> num option    (* the port a connect end asked for *)
              ; peer : cend -> cend option     (* the other end of its connection *)
              ; moved : cend -> num            (* bytes of the end's stream at its peer *)
              ; acked : cend -> num            (* of them, acknowledged to its process *)
              ; finned : cend -> bool          (* its FIN has reached its peer *)
              ; backlog : num -> num -> num    (* process k's queue limit on port p *) |>
End

Definition sys_chan_def:
  sys_chan s (k, j) = EL j (EL k s.procs).chans
End

Definition is_end_def:
  is_end s (k, j) ⇔ k < LENGTH s.procs ∧ j < LENGTH (EL k s.procs).chans
End

(* An arrival at process k (honestL0World's l0_deliver) *)
Definition sys_deliver_def:
  sys_deliver k a s =
    s with procs := LUPDATE (l0_deliver (EL k s.procs) a) k s.procs
End

(* Process k is alive and its first listener on port p (the one
   l0_deliver's LIncoming queues on) has room *)
Definition sys_room_def:
  sys_room s k p ⇔
    k < LENGTH s.procs ∧ s.alive k ∧
    case FILTER (λ(l, p', q). p' = p) (EL k s.procs).listeners of
    | (_, _, q) :: _ => LENGTH q < s.backlog k p
    | [] => F
End

(* End e's connect reaches k''s listener on port p: a new queued channel
   at k', and the two ends paired *)
Definition sys_pair_def:
  sys_pair e k' p s =
    let e' = (k', LENGTH (EL k' s.procs).chans);
        s1 = sys_deliver k' (LIncoming p) s in
      s1 with peer := (e =+ SOME e') ((e' =+ SOME e) s1.peer)
End

(* A blocking poll is answered as a non-blocking one, once it may return *)
Definition unblock_def:
  unblock nm (conf : word8 list) =
    if nm = «sys_poll» ∧ conf ≠ [] then 0w :: TL conf else conf
End

Definition poll_may_return_def:
  poll_may_return nm (conf : word8 list) (w : l0world) ⇔
    nm = «sys_poll» ∧ conf ≠ [] ∧ HD conf = 1w ⇒
    w.ch.transient w.hist ≠ NONE ∨ any_revents w (poll_entries (DROP 1 conf))
End

(* Exit: every fd of the process is closed (honestL0World's close_fd) *)
Definition close_all_def:
  close_all (w : l0world) =
    FOLDL (λw f. close_fd f w) w (MAP FST w.open_fds ++ MAP FST w.listeners)
End

(*---------------------------------------------------------------------------*)
(* The labels *)

Datatype:
  kstep = Handshake num num num            (* k j k' *)
        | Move num num num                 (* k j n *)
        | Ack num num num                  (* k j n *)
        | Fin num num                      (* k j *)
        | Break num num errcode bool       (* k j e keep *)
        | ConnFail num num errcode         (* k j e *)
End

Datatype:
  estep = EIncoming num num                (* k p *)
        | EConnUp num num                  (* k j *)
        | EArrive num l0_arrival           (* k a *)
End

Datatype:
  syslabel = Call num mlstring (word8 list) (word8 list) (word8 list)
                                           (* k, name, conf, bytes in, bytes out *)
           | Kern kstep
           | Env estep
           | Exit num
End

(* The channel an outside peer's arrival is on (only these three) *)
Definition env_arrival_chan_def:
  env_arrival_chan (LData j bs) = SOME j ∧
  env_arrival_chan (LEof j) = SOME j ∧
  env_arrival_chan (LDrain j n) = SOME j ∧
  env_arrival_chan _ = NONE
End

(*---------------------------------------------------------------------------*)
(* The steps *)

Definition sys_step_def:
  (sys_step s (Call k nm conf bytes out) s' ⇔
     k < LENGTH s.procs ∧ s.alive k ∧
     let w = EL k s.procs in
       poll_may_return nm conf w ∧
       ∃w1. l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
            let s1 = s with procs :=
                       LUPDATE (w1 with <| clock := w.clock + 1;
                                           hist := w.hist ++ [(nm, conf, bytes)] |>)
                               k s.procs in
              if nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1 then
                let e = (k, LENGTH w.chans);
                    s2 = s1 with target := (e =+ SOME (w22n conf)) s1.target;
                    c = EL (LENGTH w.chans) w1.chans in
                  if ¬c.connecting ∧ ¬c.broken then
                    (* connected at once: to a listener of the system, or outside *)
                    s' = s2 ∨ ∃k'. sys_room s2 k' (w22n conf) ∧ s' = sys_pair e k' (w22n conf) s2
                  else s' = s2
              else s' = s1) ∧
  (sys_step s (Kern (Handshake k j k')) s' ⇔
     is_end s (k, j) ∧ (sys_chan s (k, j)).connecting ∧ ¬(sys_chan s (k, j)).closed ∧
     ∃p. s.target (k, j) = SOME p ∧ sys_room s k' p ∧
         s' = sys_pair (k, j) k' p (sys_deliver k (LConnUp j) s)) ∧
  (sys_step s (Kern (Move k j n)) s' ⇔
     is_end s (k, j) ∧ 0 < n ∧ s.moved (k, j) + n ≤ LENGTH (sys_chan s (k, j)).sent ∧
     ∃k' j'. s.peer (k, j) = SOME (k', j') ∧
       s' = (sys_deliver k' (LData j' (TAKE n (DROP (s.moved (k, j)) (sys_chan s (k, j)).sent))) s)
              with moved := ((k, j) =+ s.moved (k, j) + n) s.moved) ∧
  (sys_step s (Kern (Ack k j n)) s' ⇔
     is_end s (k, j) ∧ s.peer (k, j) ≠ NONE ∧ s.acked (k, j) + n ≤ s.moved (k, j) ∧
     s' = (sys_deliver k (LDrain j n) s) with acked := ((k, j) =+ s.acked (k, j) + n) s.acked) ∧
  (sys_step s (Kern (Fin k j)) s' ⇔
     is_end s (k, j) ∧ (sys_chan s (k, j)).shut ∧ ¬s.finned (k, j) ∧
     s.moved (k, j) = LENGTH (sys_chan s (k, j)).sent ∧
     ∃k' j'. s.peer (k, j) = SOME (k', j') ∧
       s' = (sys_deliver k' (LEof j') s) with finned := ((k, j) =+ T) s.finned) ∧
  (sys_step s (Kern (Break k j e keep)) s' ⇔
     is_end s (k, j) ∧ s' = sys_deliver k (LBreak j e keep) s) ∧
  (sys_step s (Kern (ConnFail k j e)) s' ⇔
     is_end s (k, j) ∧ (sys_chan s (k, j)).connecting ∧
     s' = sys_deliver k (LConnFail j e) s) ∧
  (sys_step s (Env (EIncoming k p)) s' ⇔
     sys_room s k p ∧ s' = sys_deliver k (LIncoming p) s) ∧
  (sys_step s (Env (EConnUp k j)) s' ⇔
     is_end s (k, j) ∧ (sys_chan s (k, j)).connecting ∧
     s' = sys_deliver k (LConnUp j) s) ∧
  (sys_step s (Env (EArrive k a)) s' ⇔
     ∃j. env_arrival_chan a = SOME j ∧ is_end s (k, j) ∧ s.peer (k, j) = NONE ∧
         ¬(sys_chan s (k, j)).connecting ∧ s' = sys_deliver k a s) ∧
  (sys_step s (Exit k) s' ⇔
     k < LENGTH s.procs ∧ s.alive k ∧
     s' = s with <| alive := (k =+ F) s.alive;
                    procs := LUPDATE (close_all (EL k s.procs)) k s.procs |>)
End

(*---------------------------------------------------------------------------*)
(* The programs *)

(* The calls a run recorded, answered as recorded; any other call fails *)
Definition replay_oracle_def:
  replay_oracle (ExtCall n) (evs : io_event list) conf bytes =
    (case evs of
     | IO_event (ExtCall n') conf' bl :: rest =>
         if n' = n ∧ conf' = conf ∧ MAP FST bl = bytes
         then Oracle_return rest (MAP SND bl)
         else Oracle_final FFI_failed
     | _ => Oracle_final FFI_failed) ∧
  replay_oracle _ evs conf bytes = Oracle_final FFI_failed
End

Definition replay_ffi_def:
  replay_ffi evs = <| oracle := replay_oracle; ffi_state := evs; io_events := [] |>
End

(* The program, answered as recorded, makes exactly the calls evs (and then
   stops, is stopped, or computes without calling) *)
Definition prog_makes_def:
  prog_makes (prog : dec list) evs ⇔
    ∃b. semantics_prog (init_state (replay_ffi evs)) init_env prog b ∧
        case b of
        | Diverge io => io = fromList evs
        | Terminate _ io => io = evs
        | Fail => F
End

(* Process k's calls in a run, as I/O events *)
Definition proc_events_def:
  proc_events k [] = [] ∧
  proc_events k (Call k' nm conf bytes out :: rs) =
    (if k' = k then [IO_event (ExtCall nm) conf (ZIP (bytes, out))] else []) ++
    proc_events k rs ∧
  proc_events k (_ :: rs) = proc_events k rs
End

(*---------------------------------------------------------------------------*)
(* The run *)

(* One fresh L0 state per program: no listener, no channel; the reserved
   fds include 0 (the startup contract: fds 0-2 are open), and every fd in
   use is below the fd limit (the startup contract, as l0_server_world's
   fds_lt; user-approved 2026-10-17, design/45 §9 (d)); the choices
   satisfy honestL0Rely's rely *)
Definition sys_init_def:
  sys_init (S : dec list list) s ⇔
    LENGTH s.procs = LENGTH S ∧
    (∀k. k < LENGTH S ⇒
         let w = EL k s.procs in
           w.listeners = [] ∧ w.chans = [] ∧ w.open_fds = [] ∧ MEM 0w w.reserved ∧
           (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧
           w.clock = 0 ∧ w.hist = [] ∧ l0_rely w) ∧
    (∀k. s.alive k ⇔ k < LENGTH S) ∧
    s.target = K NONE ∧ s.peer = K NONE ∧ s.moved = K 0 ∧ s.acked = K 0 ∧
    s.finned = K F
End

(* The states a run passes through: ss = s0, s1, ..., one more than rs *)
Definition sys_steps_def:
  (sys_steps s [] ss ⇔ ss = [s]) ∧
  (sys_steps s (r :: rs) ss ⇔
     ∃s1 ss'. sys_step s r s1 ∧ sys_steps s1 rs ss' ∧ ss = s :: ss')
End

Definition l0sys_run_def:
  l0sys_run (S : dec list list) rs ⇔
    ∃s0 ss. sys_init S s0 ∧ sys_steps s0 rs ss ∧
            ∀k. k < LENGTH S ⇒ prog_makes (EL k S) (proc_events k rs)
End
