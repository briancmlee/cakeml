(*
  EchoSpec2: what the echo server does in a world where connections are
  closed and fds are REUSED.  A companion of EchoSpec (unchanged), for the
  user's review.

  To believe a theorem  echo_spec2 3w prog, a reader needs this file and
  the version-2 socket world it imports (socket-v2/socketV2FFI and the
  assumption sched_wf2 in socket-v2/socketV2Fair), plus EchoSpec's
  per-fd projections of raw I/O events, which are reused here.

  What changes from EchoSpec:
   - The world (socketV2FFI): clients numbered in order of connection;
     the kernel gives an accepted connection the lowest free fd; a fifth
     call, «sock_close», frees an fd for reuse.
   - The projections are per EPISODE, not per fd.  Episode j is the life
     of the j-th accepted connection: from the accept that returned its fd
     f to the following close of f.  Its bytes read and written are the
     reads and writes on f during that time.  So a later connection that
     reuses f is a different episode.
   - With one listener, the j-th accept takes the j-th client to connect
     (accept takes the oldest pending client), so liveness is stated per
     client: everything client j sends is eventually written back in
     episode j.
   - A third clause, echo_closes2: once the server has read the EOF of an
     episode's client, it eventually closes the episode's fd (so a server
     that never closes, and so never frees an fd, does not meet the spec).
  Safety and liveness have EchoSpec's shape, per episode.

  Nothing here is proved; echo_spec2 is a definition.
  EchoSpec2BiteScript.sml shows that it rules out plausible bugs, including
  the new one: data of a previous connection on a reused fd reaching the
  new client.
*)
Theory EchoSpec2
Ancestors
  semantics ffi llist ml_prog ffiSpikeSocketFFI EchoSpec socketV2FFI
  socketV2Fair
Libs
  preamble

(* ------------------------------------------------------------------------
   The world: a sockets-only FFI, driven by the version-2 socket model
   ------------------------------------------------------------------------ *)

Definition socket2_fn_def:
  socket2_fn n =
    if n = «sock_poll» then SOME ffi_sock_poll2
    else if n = «sock_accept» then SOME ffi_sock_accept2
    else if n = «sock_read» then SOME ffi_sock_read2
    else if n = «sock_write» then SOME ffi_sock_write2
    else if n = «sock_close» then SOME ffi_sock_close2
    else NONE
End

Definition socket2_oracle_def:
  socket2_oracle (ExtCall n) (sk:sockets2) conf bytes =
    (case socket2_fn n of
     | SOME f =>
         (case f conf bytes sk of
          | SOME (FFIreturn bytes' sk') => Oracle_return sk' bytes'
          | _ => Oracle_final FFI_failed)
     | NONE => Oracle_final FFI_failed) ∧
  socket2_oracle _ sk conf bytes = Oracle_final FFI_failed
End

Definition socket2_ffi_def:
  socket2_ffi sk = <| oracle := socket2_oracle; ffi_state := sk; io_events := [] |>
End

(* The worlds the server is run in: one listener lfd with nothing pending,
   no clients and no open connections yet, any other fds of the process,
   a kernel that gives new connections free fds (any allocation policy),
   and a fair schedule. *)
Definition server_world2_def:
  server_world2 lfd sk ⇔
    sk.listening = [(lfd, [])] ∧ sk.clients = [] ∧ sk.open_fds = [] ∧
    alloc_ok sk.alloc ∧ sched_wf2 sk
End

(* ------------------------------------------------------------------------
   Episodes
   ------------------------------------------------------------------------ *)

(* The fd an accept event returned: the buffer came back as status 1, then
   the 8-byte fd *)
Definition event_accepted_def:
  event_accepted (IO_event (ExtCall n) conf bytes) =
    (let out = MAP SND bytes in
     if n = «sock_accept» ∧ LENGTH out = 9 ∧ HD out = 1w
     then SOME (bytes_fd (TL out)) else NONE) ∧
  event_accepted _ = NONE
End

(* The fd a close event closed: the config is the 8-byte fd *)
Definition event_closed_def:
  event_closed (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_close» ∧ LENGTH conf = 8 then SOME (bytes_fd conf) else NONE) ∧
  event_closed _ = NONE
End

(* The fds of the accepted connections, in order: episode j's fd is the
   j-th *)
Definition accepted_fds_def:
  accepted_fds evs =
    FLAT (MAP (λev. case event_accepted ev of SOME f => [f] | NONE => []) evs)
End

(* The events during episode j: those that happen while it is open, i.e.
   after the j-th accept and up to the following close of its fd.  k counts
   the accepts so far; opn maps each open fd to its episode. *)
Definition ep_events_def:
  ep_events (j:num) (k:num) (opn : (word64 # num) list) [] = [] ∧
  ep_events j k opn (ev :: evs) =
    (if MEM j (MAP SND opn) then [ev] else []) ++
    (case event_accepted ev of
     | SOME f => ep_events j (k + 1) ((f, k) :: ADELKEY f opn) evs
     | NONE =>
         case event_closed ev of
         | SOME f => ep_events j k (ADELKEY f opn) evs
         | NONE => ep_events j k opn evs)
End

(* The fd a read event that returned EOF read: status 2 *)
Definition event_eof_def:
  event_eof (IO_event (ExtCall n) conf bytes) =
    (let out = MAP SND bytes in
     if n = «sock_read» ∧ LENGTH conf = 8 ∧ out ≠ [] ∧ HD out = 2w
     then SOME (bytes_fd conf) else NONE) ∧
  event_eof _ = NONE
End

(* In a finite trace, the program read the EOF of episode j's fd, while
   episode j was open *)
Definition ep_eof_read_def:
  ep_eof_read j evs ⇔
    j < LENGTH (accepted_fds evs) ∧
    EXISTS (λev. event_eof ev = SOME (EL j (accepted_fds evs))) (ep_events j 0 [] evs)
End

(* In a finite trace, episode j ended: the program closed its fd while it
   was open *)
Definition ep_closed_def:
  ep_closed j evs ⇔
    j < LENGTH (accepted_fds evs) ∧
    EXISTS (λev. event_closed ev = SOME (EL j (accepted_fds evs))) (ep_events j 0 [] evs)
End

(* What the program read in / wrote in episode j of a finite trace: the
   reads and writes on its fd while it is open *)
Definition ep_read_def:
  ep_read j evs =
    if j < LENGTH (accepted_fds evs) then
      bytes_read_from (EL j (accepted_fds evs)) (ep_events j 0 [] evs)
    else []
End

Definition ep_written_def:
  ep_written j evs =
    if j < LENGTH (accepted_fds evs) then
      bytes_written_to (EL j (accepted_fds evs)) (ep_events j 0 [] evs)
    else []
End

(* ------------------------------------------------------------------------
   What the clients send
   ------------------------------------------------------------------------ *)

Definition arrivals2_upto_def:
  arrivals2_upto 0 sched = [] ∧
  arrivals2_upto (SUC n) sched =
    case LHD sched of
    | NONE => []
    | SOME step => step ++ arrivals2_upto n (THE (LTL sched))
End

(* The data client j sends in the first n steps *)
Definition sent2_upto_def:
  sent2_upto j n sk =
    FLAT (MAP (λa. case a of Data2 j' bs => if j' = j then bs else [] | _ => [])
              (arrivals2_upto n sk.future))
End

(* ------------------------------------------------------------------------
   The specification
   ------------------------------------------------------------------------ *)

(* Safety: at every point of the run, in every episode, the server has
   written back a prefix of what it has read in that episode. *)
Definition echo_safe2_def:
  echo_safe2 io ⇔
    ∀evs j. LPREFIX (fromList evs) io ⇒ ep_written j evs ≼ ep_read j evs
End

(* Liveness: everything client j sends is eventually written back, in its
   episode (the j-th accepted connection). *)
Definition echo_live2_def:
  echo_live2 sk io ⇔
    ∀j n. ∃evs. LPREFIX (fromList evs) io ∧ sent2_upto j n sk ≼ ep_written j evs
End

(* Closing: once the program has read the EOF of episode j's client, it
   eventually closes episode j's fd. *)
Definition echo_closes2_def:
  echo_closes2 io ⇔
    ∀evs j. LPREFIX (fromList evs) io ∧ ep_eof_read j evs ⇒
            ∃evs'. LPREFIX (fromList evs') io ∧ ep_closed j evs'
End

(* THE STATEMENT: in every fair version-2 world with one listener lfd, the
   program runs forever, and its I/O trace is safe and live in every
   episode, and closes every episode whose client has closed. *)
Definition echo_spec2_def:
  echo_spec2 lfd (prog : dec list) ⇔
    ∀sk. server_world2 lfd sk ⇒
         ∃io. semantics_prog (init_state (socket2_ffi sk)) init_env prog
                (Diverge io) ∧
              echo_safe2 io ∧ echo_live2 sk io ∧ echo_closes2 io
End
