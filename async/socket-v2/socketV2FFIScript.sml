(*
  The socket world, version 2: connections can be closed, and fds are
  REUSED after a close.  This is the world of EchoSpec2; it extends the
  version-1 model (ffiSpikeSocketFFI) as follows.

  - Clients are numbered 0, 1, 2, ... in the order they connect.  The
    schedule talks about clients, not fds: Connect2 l (a new client
    connects to listener l), Data2 j bs, Eof2 j.  In version 1 the
    schedule chose each connection's fd in advance, which cannot model
    reuse (the fd a client gets depends on what the program has closed).
  - The fd is chosen by the kernel when the program accepts: the LOWEST
    fd not in use (as POSIX accept does), where "in use" means one of the
    process's other fds (reserved, e.g. 0, 1, 2), a listener, or an open
    connection.  So after the program closes fd f, the next accepted
    connection may get f again.
  - A fifth call, «sock_close», closes a connection fd.  The client's byte
    stream stays in the world (data it still sends is never read).

  Everything else is version 1's: honest reads (data, would-block, EOF),
  full writes, and time advancing only at «sock_poll», by one step of the
  schedule.
*)
Theory socketV2FFI
Ancestors
  cfHeapsBase cfFFIType llist alist ffiSpikeSocketFFI Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The model *)

Datatype:
  arrival2 = Connect2 word64           (* a new client connects to listener l;
                                          clients are numbered 0, 1, 2, ...
                                          in order of connection *)
           | Data2 num (word8 list)    (* client j sends bytes *)
           | Eof2 num                  (* client j closes its side *)
End

(* A client's byte stream is version 1's conn: unread incoming bytes, EOF
   after them, everything the server wrote *)
Datatype:
  sockets2 = <| listening : (word64 # num list) list
                                          (* listener, its pending clients *)
              ; clients : conn list       (* client j's stream, j = 0, 1, ... *)
              ; open_fds : (word64 # num) list
                                          (* open connection fd, its client *)
              ; reserved : word64 list    (* the process's other fds *)
              ; future : arrival2 list llist
              |>
End

(* The fds in use *)
Definition used_fds_def:
  used_fds s = s.reserved ++ MAP FST s.listening ++ MAP FST s.open_fds
End

(* The lowest fd not in a list *)
Definition lowest_free_def:
  lowest_free (used : word64 list) : word64 =
    n2w (LEAST n. ¬MEM (n2w n : word64) used)
End

Definition client_of_def:
  client_of s f =
    case ALOOKUP s.open_fds f of
    | SOME j => if j < LENGTH s.clients then SOME j else NONE
    | NONE => NONE
End

Definition update_client_def:
  update_client j g s = s with clients := LUPDATE (g (EL j s.clients)) j s.clients
End

(* One arrival; one that makes no sense (a connection to a non-listener,
   data or EOF from an unknown client, data after EOF) is dropped; the
   assumption sched_wf2 (socketV2Fair) excludes such schedules. *)
Definition deliver2_def:
  deliver2 s (Connect2 l) =
    (if ALOOKUP s.listening l ≠ NONE then
       s with <| listening := AFUPDKEY l (λq. q ++ [LENGTH s.clients]) s.listening
               ; clients := s.clients ++ [empty_conn] |>
     else s) ∧
  deliver2 s (Data2 j bs) =
    (if j < LENGTH s.clients ∧ ¬(EL j s.clients).peer_closed then
       update_client j (λcn. cn with incoming := cn.incoming ++ bs) s
     else s) ∧
  deliver2 s (Eof2 j) =
    (if j < LENGTH s.clients then
       update_client j (λcn. cn with peer_closed := T) s
     else s)
End

(* Time passes: the next step of the schedule arrives *)
Definition tick2_def:
  tick2 s =
    case LHD s.future of
    | NONE => s
    | SOME arrivals => FOLDL deliver2 (s with future := THE (LTL s.future)) arrivals
End

(* A listener with a pending client, or an open connection with unread data
   or EOF *)
Definition is_ready2_def:
  is_ready2 s fd ⇔
    (case ALOOKUP s.listening fd of SOME q => q ≠ [] | NONE => F) ∨
    (case client_of s fd of
     | SOME j => (EL j s.clients).incoming ≠ [] ∨ (EL j s.clients).peer_closed
     | NONE => F)
End

(* The five operations.  NONE: misuse (an fd of the wrong kind), on which
   the FFI call fails. *)

Definition sock_poll2_def:
  sock_poll2 fds s = (FILTER (is_ready2 (tick2 s)) fds, tick2 s)
End

(* accept: the oldest pending client, on the lowest free fd; NONE (would
   block) if there is no pending client, or no free fd *)
Definition sock_accept2_def:
  sock_accept2 l s =
    case ALOOKUP s.listening l of
    | NONE => NONE
    | SOME [] => SOME (NONE, s)
    | SOME (j::q) =>
        if LENGTH (used_fds s) < dimword (:64) then
          let f = lowest_free (used_fds s) in
            SOME (SOME f, s with <| listening := AFUPDKEY l (K q) s.listening
                                  ; open_fds := (f, j) :: s.open_fds |>)
        else SOME (NONE, s)
End

Definition sock_read2_def:
  sock_read2 f n s =
    case client_of s f of
    | NONE => NONE
    | SOME j =>
        let cn = EL j s.clients in
          if cn.incoming ≠ [] then
            SOME (SOME (TAKE n cn.incoming),
                  update_client j (λcn. cn with incoming := DROP n cn.incoming) s)
          else if cn.peer_closed then SOME (SOME [], s)
          else SOME (NONE, s)
End

Definition sock_write2_def:
  sock_write2 f bs s =
    case client_of s f of
    | NONE => NONE
    | SOME j => SOME (update_client j (λcn. cn with outgoing := cn.outgoing ++ bs) s)
End

(* close: the fd is free again *)
Definition sock_close2_def:
  sock_close2 f s =
    case client_of s f of
    | NONE => NONE
    | SOME j => SOME (s with open_fds := ADELKEY f s.open_fds)
End

(*---------------------------------------------------------------------------*)
(* The FFI functions: version 1's encodings, plus «sock_close» *)

Definition ffi_sock_poll2_def:
  ffi_sock_poll2 (conf:word8 list) (bytes:word8 list) s =
    if LENGTH conf = 8 * LENGTH bytes then
      SOME (FFIreturn (MAP (λfd. if is_ready2 (tick2 s) fd then 1w else 0w)
                           (bytes_fds conf)) (tick2 s))
    else NONE
End

Definition ffi_sock_accept2_def:
  ffi_sock_accept2 (conf:word8 list) (bytes:word8 list) s =
    if LENGTH conf = 8 ∧ LENGTH bytes = 9 then
      case sock_accept2 (bytes_fd conf) s of
      | NONE => NONE
      | SOME (NONE, s') => SOME (FFIreturn (0w :: TL bytes) s')
      | SOME (SOME c, s') => SOME (FFIreturn (1w :: fd_bytes c) s')
    else NONE
End

Definition ffi_sock_read2_def:
  ffi_sock_read2 (conf:word8 list) (bytes:word8 list) s =
    if LENGTH conf = 8 ∧ 9 < LENGTH bytes then
      case sock_read2 (bytes_fd conf) (LENGTH bytes - 9) s of
      | NONE => NONE
      | SOME (NONE, s') => SOME (FFIreturn (1w :: TL bytes) s')
      | SOME (SOME d, s') =>
          if d = [] then SOME (FFIreturn (2w :: TL bytes) s')
          else SOME (FFIreturn (0w :: n2w8 (LENGTH d) ++ d ++
                                DROP (9 + LENGTH d) bytes) s')
    else NONE
End

Definition ffi_sock_write2_def:
  ffi_sock_write2 (conf:word8 list) (bytes:word8 list) s =
    if 8 ≤ LENGTH conf then
      case sock_write2 (bytes_fd (TAKE 8 conf)) (DROP 8 conf) s of
      | NONE => NONE
      | SOME s' => SOME (FFIreturn bytes s')
    else NONE
End

(* «sock_close»: conf is the connection; bytes are not used. *)
Definition ffi_sock_close2_def:
  ffi_sock_close2 (conf:word8 list) (bytes:word8 list) s =
    if LENGTH conf = 8 then
      case sock_close2 (bytes_fd conf) s of
      | NONE => NONE
      | SOME s' => SOME (FFIreturn bytes s')
    else NONE
End
