(*
  THE ENDPOINT SOCKET WORLD (trusted; for the user's review).

  One program, many channels.  A channel is a byte stream to one remote
  peer, created either when a peer connects to one of the program's
  listeners (the program then accepts it) or when the program connects to
  an address.  Both kinds are read, written, polled, shut down and closed
  the same way: POSIX's view of sockets.  It subsumes the server worlds of
  version 1 (ffiSpikeSocketFFI) and version 2 (socketV2FFI): see
  endpointInstances.

  The ENVIRONMENT is REACTIVE: at each tick it chooses the next arrivals
  as a function of the calls the program has made so far (env).  A fixed
  schedule, as in versions 1 and 2, is the instance that ignores them.
  (So a peer can answer what the program sent.)

  As in version 2: channels are numbered 0, 1, 2, ... in order of
  creation; the kernel gives a new channel ANY free fd (alloc), and close
  frees it for reuse.
  New:
   - connect a: a new channel to address a, Connecting until the
     environment SETTLES it (Settle j b: Up if b, refused otherwise),
     whenever it chooses, as a kernel completes a handshake after any
     number of rounds (design/36 §4.1's LConnUp/LConnFail).  A refused
     channel has a PENDING ERROR (as the kernel's so_error): the next read
     or send on it reports ECONNREFUSED, and clears it; after that it
     reads as EOF and sends fail with EPIPE.  It keeps its fd until the
     program closes it (design/36 §4.1);
   - shutdown: the program closes its sending side (half-close);
   - backpressure, as a PARAMETER: the acceptance policy `takes` says how
     many of the bytes offered to channel j it accepts, given how many are
     still in flight (not yet read by the peer).  «sock_send» writes that
     many and returns the count; a channel is writable when it would
     accept a byte; the peer reading empties the buffer (Drain j).  The
     world without backpressure is the instance takes j b n = n;
   - the world supports a set of calls (calls); any other call fails.
*)
Theory endpointWorld
Ancestors
  cfHeapsBase cfFFIType llist alist ffiSpikeSocketFFI Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The model *)

Datatype:
  cstatus = Connecting | Up
          | Refused     (* refused; the error not yet reported *)
          | Failed      (* refused; the error reported *)
End

Datatype:
  chan = <| peer_addr : num option    (* the address connected to; NONE if accepted *)
          ; status : cstatus
          ; recv : word8 list         (* every byte the peer sent *)
          ; inbox : word8 list        (* ... of which not yet read *)
          ; peer_eof : bool           (* the peer has closed its side *)
          ; inflight : num            (* bytes sent, not yet read by the peer *)
          ; drained : num             (* how often the peer has read *)
          ; sent : word8 list         (* every byte the program sent *)
          ; shut : bool               (* the program shut its sending side *)
          ; closed : bool             (* the program closed its fd *) |>
End

Datatype:
  ep_arrival = Incoming num           (* a peer connects to the listener on address a *)
             | PData num (word8 list) (* the peer of channel j sends bytes *)
             | PEof num               (* the peer of channel j closes its side *)
             | Drain num              (* the peer of channel j reads all in flight *)
             | Settle num bool        (* channel j's connect completes: Up if T, refused if F *)
End

(* A call the program made: name, config, buffer in *)
Type call = “:mlstring # word8 list # word8 list”

Datatype:
  eworld = <| listening : (word64 # num # num list) list
                                          (* listener fd, its address, pending channels *)
            ; chans : chan list           (* channel j *)
            ; open_fds : (word64 # num) list   (* open channel fd, its channel *)
            ; reserved : word64 list      (* the process's other fds *)
            ; alloc : num -> word64 list -> word64     (* as version 2 *)
            ; takes : num -> num -> num -> num
                        (* bytes channel j accepts of n offered, b in flight *)
            ; calls : mlstring list       (* the calls the world supports *)
            ; env : num -> call list -> ep_arrival list
                        (* the arrivals of tick n, given the calls so far *)
            ; clock : num                 (* ticks so far *)
            ; hist : call list |>         (* the calls so far *)
End

Definition ep_used_def:
  ep_used w = w.reserved ++ MAP FST w.listening ++ MAP FST w.open_fds
End

Definition ep_chan_of_def:
  ep_chan_of w f =
    case ALOOKUP w.open_fds f of
    | SOME j => if j < LENGTH w.chans then SOME j else NONE
    | NONE => NONE
End

Definition upd_chan_def:
  upd_chan j g w = w with chans := LUPDATE (g (EL j w.chans)) j w.chans
End

Definition new_chan_def:
  new_chan pa st = <| peer_addr := pa; status := st; recv := []; inbox := [];
                      peer_eof := F; inflight := 0; drained := 0; sent := [];
                      shut := F; closed := F |>
End

(* One arrival; one that makes no sense is dropped (endpointFair's rely
   excludes them) *)
Definition ep_deliver_def:
  ep_deliver w (Incoming a) =
    (case FILTER (λ(l, a', q). a' = a) w.listening of
     | [] => w
     | (l, _, _) :: _ =>
         w with <| listening := AFUPDKEY l (λ(a, q). (a, q ++ [LENGTH w.chans])) w.listening
                 ; chans := w.chans ++ [new_chan NONE Up] |>) ∧
  ep_deliver w (PData j bs) =
    (if j < LENGTH w.chans ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).peer_eof
     then upd_chan j (λc. c with <| recv := c.recv ++ bs; inbox := c.inbox ++ bs |>) w
     else w) ∧
  ep_deliver w (PEof j) =
    (if j < LENGTH w.chans ∧ (EL j w.chans).status = Up
     then upd_chan j (λc. c with peer_eof := T) w else w) ∧
  ep_deliver w (Drain j) =
    (if j < LENGTH w.chans
     then upd_chan j (λc. c with <| inflight := 0; drained := c.drained + 1 |>) w else w) ∧
  ep_deliver w (Settle j b) =
    (if j < LENGTH w.chans ∧ (EL j w.chans).status = Connecting
     then upd_chan j (λc. c with status := if b then Up else Refused) w else w)
End

(* Time passes: the environment's next arrivals come *)
Definition ep_tick_def:
  ep_tick w = FOLDL ep_deliver (w with clock := w.clock + 1) (w.env w.clock w.hist)
End

Definition ep_readable_def:
  ep_readable w fd ⇔
    (case FILTER (λ(l, a, q). l = fd) w.listening of
     | (_, _, q) :: _ => q ≠ []
     | [] => F) ∨
    (case ep_chan_of w fd of
     | SOME j => (EL j w.chans).inbox ≠ [] ∨ (EL j w.chans).peer_eof ∨
                 (EL j w.chans).status = Refused ∨ (EL j w.chans).status = Failed
     | NONE => F)
End

Definition ep_writable_def:
  ep_writable w fd ⇔
    case ep_chan_of w fd of
    | SOME j => (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧
                0 < w.takes j (EL j w.chans).inflight 1 ∨
                (EL j w.chans).status = Refused ∨ (EL j w.chans).status = Failed
    | NONE => F
End

(* The operations; NONE: misuse, on which the FFI call fails *)

Definition ep_alloc_def:
  ep_alloc w j =
    if LENGTH (ep_used w) < dimword (:64) then
      let f = w.alloc j (ep_used w) in SOME (f, w with open_fds := (f, j) :: w.open_fds)
    else NONE
End

Definition ep_accept_def:
  ep_accept l w =
    case FILTER (λ(l', a, q). l' = l) w.listening of
    | [] => NONE
    | (_, a, []) :: _ => SOME (NONE, w)
    | (_, a, j :: q) :: _ =>
        case ep_alloc w j of
        | NONE => SOME (NONE, w)
        | SOME (f, w') => SOME (SOME f, w' with listening := AFUPDKEY l (K (a, q)) w'.listening)
End

Definition ep_connect_def:
  ep_connect a w =
    case ep_alloc (w with chans := w.chans ++ [new_chan (SOME a) Connecting])
                  (LENGTH w.chans) of
    | NONE => (NONE, w)
    | SOME (f, w') => (SOME f, w')
End

Definition ep_read_def:
  ep_read f n w =
    case ep_chan_of w f of
    | NONE => NONE
    | SOME j =>
        let c = EL j w.chans in
          if c.inbox ≠ [] then
            SOME (SOME (TAKE n c.inbox), upd_chan j (λc. c with inbox := DROP n c.inbox) w)
          else if c.peer_eof ∨ c.status = Failed then SOME (SOME [], w)
          else SOME (NONE, w)
End

(* Send what the policy accepts; the count *)
Definition ep_send_def:
  ep_send f bs w =
    case ep_chan_of w f of
    | NONE => NONE
    | SOME j =>
        let c = EL j w.chans;
            k = if c.status = Up ∧ ¬c.shut
                then MIN (LENGTH bs) (w.takes j c.inflight (LENGTH bs)) else 0 in
          SOME (k, upd_chan j (λc. c with <| sent := c.sent ++ TAKE k bs;
                                             inflight := c.inflight + k |>) w)
End

(* A refused channel's pending error, reported (and so cleared) *)
Definition ep_conn_err_def:
  ep_conn_err f w =
    case ep_chan_of w f of
    | SOME j => if (EL j w.chans).status = Refused
                then SOME (upd_chan j (λc. c with status := Failed) w) else NONE
    | NONE => NONE
End

(* The channel of f can no longer send: shut, or refused (reported) *)
Definition ep_broken_def:
  ep_broken f w ⇔
    case ep_chan_of w f of
    | SOME j => (EL j w.chans).shut ∨ (EL j w.chans).status = Failed
    | NONE => F
End

Definition ep_shutdown_def:
  ep_shutdown f w =
    case ep_chan_of w f of
    | NONE => NONE
    | SOME j => SOME (upd_chan j (λc. c with shut := T) w)
End

Definition ep_close_def:
  ep_close f w =
    case ep_chan_of w f of
    | NONE => NONE
    | SOME j => SOME (upd_chan j (λc. c with <| shut := T; closed := T |>)
                        (w with open_fds := ADELKEY f w.open_fds))
End

(*---------------------------------------------------------------------------*)
(* The FFI calls.  «sock_poll», «sock_accept», «sock_read», «sock_write»,
   «sock_close»: version 1's and 2's encodings («sock_write» is a full
   write; one that does not fit is a misuse), except that «sock_read» on a
   refused channel returns status 3 (error) with the error code in byte 1
   (4: ECONNREFUSED).  New: «sock_send» (partial write), «sock_writable»
   (writability; time does not pass), «sock_connect» (conf: the 8-byte
   address), «sock_shutdown» (conf: the fd).
   «sock_send» and «sock_connect» answer design/36's 13-byte L0 header
   (l0_result): a code (0: OK, 1: EAGAIN, 3: EINPROGRESS, 4: ECONNREFUSED,
   6: EPIPE, 10: EMFILE), an 8-byte value, and 4 bytes of errno (0 here:
   the model does not fix the raw errno).  A connect is always pending
   (code 3, with the fd) or finds no free fd (code 10). *)

Definition l0_result_def:
  l0_result (code:num) v = n2w code :: n2w8 v ++ [0w; 0w; 0w; 0w] : word8 list
End


Definition ep_call_def:
  ep_call n (conf:word8 list) (bytes:word8 list) w =
    if ¬MEM n w.calls then NONE
    else if n = «sock_poll» then
      (if LENGTH conf = 8 * LENGTH bytes then
         SOME (MAP (λfd. if ep_readable (ep_tick w) fd then 1w else 0w) (bytes_fds conf),
               ep_tick w)
       else NONE)
    else if n = «sock_writable» then
      (if LENGTH conf = 8 * LENGTH bytes then
         SOME (MAP (λfd. if ep_writable w fd then 1w else 0w) (bytes_fds conf), w)
       else NONE)
    else if n = «sock_accept» then
      (if LENGTH conf = 8 ∧ LENGTH bytes = 9 then
         case ep_accept (bytes_fd conf) w of
         | NONE => NONE
         | SOME (NONE, w') => SOME (0w :: TL bytes, w')
         | SOME (SOME c, w') => SOME (1w :: fd_bytes c, w')
       else NONE)
    else if n = «sock_connect» then
      (if LENGTH conf = 8 ∧ LENGTH bytes = 13 then
         case ep_connect (w82n conf) w of
         | (NONE, w') => SOME (l0_result 10 0, w')
         | (SOME c, w') => SOME (l0_result 3 (w2n c), w')
       else NONE)
    else if n = «sock_read» then
      (if LENGTH conf = 8 ∧ 9 < LENGTH bytes then
         case ep_conn_err (bytes_fd conf) w of
         | SOME w' => SOME (3w :: 4w :: DROP 2 bytes, w')
         | NONE =>
         case ep_read (bytes_fd conf) (LENGTH bytes - 9) w of
         | NONE => NONE
         | SOME (NONE, w') => SOME (1w :: TL bytes, w')
         | SOME (SOME d, w') =>
             if d = [] then SOME (2w :: TL bytes, w')
             else SOME (0w :: n2w8 (LENGTH d) ++ d ++ DROP (9 + LENGTH d) bytes, w')
       else NONE)
    else if n = «sock_write» then
      (if 8 ≤ LENGTH conf then
         case ep_send (bytes_fd (TAKE 8 conf)) (DROP 8 conf) w of
         | SOME (k, w') => if k = LENGTH conf − 8 then SOME (bytes, w') else NONE
         | NONE => NONE
       else NONE)
    else if n = «sock_send» then
      (if 8 ≤ LENGTH conf ∧ LENGTH bytes = 13 then
         case ep_conn_err (bytes_fd (TAKE 8 conf)) w of
         | SOME w' => SOME (l0_result 4 0, w')
         | NONE =>
         if ep_broken (bytes_fd (TAKE 8 conf)) w then SOME (l0_result 6 0, w)
         else
         case ep_send (bytes_fd (TAKE 8 conf)) (DROP 8 conf) w of
         | SOME (k, w') =>
             if k = 0 ∧ 8 < LENGTH conf then SOME (l0_result 1 0, w')
             else SOME (l0_result 0 k, w')
         | NONE => NONE
       else NONE)
    else if n = «sock_shutdown» then
      (if LENGTH conf = 8 then
         case ep_shutdown (bytes_fd conf) w of
         | SOME w' => SOME (bytes, w')
         | NONE => NONE
       else NONE)
    else if n = «sock_close» then
      (if LENGTH conf = 8 then
         case ep_close (bytes_fd conf) w of
         | SOME w' => SOME (bytes, w')
         | NONE => NONE
       else NONE)
    else NONE
End

(* A call, recorded in the history the environment sees *)
Definition ep_ffi_fn_def:
  ep_ffi_fn n conf bytes w =
    case ep_call n conf bytes w of
    | SOME (bytes', w') => SOME (bytes', w' with hist := w.hist ++ [(n, conf, bytes)])
    | NONE => NONE
End

Definition ep_oracle_def:
  ep_oracle (ExtCall n) (w:eworld) conf bytes =
    (case ep_ffi_fn n conf bytes w of
     | SOME (bytes', w') => Oracle_return w' bytes'
     | NONE => Oracle_final FFI_failed) ∧
  ep_oracle _ w conf bytes = Oracle_final FFI_failed
End

Definition ep_ffi_def:
  ep_ffi w = <| oracle := ep_oracle; ffi_state := w; io_events := [] |>
End
