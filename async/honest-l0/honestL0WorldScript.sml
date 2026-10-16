(*
  THE L0 SOCKET WORLD (trusted; design/36 §4, for the user's review).

  The model of async/runnable/l0/socket_ffi_l0.c together with the kernel,
  ANCHORED ON THE STANDARDS:
    [P]  POSIX.1-2024 (IEEE Std 1003.1-2024, Base Specifications Issue 8),
         XSH: send(), recv(), accept(), poll(), close(), shutdown(),
         listen(), bind(), socket(); 2.6 File Descriptor Allocation;
         2.10.7 Socket I/O Mode; 2.10.14 Signals.
    [T]  RFC 9293 (TCP), and RFC 1122 §4.2.2.13.
  Rules (design/36 §4.3):
   - where a standard is specific, the model follows it;
   - where it is loose or silent, the model is NONDETERMINISTIC: the world
     chooses (the fields of lchoices; specs quantify over all of them), so
     every permitted behaviour is a model behaviour;
   - where a real platform does something the standard forbids, the model
     allows it too, as a documented PLATFORM EXTENSION, marked [X..];
   - the few constraints the standards do not give but the model assumes
     are marked [A..]; the conformance tests check them on each platform.
  The honesty criterion (design/36 D1): every behaviour of the real C plus
  kernel is a behaviour of this model (a sound over-approximation).

  TIME (design/36 D3): the kernel changes state at any moment, so before
  EVERY call the environment delivers arrivals (env sees the calls so far
  and the name of the call about to be made).  A blocking poll lets further
  steps pass until something is ready.

  A CHANNEL is one connection, numbered 0, 1, ... in order of arrival.  Its
  peer is the environment: it sends data (LData), closes its sending side
  (LEof, a FIN), breaks the connection (LBreak: a reset, a timeout, an
  unreachable host), and reads what the program sent (LDrain).

  What a channel records:
   - inbox      : arrived, not yet read
   - peer_sent  : everything the peer sent (for specs)
   - peer_eof   : the peer closed its sending side
   - err        : the pending socket error (SO_ERROR), reported once
   - broken     : the connection is gone; sticky
   - shut       : the program shut its sending side
   - sent       : every byte the kernel accepted from the program
   - inflight   : accepted, not yet read by the peer
   - drained    : how often the peer has read
   - closed     : the program closed its fd
   - aborted    : the program closed it while received data was pending,
                  or data arrived after the close: TCP SHOULD then send a
                  RST [T §3.6.1, SHLD-3], and the peer may lose bytes in
                  flight.  (A flag meaning MAY have been aborted.)

  Calls fail (NONE; the C exits) only on the C's misuse checks: buffer
  lengths, a poll block flag other than 0/1, an fd above 2^31 - 1; and
  (unchecked by the C, a precondition on the verified caller) a poll entry
  requesting events other than POLLIN, POLLOUT.  Every other outcome is a
  result.  sys_poll (D20) polls the caller's buffer in place: after the
  13-byte header and 3 pad bytes, k struct pollfd entries (fd int32, events
  int16, revents int16, little-endian; POLLIN 1, POLLOUT 4, POLLERR 8,
  POLLHUP 16, POLLNVAL 32: the C's build-time-checked ABI assumption); no
  limit on k ([P poll] EINVAL above OPEN_MAX and ENOMEM are among the
  transient errors).
*)
Theory honestL0World
Ancestors
  ffi llist alist mlstring Marshalling honestL0 ffiSpikeSocketFFI
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The state *)

Datatype:
  lchan = <| inbox : word8 list
           ; peer_sent : word8 list
           ; peer_eof : bool
           ; err : errcode option
           ; broken : bool
           ; shut : bool
           ; sent : word8 list
           ; inflight : num
           ; drained : num
           ; closed : bool
           ; aborted : bool
           ; connecting : bool |>
End

Datatype:
  l0_arrival = LIncoming num              (* a peer connects to the listener on port p *)
             | LData num (word8 list)     (* the peer of channel j sends bytes *)
             | LEof num                   (* the peer of channel j closes its side *)
             | LBreak num errcode bool    (* channel j breaks with error e (ECONNRESET,
                                             ETIMEDOUT, ...); T: the unread input is
                                             kept, F: flushed.  [T §3.10.7.4]: "All
                                             segment queues should be flushed"
                                             (lowercase, not BCP 14): either *)
             | LDrain num num             (* the peer of channel j reads k bytes *)
             | LConnUp num                (* channel j's pending connect completes *)
             | LConnFail num errcode      (* channel j's pending connect fails with e
                                             (ECONNREFUSED, ETIMEDOUT, ENETUNREACH, ...):
                                             the socket's pending error [P connect] *)
End

(* A call: name, configuration, buffer in *)
Type lcall = “:mlstring # word8 list # word8 list”

(* The world's choices, each a function of the calls so far *)
Datatype:
  lchoices =
    <| takes : num -> lcall list -> num -> num -> num
          (* how many of n bytes channel j accepts with b in flight: [P 2.10.7]
             "transfer only as much as is available"; the space is the kernel's *)
     ; short : num -> lcall list -> num -> num
          (* how many of the a available bytes recv returns ([P recv]: data
             "as soon as it becomes available"; no segment boundary is visible) *)
     ; transient : lcall list -> errcode option
          (* the call fails at once with EINTR / ENOBUFS / ENOMEM / ENFILE
             (each in the call's [P] error list; EINTR only with a caught
             signal, which the startup contract does not install) *)
     ; errno_of : lcall list -> word8 list      (* the raw errno bytes (opaque) *)
     ; listen_fails : lcall list -> (num # errcode) option
          (* sys_listen fails at step k (1..5) with e: bind's EADDRINUSE,
             EACCES, ... [P bind, listen, socket] *)
     ; emfile_drops : lcall list -> bool
          (* accept failed with EMFILE: the pending connection is dropped
             and its peer reset (macOS), or stays queued (Linux).  [P accept]
             says nothing: either *)
     ; accept_aborts : lcall list -> errcode option
          (* SOME e: the first pending connection, which has broken, is
             dropped with e: ECONNABORTED [P accept, shall], EPROTO [may],
             or [X3] Linux's pending network errors; NONE: it is returned *)
     ; send_pending : lcall list -> bool
          (* send on a broken channel with a pending error reports it and
             clears it (T), or fails otherwise and keeps it (F; macOS) *)
     ; broken_send : lcall list -> errcode
          (* send's error on a broken channel otherwise: EPIPE "no longer
             connected" [P send], ECONNRESET, ENOTCONN, ... *)
     ; broken_recv : lcall list -> errcode option
          (* recv on a broken channel once its error was reported: 0 (EOF;
             macOS, Linux) or an error again.  [P] is silent: either *)
     ; show_err : lcall list -> num -> bool
          (* POLLERR shown.  [P poll] REQUIRES it for every condition a
             read or write would report with -1; [X1] macOS (and Linux after
             SHUT_WR) omit it, so the model lets the world omit it *)
     ; show_hup : lcall list -> num -> bool
          (* POLLHUP shown: [P poll] defines it for devices, pipes and FIFOs
             only, so for sockets it is the world's choice, but [A1] only
             after the peer's EOF, a break, or the program's own shutdown
             (macOS shows it after SHUT_WR alone: random conformance test) *)
     ; show_out : lcall list -> num -> bool
          (* POLLOUT on a shut or broken channel (a send would not block:
             it fails) *)
     ; shut_err : lcall list -> errcode option
          (* shutdown of a broken or already shut channel: ENOTCONN "The
             socket is not connected" [P shutdown] (macOS, once both sides
             have sent FIN), or success *)
     ; close_intr : lcall list -> (bool # errcode) option
          (* close interrupted [P close]: "unspecified whether it returns -1
             with errno set to [EINTR] and fildes remaining open (F), or ...
             [EINPROGRESS] and fildes being closed (T)" *)
     ; misuse : lcall list -> errcode           (* a call on an fd of the wrong kind *)
     ; reserved_rev : lcall list -> word64 -> word8   (* poll flags of a reserved fd *)
     ; poll_junk : lcall list -> num -> word8
          (* byte i of a failed poll's revents fields: [P poll] does not say
             what revents holds when poll fails *)
     ; connect_now : lcall list -> errcode option option
          (* connect's immediate outcome [P connect]: NONE: EINPROGRESS ("If the
             connection cannot be established immediately and O_NONBLOCK is set
             ... shall fail and set errno to [EINPROGRESS] ... the connection
             shall be established asynchronously"); SOME NONE: connected at once;
             SOME (SOME e): failed at once with e (ECONNREFUSED: "The target
             address was not listening for connections or refused"), after which
             "the state of the socket is unspecified": the model breaks it *)
     ; pending_err : lcall list -> mlstring -> errcode
          (* recv, send, shutdown on a socket whose connect is pending: [P] says
             only ENOTCONN "not connected" for send/shutdown, and recv's
             "connection-mode socket not connected"; Linux answers EAGAIN to recv
             and send: either (the world's choice, per call name) *)
     |>
End

Datatype:
  l0world = <| listeners : (word64 # num # num list) list
                             (* listener fd, its port, pending channels *)
             ; chans : lchan list
             ; open_fds : (word64 # num) list   (* open channel fd, its channel *)
             ; reserved : word64 list           (* the process's other open fds *)
             ; fd_limit : num                   (* RLIMIT_NOFILE (soft) *)
             ; ch : lchoices
             ; env : num -> lcall list -> mlstring -> l0_arrival list
                             (* the arrivals of step n, given the calls so far
                                and the call about to be made *)
             ; clock : num
             ; hist : lcall list |>
End

Definition l0_used_def:
  l0_used w = w.reserved ++ MAP FST w.listeners ++ MAP FST w.open_fds
End

Definition l0_chan_of_def:
  l0_chan_of w f =
    case ALOOKUP w.open_fds f of
    | SOME j => if j < LENGTH w.chans then SOME j else NONE
    | NONE => NONE
End

Definition is_listener_fd_def:
  is_listener_fd w f ⇔ MEM f (MAP FST w.listeners)
End

Definition upd_lchan_def:
  upd_lchan j g w = w with chans := LUPDATE (g (EL j w.chans)) j w.chans
End

Definition fresh_lchan_def:
  fresh_lchan = <| inbox := []; peer_sent := []; peer_eof := F; err := NONE;
                   broken := F; shut := F; sent := []; inflight := 0;
                   drained := 0; closed := F; aborted := F; connecting := F |>
End

(*---------------------------------------------------------------------------*)
(* Arrivals *)

(* The connection breaks with error e (reported once by the next recv or
   send, [T §3.10.7.4] "connection reset" responses) *)
Definition break_lchan_def:
  break_lchan e keep c =
    if c.broken then c
    else c with <| broken := T; err := SOME e;
                   inbox := if keep then c.inbox else [] |>
End

(* One arrival; one that makes no sense (an unknown port or channel) is
   dropped.  Data after the peer's EOF or after a break is dropped; data
   arriving at a channel the program has closed makes TCP answer with RST
   [T §3.6.1] (aborted). *)
Definition l0_deliver_def:
  l0_deliver w (LIncoming p) =
    (case FILTER (λ(l, p', q). p' = p) w.listeners of
     | [] => w
     | (l, _, _) :: _ =>
         w with <| listeners := AFUPDKEY l (λ(p, q). (p, q ++ [LENGTH w.chans])) w.listeners
                 ; chans := w.chans ++ [fresh_lchan] |>) ∧
  l0_deliver w (LData j bs) =
    (if j < LENGTH w.chans ∧ ¬(EL j w.chans).peer_eof ∧ ¬(EL j w.chans).broken ∧
        ¬(EL j w.chans).connecting then
       upd_lchan j (λc. if c.closed then c with aborted := T
                        else c with <| inbox := c.inbox ++ bs;
                                       peer_sent := c.peer_sent ++ bs |>) w
     else w) ∧
  l0_deliver w (LEof j) =
    (if j < LENGTH w.chans ∧ ¬(EL j w.chans).broken ∧ ¬(EL j w.chans).connecting
     then upd_lchan j (λc. c with peer_eof := T) w else w) ∧
  l0_deliver w (LBreak j e keep) =
    (if j < LENGTH w.chans then upd_lchan j (break_lchan e keep) w else w) ∧
  l0_deliver w (LDrain j k) =
    (if j < LENGTH w.chans
     then upd_lchan j (λc. c with <| inflight := c.inflight − k;
                                     drained := c.drained + 1 |>) w
     else w) ∧
  l0_deliver w (LConnUp j) =
    (if j < LENGTH w.chans ∧ (EL j w.chans).connecting
     then upd_lchan j (λc. c with connecting := F) w else w) ∧
  l0_deliver w (LConnFail j e) =
    (if j < LENGTH w.chans ∧ (EL j w.chans).connecting
     then upd_lchan j (λc. c with <| connecting := F; broken := T; err := SOME e |>) w
     else w)
End

(* One step of time, before a call named nm *)
Definition l0_tick_def:
  l0_tick nm w =
    FOLDL l0_deliver (w with clock := w.clock + 1) (w.env w.clock w.hist nm)
End

Definition l0_ticks_def:
  l0_ticks nm 0 w = w ∧
  l0_ticks nm (SUC n) w = l0_ticks nm n (l0_tick nm w)
End

(*---------------------------------------------------------------------------*)
(* Readiness [P poll].  The revents of one fd for the requested events
   (bit 1 IN, bit 2 OUT).  ERR, HUP and NVAL are reported whether requested
   or not ("shall set the POLLHUP, POLLERR, and POLLNVAL flag in revents if
   the condition is true, even if the application did not set the
   corresponding bit in events").  POLLIN: "data other than high-priority
   data may be read without blocking": a recv would not fail with EAGAIN.
   [P poll] makes POLLHUP and POLLOUT mutually exclusive; [X2] Linux reports
   both after a reset, so the model does not exclude it. *)

Definition no_revents_def:
  no_revents = <| rin := F; rout := F; rerr := F; rhup := F; rnval := F |>
End

Definition chan_revents_def:
  chan_revents w j (ev : num) =
    let c = EL j w.chans; h = w.hist in
      if c.connecting then no_revents   (* "ready for writing" only once
                                             established [P connect] *)
      else
      <| rin := (ODD ev ∧ (c.inbox ≠ [] ∨ c.peer_eof ∨ c.broken ∨ c.err ≠ NONE));
         rout := (2 ≤ ev MOD 4 ∧
                  (if c.broken ∨ c.shut then w.ch.show_out h j
                   else 0 < w.ch.takes j h c.inflight 1));
         rerr := ((c.err ≠ NONE ∨ c.broken ∨ c.shut) ∧ w.ch.show_err h j);
         rhup := ((c.broken ∨ c.peer_eof ∨ c.shut) ∧ w.ch.show_hup h j);
         rnval := F |>
End

(* POLLNVAL: "The specified fd value is not an open file descriptor" *)
Definition fd_revents_def:
  fd_revents w (f, ev) =
    case l0_chan_of w f of
    | SOME j => revents_byte (chan_revents w j ev)
    | NONE =>
        case FILTER (λ(l, p, q). l = f) w.listeners of
        | (_, _, q) :: _ => revents_byte (no_revents with rin := (ODD ev ∧ q ≠ []))
        | [] =>
            if MEM f w.reserved then w.ch.reserved_rev w.hist f
            else revents_byte (no_revents with rnval := T)
End

(* revents for a poll entry (fd, events): [P poll] "If the value of fd is less than 0, events
   shall be ignored, and revents shall be set to 0" *)
Definition pfd_revents_def:
  pfd_revents w (f, ev) = if 2 ** 31 ≤ w2n f then 0w else fd_revents w (f, ev)
End

Definition any_revents_def:
  any_revents w fes ⇔ EXISTS (λfe. pfd_revents w fe ≠ 0w) fes
End

(* A blocking poll ("block indefinitely until at least one descriptor
   meets the specified criteria"): how many more steps pass; NONE: never *)
Definition l0_wait_def:
  l0_wait fes w =
    if ∃n. any_revents (l0_ticks «sys_poll» n w) fes then
      SOME (LEAST n. any_revents (l0_ticks «sys_poll» n w) fes)
    else NONE
End

(*---------------------------------------------------------------------------*)
(* File descriptor allocation [P 2.6]: "All functions that open one or more
   file descriptors shall, unless specified otherwise, atomically allocate
   the lowest numbered available ... file descriptor"; accept() and socket()
   refer to it.  EMFILE when that fd is not below the limit. *)

Definition lowest_fd_def:
  lowest_fd w : word64 = n2w (LEAST n. ¬MEM (n2w n : word64) (l0_used w))
End

Definition l0_alloc_def:
  l0_alloc w = if w2n (lowest_fd w) < w.fd_limit then SOME (lowest_fd w) else NONE
End

(*---------------------------------------------------------------------------*)
(* The operations, after the step of time that precedes the call *)

Definition fail_def:
  fail w e = Fail e (w.ch.errno_of w.hist)
End

(* The error for an fd that is not a channel: EBADF if it is not open at
   all, else the world's choice (ENOTCONN, ENOTSOCK, EINVAL, ...) *)
Definition not_chan_def:
  not_chan w f =
    if is_listener_fd w f ∨ MEM f w.reserved then fail w (w.ch.misuse w.hist)
    else fail w E_BADF
End

(* sys_listen: socket, setsockopt, bind, listen, fcntl; a listener on the
   port, or the failing step and its error (the socket is closed again) *)
Definition l0_listen_def:
  l0_listen p w =
    case w.ch.listen_fails w.hist of
    | SOME (k, e) => (INR (k, e), w)
    | NONE =>
        case l0_alloc w of
        | NONE => (INR (1, E_MFILE), w)
        | SOME f => (INL f, w with listeners := w.listeners ++ [(f, p, [])])
End

(* accept [P accept]: the first pending connection on a new fd [P 2.6];
   EAGAIN if there is none; EMFILE if no fd is available *)
Definition l0_accept_def:
  l0_accept l w =
    case FILTER (λ(l', p, q). l' = l) w.listeners of
    | [] => (fail w (if l0_chan_of w l ≠ NONE ∨ MEM l w.reserved
                     then w.ch.misuse w.hist else E_BADF), w)
    | (_, p, q) :: _ =>
        case w.ch.transient w.hist of
        | SOME e => (fail w e, w)
        | NONE =>
            case q of
            | [] => (fail w E_AGAIN, w)
            | j :: q' =>
                let pop = w with listeners := AFUPDKEY l (K (p, q')) w.listeners in
                  case (if (EL j w.chans).broken then w.ch.accept_aborts w.hist else NONE) of
                  | SOME e => (fail w e, pop)
                  | NONE =>
                      case l0_alloc w of
                      | NONE =>
                          if w.ch.emfile_drops w.hist
                          then (fail w E_MFILE, upd_lchan j (break_lchan E_CONNRESET F) pop)
                          else (fail w E_MFILE, w)
                      | SOME f => (Ok (w2n f), pop with open_fds := (f, j) :: pop.open_fds)
End

(* recv of at most n bytes [P recv]: data; 0 "if no messages are available
   to be received and the peer has performed an orderly shutdown"; the
   pending error; EAGAIN with nothing to read (MSG_DONTWAIT, [X4]) *)
Definition l0_recv_def:
  l0_recv f n w =
    case l0_chan_of w f of
    | NONE => (not_chan w f, [], w)
    | SOME j =>
        case w.ch.transient w.hist of
        | SOME e => (fail w e, [], w)
        | NONE =>
            let c = EL j w.chans in
              if c.connecting then (fail w (w.ch.pending_err w.hist «sys_recv»), [], w)
              else if c.inbox ≠ [] then
                let k = MIN n (w.ch.short j w.hist (LENGTH c.inbox)) in
                  (Ok k, TAKE k c.inbox,
                   upd_lchan j (λc. c with inbox := DROP k c.inbox) w)
              else
                case c.err of
                | SOME e => (fail w e, [], upd_lchan j (λc. c with err := NONE) w)
                | NONE =>
                    if c.broken then
                      (case w.ch.broken_recv w.hist of
                       | NONE => (Ok 0, [], w)
                       | SOME e => (fail w e, [], w))
                    else if c.peer_eof then (Ok 0, [], w)
                    else (fail w E_AGAIN, [], w)
End

(* send [P send, 2.10.7]: the count the kernel accepts ("only as much as is
   available"), EAGAIN if no byte fits, EPIPE if shut down for writing, or
   an error on a broken connection.  Sending after the peer's EOF is
   permitted [T §3.6.1]. *)
Definition l0_send_def:
  l0_send f bs w =
    case l0_chan_of w f of
    | NONE => (not_chan w f, w)
    | SOME j =>
        case w.ch.transient w.hist of
        | SOME e => (fail w e, w)
        | NONE =>
            let c = EL j w.chans in
              if c.connecting then (fail w (w.ch.pending_err w.hist «sys_send»), w)
              else if c.broken then
                (case c.err of
                 | SOME e =>
                     if w.ch.send_pending w.hist
                     then (fail w e, upd_lchan j (λc. c with err := NONE) w)
                     else (fail w (w.ch.broken_send w.hist), w)
                 | NONE => (fail w (w.ch.broken_send w.hist), w))
              else if c.shut then (fail w E_PIPE, w)
              else
                let k = MIN (LENGTH bs) (w.ch.takes j w.hist c.inflight (LENGTH bs)) in
                  if k = 0 ∧ bs ≠ [] then (fail w E_AGAIN, w)
                  else (Ok k, upd_lchan j (λc. c with <| sent := c.sent ++ TAKE k bs;
                                                         inflight := c.inflight + k |>) w)
End

(* shutdown(SHUT_WR) [P shutdown]: "Disables further send operations" *)
Definition l0_shutdown_def:
  l0_shutdown f w =
    case l0_chan_of w f of
    | NONE => (not_chan w f, w)
    | SOME j =>
        case w.ch.transient w.hist of
        | SOME e => (fail w e, w)
        | NONE =>
            if (EL j w.chans).connecting then
              (fail w (w.ch.pending_err w.hist «sys_shutdown»), w)
            else if (EL j w.chans).broken ∨ (EL j w.chans).shut then
              (case w.ch.shut_err w.hist of
               | SOME e => (fail w e, w)
               | NONE => (Ok 0, upd_lchan j (λc. c with shut := T) w))
            else (Ok 0, upd_lchan j (λc. c with shut := T) w)
End

(* close [P close]: the fd is free again.  A channel closed while received
   data is pending may be aborted [T §3.6.1].  Closing a listener drops
   (and resets) its pending connections; closing a reserved fd frees it.
   An interrupted close leaves the fd open or closes it (close_intr). *)
(* connect [P connect] to 127.0.0.1:p: a new socket (the lowest free fd,
   [P 2.6]; EMFILE if none is below the limit), made non-blocking, then
   connected; the result and the value: the new fd (also when connect then
   fails: the socket stays open until closed); value 0: no socket (fd 0 is
   always open, by the startup contract, so it is never a new fd).  The
   peer is the environment: whether and when the connect completes is its
   choice (connect_now, LConnUp, LConnFail); a connect to one of the
   program's own listeners also arrives there as LIncoming, also the
   environment's choice (the model does not link the two ends; every real
   pairing is a behaviour) *)
Definition l0_connect_def:
  l0_connect (p : num) w =
    case w.ch.transient w.hist of
    | SOME e => (fail w e, 0n, w)
    | NONE =>
        case l0_alloc w of
        | NONE => (fail w E_MFILE, 0, w)
        | SOME f =>
            let j = LENGTH w.chans;
                w1 = w with <| chans := w.chans ++ [fresh_lchan with connecting := T];
                               open_fds := (f, j) :: w.open_fds |> in
              case w.ch.connect_now w.hist of
              | NONE => (fail w E_INPROGRESS, w2n f, w1)
              | SOME NONE => (Ok (w2n f), w2n f, upd_lchan j (λc. c with connecting := F) w1)
              | SOME (SOME e) =>
                  (fail w e, w2n f,
                   upd_lchan j (λc. c with <| connecting := F; broken := T |>) w1)
End

(* getsockopt(SO_ERROR): the pending error, which reading clears; SOME e:
   the pending error; NONE: none (Ok) *)
Definition l0_connerr_def:
  l0_connerr f w =
    case l0_chan_of w f of
    | NONE => (INR (not_chan w f), w)
    | SOME j =>
        case (EL j w.chans).err of
        | SOME e => (INL (SOME e), upd_lchan j (λc. c with err := NONE) w)
        | NONE => (INL NONE, w)
End

Definition close_fd_def:
  close_fd f w =
    case l0_chan_of w f of
    | SOME j =>
        upd_lchan j (λc. c with <| shut := T; closed := T;
                                   aborted := (c.aborted ∨ c.inbox ≠ []) |>)
          (w with open_fds := ADELKEY f w.open_fds)
    | NONE =>
        case FILTER (λ(l, p, q). l = f) w.listeners of
        | (_, _, q) :: _ =>
            FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w)
              (w with listeners := FILTER (λ(l, p, q). l ≠ f) w.listeners) q
        | [] => w with reserved := FILTER ($≠ f) w.reserved
End

Definition l0_close_def:
  l0_close f w =
    if MEM f (l0_used w) then
      case w.ch.close_intr w.hist of
      | SOME (gone, e) => (fail w e, if gone then close_fd f w else w)
      | NONE => (Ok 0, close_fd f w)
    else (fail w E_BADF, w)
End

(*---------------------------------------------------------------------------*)
(* The FFI calls: socket_ffi_l0.c's byte encodings *)

Definition l0_hdr_def:
  l0_hdr = 13n
End

(* An fd the C accepts: at most INT_MAX *)
Definition fd_ok_def:
  fd_ok (f : word64) ⇔ w2n f < 2 ** 31
End

(* sys_listen's failure: the step is in the value field *)
(* A result with error e and value v (sys_connect's fd, sys_connerr's 1) *)
Definition enc_err_val_def:
  enc_err_val w e (v : num) = n2w (err_code e) :: n2w8 v ++ w.ch.errno_of w.hist
End

Definition enc_listen_fail_def:
  enc_listen_fail w (k, e) = n2w (err_code e) :: n2w8 k ++ w.ch.errno_of w.hist
End

(* sys_poll's buffer (D20): 16 bytes (the header's 13, 3 pad), then
   8-byte struct pollfd entries *)
Definition pollfd_entries_def:
  pollfd_entries (bs : word8 list) =
    if LENGTH bs < 8 then [] else TAKE 8 bs :: pollfd_entries (DROP 8 bs)
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rw[LENGTH_DROP]
End

(* An entry's fd (int32, little-endian; 2^31 and above: negative) and
   requested events (int16) *)
Definition pe_fd_def:
  pe_fd (e : word8 list) : word64 =
    n2w (w2n (EL 0 e) + 256 * w2n (EL 1 e) + 65536 * w2n (EL 2 e) +
         16777216 * w2n (EL 3 e))
End

Definition pe_events_def:
  pe_events (e : word8 list) = w2n (EL 4 e) + 256 * w2n (EL 5 e)
End

(* Only POLLIN (1) and POLLOUT (4) may be requested *)
Definition pe_ok_def:
  pe_ok e ⇔ pe_events e = 0 ∨ pe_events e = 1 ∨ pe_events e = 4 ∨ pe_events e = 5
End

(* The entry as (fd, events) with the model's events bits (1 IN, 2 OUT) *)
Definition pe_fe_def:
  pe_fe e = (pe_fd e, (if ODD (pe_events e) then 1 else 0) +
                      (if 4 ≤ pe_events e then 2 else 0n))
End

(* The model's revents byte (1 IN 2 OUT 4 ERR 8 HUP 16 NVAL) as the int16
   revents field (POLLIN 1, POLLOUT 4, POLLERR 8, POLLHUP 16, POLLNVAL 32) *)
Definition abi_rev_def:
  abi_rev (b : word8) =
    let r = byte_revents b in
      [n2w ((if r.rin then 1 else 0) + (if r.rout then 4 else 0) +
            (if r.rerr then 8 else 0) + (if r.rhup then 16 else 0) +
            (if r.rnval then 32 else 0)) : word8; 0w]
End

(* A completed poll: the count, the pad bytes as they were, each entry's fd
   and events as they were and its revents *)
Definition poll_out_def:
  poll_out w (bytes : word8 list) =
    let ents = pollfd_entries (DROP 16 bytes) in
      enc_res (Ok (LENGTH (FILTER (λe. pfd_revents w (pe_fe e) ≠ 0w) ents))) ++
      TAKE 3 (DROP 13 bytes) ++
      FLAT (MAP (λe. TAKE 6 e ++ abi_rev (pfd_revents w (pe_fe e))) ents)
End

(* A failed poll: revents unspecified *)
Definition poll_failed_def:
  poll_failed w e (bytes : word8 list) =
    let ents = pollfd_entries (DROP 16 bytes) in
      enc_res (fail w e) ++ TAKE 3 (DROP 13 bytes) ++
      FLAT (MAPi (λi en. TAKE 6 en ++ [w.ch.poll_junk w.hist (2 * i);
                                        w.ch.poll_junk w.hist (2 * i + 1)]) ents)
End

Definition l0_call_def:
  l0_call n (conf : word8 list) (bytes : word8 list) (w : l0world) =
    if n = «sys_listen» then
      (if LENGTH conf = 2 ∧ LENGTH bytes = l0_hdr then
         case l0_listen (w22n conf) w of
         | (INL f, w') => SOME (FFIreturn (enc_res (Ok (w2n f))) w')
         | (INR ke, w') => SOME (FFIreturn (enc_listen_fail w ke) w')
       else NONE)
    else if n = «sys_poll» then
      (let ents = pollfd_entries (DROP 16 bytes); fes = MAP pe_fe ents in
       if LENGTH conf = 1 ∧ w2n (HD conf) ≤ 1 ∧ 16 ≤ LENGTH bytes ∧
          (LENGTH bytes − 16) MOD 8 = 0 ∧ EVERY pe_ok ents
       then
         case w.ch.transient w.hist of
         | SOME e => SOME (FFIreturn (poll_failed w e bytes) w)
         | NONE =>
             if HD conf = 0w then SOME (FFIreturn (poll_out w bytes) w)
             else
               case l0_wait fes w of
               | NONE => SOME FFIdiverge
               | SOME k => SOME (FFIreturn (poll_out (l0_ticks «sys_poll» k w) bytes)
                                           (l0_ticks «sys_poll» k w))
       else NONE)
    else if n = «sys_accept» then
      (if LENGTH conf = 8 ∧ LENGTH bytes = l0_hdr ∧ fd_ok (bytes_fd conf) then
         let (r, w') = l0_accept (bytes_fd conf) w in SOME (FFIreturn (enc_res r) w')
       else NONE)
    else if n = «sys_recv» then
      (if LENGTH conf = 8 ∧ l0_hdr < LENGTH bytes ∧ fd_ok (bytes_fd conf) then
         let (r, d, w') = l0_recv (bytes_fd conf) (LENGTH bytes − l0_hdr) w in
           SOME (FFIreturn (enc_res r ++ d ++ DROP (l0_hdr + LENGTH d) bytes) w')
       else NONE)
    else if n = «sys_send» then
      (if 8 ≤ LENGTH conf ∧ LENGTH bytes = l0_hdr ∧ fd_ok (bytes_fd (TAKE 8 conf)) then
         let (r, w') = l0_send (bytes_fd (TAKE 8 conf)) (DROP 8 conf) w in
           SOME (FFIreturn (enc_res r) w')
       else NONE)
    else if n = «sys_shutdown» then
      (if LENGTH conf = 8 ∧ LENGTH bytes = l0_hdr ∧ fd_ok (bytes_fd conf) then
         let (r, w') = l0_shutdown (bytes_fd conf) w in SOME (FFIreturn (enc_res r) w')
       else NONE)
    else if n = «sys_connect» then
      (if LENGTH conf = 2 ∧ LENGTH bytes = l0_hdr then
         case l0_connect (w22n conf) w of
         | (Ok v, _, w') => SOME (FFIreturn (enc_res (Ok v)) w')
         | (Fail e _, v, w') => SOME (FFIreturn (enc_err_val w e v) w')
       else NONE)
    else if n = «sys_connerr» then
      (if LENGTH conf = 8 ∧ LENGTH bytes = l0_hdr ∧ fd_ok (bytes_fd conf) then
         case l0_connerr (bytes_fd conf) w of
         | (INL NONE, w') => SOME (FFIreturn (enc_res (Ok 0)) w')
         | (INL (SOME e), w') => SOME (FFIreturn (enc_err_val w e 1) w')
         | (INR r, w') => SOME (FFIreturn (enc_res r) w')
       else NONE)
    else if n = «sys_close» then
      (if LENGTH conf = 8 ∧ LENGTH bytes = l0_hdr ∧ fd_ok (bytes_fd conf) then
         let (r, w') = l0_close (bytes_fd conf) w in SOME (FFIreturn (enc_res r) w')
       else NONE)
    else NONE
End

(* A call: first a step of time, then the call; it is recorded in the
   history the world's choices and environment see *)
Definition l0_ffi_fn_def:
  l0_ffi_fn n conf bytes w =
    case l0_call n conf bytes (l0_tick n w) of
    | SOME (FFIreturn bytes' w') =>
        SOME (FFIreturn bytes' (w' with hist := w.hist ++ [(n, conf, bytes)]))
    | r => r
End

Definition l0_oracle_def:
  l0_oracle (ExtCall n) (w : l0world) conf bytes =
    (case l0_ffi_fn n conf bytes w of
     | SOME (FFIreturn bytes' w') => Oracle_return w' bytes'
     | SOME FFIdiverge => Oracle_final FFI_diverged
     | NONE => Oracle_final FFI_failed) ∧
  l0_oracle _ w conf bytes = Oracle_final FFI_failed
End

Definition l0_ffi_def:
  l0_ffi w = <| oracle := l0_oracle; ffi_state := w; io_events := [] |>
End
