(*
  A model-level world of sockets, and the closed loop: a program and the
  world running together.

  The world mirrors the socket model of async/ffi-spike/ffiSpikeSocketFFI
  (branch spike/socket-model), so that the two layers line up for M4:
   - listening fds, each with a queue of pending connections;
   - connections, each an abstract byte stream: data that has arrived but
     not been read, whether the peer has closed its side, and everything
     written;
   - a schedule: the unpredictable future, a lazy list of steps, each a
     list of arrivals (a new connection, data, or the peer closing).
  Differences, recorded in design/09-closed-loop.md: fds are numbers and
  data are strings (not word64 / bytes); arrivals are named Connect /
  Arrive / Hangup (Data and Eof name responses here); a read returns all
  available data; each connection has a ghost field `received` (everything
  that ever arrived), against which the theorems are stated.

  The closed loop: in each round the program is polled with the history so
  far; the world performs the round's actions in order (their responses,
  in order, are the next snapshot's results); then time passes (the next
  step of the schedule arrives) and the next snapshot reports the ready
  fds.  This is the order of the socket model's sock_poll.
*)
Theory asyncWorld
Ancestors
  pair list rich_list arithmetic option pred_set string alist llist
  asyncCore asyncLevel1 asyncTranscript asyncServer
Libs
  BasicProvers

Datatype:
  arrival = Connect num num        (* Connect l c: connection c is pending
                                      on listener l *)
          | Arrive num string      (* data arrives on connection c *)
          | Hangup num             (* the peer of c closes its side *)
End

Datatype:
  conn = <| incoming : string ;    (* arrived, not yet read *)
            peer_closed : bool ;   (* EOF after the incoming data *)
            outgoing : string ;    (* everything written so far *)
            received : string |>   (* ghost: everything that arrived *)
End

Datatype:
  world = <| listeners : (num # num list) list ;
             conns : (num # conn) list ;
             sched : arrival list llist |>
End

Definition empty_conn_def:
  empty_conn = <| incoming := ""; peer_closed := F; outgoing := ""; received := "" |>
End

Definition is_listener_def:
  is_listener w fd ⇔ ALOOKUP w.listeners fd ≠ NONE
End

Definition is_conn_def:
  is_conn w fd ⇔ ALOOKUP w.conns fd ≠ NONE
End

(* One arrival.  As in the socket model, an arrival that makes no sense (a
   connection on a non-listener or reusing an fd, data after EOF) is
   dropped. *)
Definition deliver1_def:
  deliver1 w (Connect l c) =
    (if is_listener w l ∧ ¬is_listener w c ∧ ¬is_conn w c then
       w with <| listeners := AFUPDKEY l (λq. q ++ [c]) w.listeners;
                 conns := (c, empty_conn) :: w.conns |>
     else w) ∧
  deliver1 w (Arrive c d) =
    w with conns :=
      AFUPDKEY c (λcn. if cn.peer_closed then cn
                       else cn with <| incoming := cn.incoming ++ d;
                                       received := cn.received ++ d |>) w.conns ∧
  deliver1 w (Hangup c) =
    w with conns := AFUPDKEY c (λcn. cn with peer_closed := T) w.conns
End

Definition deliver_def:
  deliver w arrivals = FOLDL deliver1 w arrivals
End

(* Time passes: the next step of the schedule arrives *)
Definition tick_def:
  tick w =
    case LHD w.sched of
      NONE => w
    | SOME arrivals => deliver (w with sched := THE (LTL w.sched)) arrivals
End

Definition is_ready_def:
  is_ready w fd ⇔
    (case ALOOKUP w.listeners fd of SOME q => q ≠ [] | NONE => F) ∨
    (case ALOOKUP w.conns fd of
       SOME cn => cn.incoming ≠ "" ∨ cn.peer_closed
     | NONE => F)
End

(* ------------------------------------------------------------------------
   The world performs actions
   ------------------------------------------------------------------------ *)

Definition perform_def:
  perform (Accept l) w =
    (case ALOOKUP w.listeners l of
       SOME (c :: q) => (Accepted c, w with listeners := AFUPDKEY l (K q) w.listeners)
     | _ => (NoConn, w)) ∧
  perform (Read c) w =
    (case ALOOKUP w.conns c of
       SOME cn =>
         if cn.incoming ≠ "" then
           (Data cn.incoming,
            w with conns := AFUPDKEY c (λcn. cn with incoming := "") w.conns)
         else if cn.peer_closed then (Eof, w)
         else (WouldBlock, w)
     | NONE => (WouldBlock, w)) ∧
  perform (Write c d) w =
    (Written, w with conns := AFUPDKEY c (λcn. cn with outgoing := cn.outgoing ++ d) w.conns)
End

Definition perform_all_def:
  perform_all [] w = ([], w) ∧
  perform_all (a :: as) w =
    let (r, w1) = perform a w;
        (rs, w2) = perform_all as w1
    in (r :: rs, w2)
End

(* The ready fds, among the known ones (unknown fds are never ready) *)
Definition ready_fds_def:
  ready_fds w = FILTER (is_ready w) (MAP FST w.listeners ++ MAP FST w.conns)
End

Definition snapshot_of_def:
  snapshot_of w n rs =
    <| ready := set (MAP Readable (ready_fds w)); now := n; results := rs |>
End

(* ------------------------------------------------------------------------
   The closed loop
   ------------------------------------------------------------------------ *)

(* After n rounds: the history the program has seen, the world, and the log
   of performed actions with their responses *)
Definition closed_loop_def:
  closed_loop m w0 0 = ([], w0, []) ∧
  closed_loop m w0 (SUC n) =
    let (h, w, perf) = closed_loop m w0 n;
        acts = new_actions (log_of m) h;
        (rs, w1) = perform_all acts w;
        w2 = tick w1
    in (h ++ [snapshot_of w2 (SUC n) rs], w2, perf ++ ZIP (acts, rs))
End

(* A fresh world: one listener, no connections yet, and a schedule *)
Definition start_world_def:
  start_world lfd sch = <| listeners := [(lfd, [])]; conns := []; sched := sch |>
End
