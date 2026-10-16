(*
  The link from the lifetimes world (close and fd reuse; socketV2FFI,
  EchoSpec2) down to the core world (ffiSpikeSocketFFI, EchoSpec): the
  theorem the lifetimes level opens with.  STATEMENT FIRST, for review.

  A program that never closes a connection, and touches only the listener
  and the fds it has accepted, behaves in a lifetimes world sk exactly as
  in one core world, core_of sk: the same behaviour, the same I/O trace.
  Both directions: a core run with these properties (which L0's results
  give, e.g. fd discipline) is a run in the lifetimes world, and
  conversely.

  core_of sk: without closes, the fd the kernel gives the j-th accept is
  determined (core_fd sk j: the allocation function applied to the fds
  then in use: the process's own, the listener, and the j earlier
  accepts).  The core world's schedule is the lifetimes schedule with
  client j's connection on that fd from the moment it connects
  (Connect2 l becomes Connect l (core_fd sk n) for the n-th client;
  Data2 j / Eof2 j are on core_fd sk j).

  Why the two hypotheses on the run:
  - no «sock_close»: the core world has no close;
  - only the listener and accepted fds: the core world knows a
    connection's fd as soon as it connects (it can be polled or read
    before it is accepted), the lifetimes world only after the accept.
  Both are properties of the run, checked on its I/O events (and the call
  that ends it, if any); every server of the series meets them.
*)
Theory lifetimeCore
Ancestors
  llist ffi semantics ml_prog ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec
  socketV2FFI socketV2Fair EchoSpec2
Libs
  preamble

(* ------------------------------------------------------------------------
   The core world of a lifetimes world
   ------------------------------------------------------------------------ *)

(* The fds of the first j accepts, newest first, when nothing is closed *)
Definition core_fds_def:
  core_fds sk 0 = [] ∧
  core_fds sk (SUC j) =
    sk.alloc j (sk.reserved ++ MAP FST sk.listening ++ core_fds sk j) :: core_fds sk j
End

(* The fd of client j's connection *)
Definition core_fd_def:
  core_fd sk j = HD (core_fds sk (SUC j))
End

(* An arrival, and a step of arrivals, with n clients connected so far *)
Definition core_arrival_def:
  core_arrival sk n (Connect2 l) = Connect l (core_fd sk n) ∧
  core_arrival sk n (Data2 j bs) = Data (core_fd sk j) bs ∧
  core_arrival sk n (Eof2 j) = Eof (core_fd sk j)
End

Definition is_connect2_def:
  is_connect2 (Connect2 l) = T ∧
  is_connect2 _ = F
End

Definition core_step_def:
  core_step sk n [] = [] ∧
  core_step sk n (a :: as) =
    core_arrival sk n a :: core_step sk (if is_connect2 a then n + 1 else n) as
End

Definition core_sched_def:
  core_sched sk n ll =
    LUNFOLD (λ(n, ll). case LHD ll of
                       | NONE => NONE
                       | SOME st => SOME ((n + LENGTH (FILTER is_connect2 st), THE (LTL ll)),
                                          core_step sk n st))
            (n, ll)
End

Definition core_of_def:
  core_of sk =
    <| listeners := MAP (λ(l, q). (l, MAP (core_fd sk) q)) sk.listening;
       conns := [];
       sched := core_sched sk (LENGTH sk.clients) sk.future |>
End

(* ------------------------------------------------------------------------
   The runs the link is about
   ------------------------------------------------------------------------ *)

(* The fds a socket call names *)
Definition call_fds_def:
  call_fds (ExtCall n) conf =
    (if n = «sock_poll» then bytes_fds conf
     else if n = «sock_accept» ∨ n = «sock_read» then [bytes_fd conf]
     else if n = «sock_write» then [bytes_fd (TAKE 8 conf)]
     else []) ∧
  call_fds _ conf = []
End

(* After the events evs, a call is allowed: it is not a close, and it names
   only the listener and fds that evs accepted *)
Definition call_ok_def:
  call_ok lfd evs n conf ⇔
    n ≠ ExtCall «sock_close» ∧
    EVERY (λf. f = lfd ∨ MEM f (accepted_fds evs)) (call_fds n conf)
End

Definition calls_ok_def:
  calls_ok lfd evs ⇔
    ∀pre n conf bytes rest.
      evs = pre ++ [IO_event n conf bytes] ++ rest ⇒ call_ok lfd pre n conf
End

(* Every call of the behaviour is allowed (and it is not a failure, whose
   calls the behaviour does not record) *)
Definition run_ok_def:
  run_ok lfd (Diverge io) = (∀evs. LPREFIX (fromList evs) io ⇒ calls_ok lfd evs) ∧
  run_ok lfd (Terminate out io) =
    (calls_ok lfd io ∧
     case out of
     | FFI_outcome (Final_event n conf bytes res) => call_ok lfd io n conf
     | _ => T) ∧
  run_ok lfd Fail = F
End

(* ------------------------------------------------------------------------
   THE LINK (statement; the theorem to prove is lifetime_core_link)
   ------------------------------------------------------------------------ *)

Definition lifetime_core_link_def:
  lifetime_core_link ⇔
    ∀lfd sk.
      server_world2 lfd sk ⇒
      server_world lfd (core_of sk) ∧
      ∀prog b.
        run_ok lfd b ⇒
        (semantics_prog (init_state (socket_ffi (core_of sk))) init_env prog b ⇔
         semantics_prog (init_state (socket2_ffi sk)) init_env prog b)
End
