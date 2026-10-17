(*
  HTTP and KV on the honest L0 world: SAFETY STATEMENTS, DRAFT for the
  user's decision (P4, design/46).  Nothing here is proved; the claims are
  definitions.

  TRUSTED SURFACE: this file; honestEchoL0Spec (the raw-trace vocabulary
  the user approved for echo: l0_accepted, l0_read, l0_sent,
  l0_server_world, the episodes); HttpSpecBodies (requests, their grammar
  and printer, responses) and HttpKvSpec (the store, kv_run, replies,
  earlier, reply_bytes), reused unchanged.

  They are the approved version-2 statements (HttpSpecBodies2's
  http_safe_b2, HttpKvSpec2's kv_safe2) moved onto the raw L0 trace, as
  echo_safe_l0 moved echo2_safe:
   - episode j's bytes read are l0_read j (what the kernel's recv calls
     returned during episode j); the bytes written are l0_sent j (what the
     kernel TOOK from the send calls: what the client can receive);
   - an episode lasts from the j-th successful accept to the first
     successful close of its fd (an accept that reuses the fd also ends it:
     honestEchoL0Bites' l0_ep_events_reuse);
   - as for echo, the claim is made while fewer than 2^64 - 1 connections
     have been accepted (the loop stops when the handles run out, user
     decision D25; honestEchoL0NoGuard shows echo needs no such guard, and
     the guard's removal is with the user);
   - the program listens on its port first; if the listen fails it stops
     after that one event;
   - topology (for the moonshot's composition, step 12 T7/T8): every
     successful sys_listen is on the configured port, and the program makes
     no sys_connect.
  Liveness is not stated here: it waits for the liveness transfer
  (async-spike / R1-live), as for echo.
*)
Theory honestHttpKvL0Spec
Ancestors
  llist ffi honestL0 honestL0World honestEchoL0Spec HttpSpecBodies HttpKvSpec rich_list
Libs
  preamble

(* ------------------------------------------------------------------------
   HTTP (with request bodies)
   ------------------------------------------------------------------------ *)

(* Safety: at every point of the run, in every episode, if what the kernel
   has handed the server so far is some complete requests rs followed by a
   partial one, then what the kernel has taken from the server is a prefix
   of the responses to rs *)
Definition http_safe_l0_def:
  http_safe_l0 files io ⇔
    ∀evs j rs rest.
      LPREFIX (fromList evs) io ∧ LENGTH (l0_accepted evs) < 2 ** 64 − 1 ∧
      EVERY valid_brequest rs ∧ l0_read j evs = brequests rs ++ rest ∧
      no_full_brequest rest ⇒
      l0_sent j evs ≼ bresponses files rs
End

(* ------------------------------------------------------------------------
   KV (linearizable, across connections)
   ------------------------------------------------------------------------ *)

(* rss j: the complete requests read in episode j so far; (j, i) names the
   i-th of them.  An order lists each exactly once, each episode's in their
   own order (HttpKvSpec2's is_order2) *)
Definition is_order_l0_def:
  is_order_l0 (rss : num -> brequest list) (order : (num # num) list) ⇔
    ∀j. MAP SND (FILTER (λx. FST x = j) order) = COUNT_LIST (LENGTH (rss j))
End

(* Real time: at some point evs1 of the trace evs, the kernel had taken
   the whole response to (j, i) in episode j, and had handed the server no
   byte of (k, l) in episode k *)
Definition precedes_l0_def:
  precedes_l0 rss order evs (j, i) (k, l) ⇔
    ∃evs1. evs1 ≼ evs ∧
           reply_bytes (TAKE (SUC i) (replies rss order j)) ≼ l0_sent j evs1 ∧
           l0_read k evs1 ≼ brequests (TAKE l (rss k))
End

(* Safety: at every point there is one order of all the complete requests
   read so far, in all episodes, that keeps each episode's in its order,
   respects real time, and whose replies extend what each episode sent
   (HttpKvSpec2's kv_safe2, on the raw trace) *)
Definition kv_safe_l0_def:
  kv_safe_l0 io ⇔
    ∀evs rss rests.
      LPREFIX (fromList evs) io ∧ LENGTH (l0_accepted evs) < 2 ** 64 − 1 ∧
      (∀j. EVERY valid_brequest (rss j) ∧ no_full_brequest (rests j) ∧
           l0_read j evs = brequests (rss j) ++ rests j) ⇒
      ∃order.
        is_order_l0 rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedes_l0 rss order evs x y ⇒ earlier order x y) ∧
        ∀j. l0_sent j evs ≼ reply_bytes (replies rss order j)
End

(* ------------------------------------------------------------------------
   The claims (to be proved of the HTTP and KV programs on the honest L0
   loop, as echo_l0_safe of echo_l0_prog)
   ------------------------------------------------------------------------ *)

(* The topology the composition needs (step 12, T7 and T8): a successful
   listen only on the configured port (the port is the call's 2-byte conf,
   as honestL0World's l0_call reads it), and no connect *)
Definition l0_topo_ev_def:
  l0_topo_ev port (IO_event (ExtCall n) conf bytes) =
    ((n = «sys_listen» ∧ (∃k. l0_ev_res bytes = SOME (Ok k)) ⇒ w22n conf = port) ∧
     n ≠ «sys_connect») ∧
  l0_topo_ev port _ = T
End

Definition l0_topology_def:
  l0_topology port io ⇔ ∀n ev. LNTH n io = SOME ev ⇒ l0_topo_ev port ev
End

(* The program's first event: a failed sys_listen *)
Definition l0_listen_failed_def:
  l0_listen_failed (IO_event (ExtCall n) conf bytes) =
    (n = «sys_listen» ∧ ∃e v. l0_ev_res bytes = SOME (Fail e v)) ∧
  l0_listen_failed _ = F
End

Definition http_l0_claim_def:
  http_l0_claim port files (prog : dec list) ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃io. (semantics_prog (init_state (l0_ffi w0)) init_env prog (Diverge io) ∧
            http_safe_l0 files io ∧ l0_topology port io) ∨
           (∃ev. l0_listen_failed ev ∧ io = [|ev|] ∧
                 semantics_prog (init_state (l0_ffi w0)) init_env prog
                   (Terminate Success [ev]))
End

Definition kv_l0_claim_def:
  kv_l0_claim port (prog : dec list) ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃io. (semantics_prog (init_state (l0_ffi w0)) init_env prog (Diverge io) ∧
            kv_safe_l0 io ∧ l0_topology port io) ∨
           (∃ev. l0_listen_failed ev ∧ io = [|ev|] ∧
                 semantics_prog (init_state (l0_ffi w0)) init_env prog
                   (Terminate Success [ev]))
End
