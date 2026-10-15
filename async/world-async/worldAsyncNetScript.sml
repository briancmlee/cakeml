(*
  Experiment (design/12-world-as-async.md): the world as an async program.

  The world that the echo handler sees is made of two parts:
   - a CLIENT, which is an ordinary async computation (asyncLevel1), in its
     own vocabulary (Send d / Recv);
   - a NETWORK KERNEL, a small state machine (two message queues) that
     answers both sides' actions and reports both sides' readiness.

  run fd m c n polls the server m and the client c side by side for n
  rounds.  Each round both sides emit their new actions; the kernel
  performs the server's batch, then the client's, and hands each side its
  next snapshot (positional responses + readiness).  Neither side's round n
  depends on the other's round n, so the run is well-defined by recursion on
  n: the result is a pair of histories, built round by round.

  For the server, (kernel state, client history) is a world given as a
  state + step function (world_step), the shape the closed-loop and
  cf-reactive results take.

  Results:
   - net_conservation (MAIN): for ANY server and ANY client, nothing is
     created or lost in the network: what the server has read, plus the
     upward queue, is what the client has sent; what the client has
     received, plus the downward queue, is what the server has written.
   - echo_conservation / client_receives_what_it_sent (MAIN): for the echo
     handler and ANY client program, everything the client sent is either
     received, queued downwards, being written in the current round, or
     queued upwards; in particular the client receives exactly a prefix of
     what it sent, in order.
   - example_*: EVAL runs of two echo clients (sequential, and with both).
*)
Theory worldAsyncNet
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer
  asyncServerSafety
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The client's vocabulary
   ------------------------------------------------------------------------ *)

Datatype:
  cevent = CReadable
End

Datatype:
  caction = Send string | Recv
End

Datatype:
  cresponse = Sent | Got string | Empty
End

(* The strings the client has sent / received, in a transcript *)
Definition sent_def:
  sent tr = FLAT (MAP (λp. case FST p of Send d => [d] | _ => []) tr)
End

Definition got_def:
  got tr = FLAT (MAP (λp. case p of (Recv, SOME (Got d)) => [d] | _ => []) tr)
End

Theorem sent_APPEND[simp]:
  sent (t1 ++ t2) = sent t1 ++ sent t2
Proof
  simp[sent_def]
QED

Theorem got_APPEND[simp]:
  got (t1 ++ t2) = got t1 ++ got t2
Proof
  simp[got_def]
QED

(* ------------------------------------------------------------------------
   The network kernel: one connection, two message queues
   up:   sent by the client, not yet read by the server
   down: written by the server, not yet received by the client
   ------------------------------------------------------------------------ *)

Datatype:
  net = <| up : string list ; down : string list |>
End

(* One server action (the connection is fd; other fds are dead) *)
Definition sact_def:
  sact fd k (Read g) =
    (if g = fd then
       case k.up of [] => (k, WouldBlock) | d :: r => (k with up := r, Data d)
     else (k, WouldBlock)) ∧
  sact fd k (Write g d) =
    ((if g = fd then k with down := k.down ++ [d] else k), Written) ∧
  sact fd k (Accept l) = (k, NoConn)
End

Definition cact_def:
  cact k (Send d) = (k with up := k.up ++ [d], Sent) ∧
  cact k Recv =
    case k.down of [] => (k, Empty) | d :: r => (k with down := r, Got d)
End

(* A batch, in order; one response per action *)
Definition sacts_def:
  sacts fd k [] = (k, []) ∧
  sacts fd k (a :: as) =
    let (k1, r) = sact fd k a; (k2, rs) = sacts fd k1 as in (k2, r :: rs)
End

Definition cacts_def:
  cacts k [] = (k, []) ∧
  cacts k (a :: as) =
    let (k1, r) = cact k a; (k2, rs) = cacts k1 as in (k2, r :: rs)
End

(* Readiness is computed from the kernel state: honest by construction *)
Definition ssnap_def:
  ssnap fd k n rs =
    <| ready := (if k.up ≠ [] then {Readable fd} else {}); now := n; results := rs |>
End

Definition csnap_def:
  csnap k n rs =
    <| ready := (if k.down ≠ [] then {CReadable} else {}); now := n; results := rs |>
End

(* ------------------------------------------------------------------------
   Connecting a server to a client
   ------------------------------------------------------------------------ *)

(* The server's world: state = (kernel, client history); input = the
   server's new actions; output = the server's next snapshot.  The client
   is polled inside the step. *)
Definition world_step_def:
  world_step fd c (k, hc) as =
    let (k1, rs) = sacts fd k as;
        (k2, rc) = cacts k1 (new_actions (log_of c) hc);
        n = SUC (LENGTH hc)
    in (ssnap fd k2 n rs, (k2, hc ++ [csnap k2 n rc]))
End

Definition net0_def:
  net0 = <| up := []; down := [] |>
End

(* n rounds of the server m against the client c: (server history, world) *)
Definition run_def:
  run fd m c 0 = ([], (net0, [])) ∧
  run fd m c (SUC n) =
    let (hs, w) = run fd m c n;
        (s, w') = world_step fd c w (new_actions (log_of m) hs)
    in (hs ++ [s], w')
End

(* ------------------------------------------------------------------------
   Completed transcripts: only the rounds whose responses have arrived
   ------------------------------------------------------------------------ *)

Definition ctrans_def:
  ctrans m h = FLAT (GENLIST (round_trans m h) (LENGTH h))
End

Theorem ctrans_NIL[simp]:
  ctrans m [] = []
Proof
  simp[ctrans_def]
QED

Theorem ctrans_SNOC:
  ctrans m (h ++ [s]) = ctrans m h ++ zipr (new_actions (log_of m) h) s.results
Proof
  simp[ctrans_def] >> REWRITE_TAC[GSYM ADD1, GENLIST, SNOC_APPEND, FLAT_APPEND]
  >> simp[round_trans_def, responses_at_def, EL_APPEND2, TAKE_LENGTH_APPEND, zipr_def]
  >> AP_TERM_TAC >> simp[GENLIST_FUN_EQ, round_trans_def, TAKE_APPEND1,
                         responses_at_def, EL_APPEND1]
QED

Theorem trans_ctrans:
  trans m h = ctrans m h ++ zipr (new_actions (log_of m) h) []
Proof
  simp[trans_def, ctrans_def, GENLIST, SNOC_APPEND, round_trans_def,
       responses_at_def]
QED

Theorem zipr_NIL_read:
  ∀as. read fd (zipr as []) = []
Proof
  Induct >> simp[zipr_def]
  >> Cases >> simp[]
QED

Theorem LENGTH_zipr[simp]:
  ∀as rs. LENGTH (zipr as rs) = LENGTH as
Proof
  Induct >> simp[zipr_def]
QED

(* ------------------------------------------------------------------------
   The kernel moves strings, it never creates or drops them
   ------------------------------------------------------------------------ *)

Theorem sacts_moves:
  ∀as k k' rs.
    sacts fd k as = (k', rs) ⇒
    read fd (zipr as rs) ++ k'.up = k.up ∧
    k'.down = k.down ++ written fd (zipr as rs)
Proof
  Induct >> simp[sacts_def, zipr_def]
  >> rpt gen_tac >> rename1 ‘sact fd k a’
  >> Cases_on ‘sact fd k a’ >> rename1 ‘_ = (k1, r)’
  >> Cases_on ‘sacts fd k1 as’ >> simp[] >> strip_tac >> gvs[]
  >> first_x_assum drule >> strip_tac
  >> Cases_on ‘a’ >> gvs[sact_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

Theorem cacts_moves:
  ∀as k k' rs.
    cacts k as = (k', rs) ⇒
    k'.up = k.up ++ sent (zipr as rs) ∧
    got (zipr as rs) ++ k'.down = k.down
Proof
  Induct >> simp[cacts_def, zipr_def, sent_def, got_def]
  >> rpt gen_tac >> rename1 ‘cact k a’
  >> Cases_on ‘cact k a’ >> rename1 ‘_ = (k1, r)’
  >> Cases_on ‘cacts k1 as’ >> simp[] >> strip_tac >> gvs[]
  >> first_x_assum drule >> strip_tac
  >> Cases_on ‘a’ >> gvs[cact_def, AllCaseEqs(), sent_def, got_def]
QED

(* MAIN: for any server m and any client c, after any number of rounds the
   network has neither created nor dropped a string *)
Theorem net_conservation:
  ∀n hs k hc.
    run fd m c n = (hs, (k, hc)) ⇒
    read fd (ctrans m hs) ++ k.up = sent (ctrans c hc) ∧
    got (ctrans c hc) ++ k.down = written fd (ctrans m hs)
Proof
  Induct >- simp[run_def, net0_def, sent_def, got_def, read_def, written_def]
  >> simp[run_def] >> rpt gen_tac >> Cases_on ‘run fd m c n’ >> rename1 ‘_ = (hs0, w0)’
  >> PairCases_on ‘w0’ >> simp[world_step_def]
  >> Cases_on ‘sacts fd w00 (new_actions (log_of m) hs0)’
  >> Cases_on ‘cacts q (new_actions (log_of c) w01)’
  >> simp[] >> strip_tac >> gvs[ctrans_SNOC, ssnap_def, csnap_def]
  >> imp_res_tac sacts_moves >> imp_res_tac cacts_moves >> gvs[]
  >> metis_tac[APPEND_ASSOC]
QED

(* ------------------------------------------------------------------------
   The echo handler against any client
   ------------------------------------------------------------------------ *)

(* MAIN: everything the client has sent is accounted for, in order:
   received by the client, queued downwards, being written by the server
   this round, or queued upwards (not yet read by the server) *)
Theorem echo_conservation:
  run fd (handler fd) c n = (hs, (k, hc)) ⇒
  sent (ctrans c hc) =
    got (ctrans c hc) ++ k.down ++
    written fd (zipr (new_actions (log_of (handler fd)) hs) ([] : response list)) ++ k.up
Proof
  strip_tac >> drule net_conservation >> strip_tac
  >> mp_tac (Q.SPEC ‘hs’ handler_echoes)
  >> simp[trans_ctrans, zipr_NIL_read] >> rpt strip_tac
  >> qpat_x_assum ‘read _ _ ++ _ = _’ (SUBST1_TAC o SYM)
  >> qpat_x_assum ‘_ = read _ _’ (SUBST1_TAC o SYM)
  >> qpat_x_assum ‘got _ ++ _ = _’ (SUBST1_TAC o SYM) >> REWRITE_TAC[APPEND_ASSOC]
QED

(* MAIN: whatever the client program, it only ever receives what it sent,
   in order *)
Theorem client_receives_what_it_sent:
  run fd (handler fd) c n = (hs, (k, hc)) ⇒
  got (ctrans c hc) ≼ sent (ctrans c hc)
Proof
  strip_tac >> drule echo_conservation >> simp[]
  >> metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]
QED

(* ------------------------------------------------------------------------
   Echo clients, written with the library
   ------------------------------------------------------------------------ *)

Definition send_all_def:
  send_all [] = return () ∧
  send_all (l :: ls) = bind (emit (Send l)) (λu. send_all ls)
End

Definition creadable_def:
  creadable = wait (λs. if CReadable ∈ s.ready then SOME () else NONE)
End

(* Receive n strings; retry when nothing has arrived *)
Definition recv_n_body_def:
  recv_n_body r n =
    if n = 0 then return []
    else bind creadable (λu.
         bind (emit Recv) (λres.
           case res of
             Got d => map (CONS d) (r (n - 1))
           | _ => r n))
End

Theorem recv_n_body_contractive:
  contractive recv_n_body
Proof
  rw[contractive_def, recv_n_body_def] >> Cases_on ‘p = 0’ >> simp[guarded_const]
  >> ho_match_mp_tac guarded_bind
  >> simp[creadable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call]
  >> ho_match_mp_tac nonexpansive_map >> simp[nonexpansive_call]
QED

Definition recv_n_def:
  recv_n = fix recv_n_body
End

Theorem recv_n_unfold:
  recv_n n = recv_n_body recv_n n
Proof
  simp[recv_n_def, Once (MATCH_MP fix_unfold recv_n_body_contractive)]
QED

(* Send the lines, then read the replies *)
Definition echo_client_def:
  echo_client ls = bind (send_all ls) (λu. recv_n (LENGTH ls))
End

(* Send and receive concurrently *)
Definition echo_client2_def:
  echo_client2 ls = map SND (both (send_all ls) (recv_n (LENGTH ls)))
End

(* ------------------------------------------------------------------------
   Concrete runs
   ------------------------------------------------------------------------ *)

Theorem example_run_sequential:
  let (hs, (k, hc)) = run 7 (handler 7) (echo_client ["hi"; "yo"]) 8 in
    (echo_client ["hi"; "yo"] hc).result = SOME ["hi"; "yo"] ∧
    k = net0
Proof
  EVAL_TAC
QED

Theorem example_run_concurrent:
  let (hs, (k, hc)) = run 7 (handler 7) (echo_client2 ["hi"; "yo"]) 7 in
    (echo_client2 ["hi"; "yo"] hc).result = SOME ["hi"; "yo"] ∧
    (handler 7 hs).actions =
      [Read 7; Write 7 "hi"; Read 7; Write 7 "yo"]
Proof
  EVAL_TAC
QED
