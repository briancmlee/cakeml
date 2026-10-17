(*
  Moonshot liveness (design/45 §4.2, steps 14–19): the statement of
  moonshot_live, APPROVED by the user (2026-10-17: global excuse for now,
  no F4).  Nothing here is proved; the claims are definitions of
  propositions.

  WHAT IT SAYS.  Run the client, the proxy and KV as processes 0, 1 and 2
  of an infinite l0sys run (honest-ffi's step-17 l0sys_irun).  Assume:
   - the scheduler is fair (sched_fair) and the kernel is fair in the
     OBSERVED form (kernel_fair_obs), both from honest-ffi's l0sysFair
     (step 17, approved);
   - [F1] and [F2] per process (F1_sys, F2_sys, l0sysFair).  Connect
     fairness [F4] is NOT assumed (user ruling: with failures as excuses it
     is not needed);
   - `isolated`: no outside process uses ports a or b (Q6, as the safety
     headline; the client's private port c is not covered, and the
     conclusion is about the client's CONNECT episodes only);
   - 2 ≤ N < 2^62 (the proxy's exact pair cap, rev 6), valid requests.
  Then, UNLESS AN OBSERVED EXCUSE (sys_excuse), every logical connection
  i < N of the client gets complete replies to all of rqs i, and the client
  exits normally.

  The excuses are all events of the run (no world-level facts):
   - a connection of ours broke (Kern Break; design/45 §9 (b)), or a
     connect of ours failed (ConnFail, or a hard error from sys_connect);
   - a listen of ours failed;
   - a process of ours exited before its program finished (OOM, a signal:
     Exit is the kernel's, design/45 Q9);
   - L1 timed out an fd (D23, the write timeout);
   - a process's accepts failed infinitely often (D18 (c)).
  So there is no start-order, backlog, fd-limit or no-OOM hypothesis in the
  main form: a connect before the listen, a full backlog (the connect
  settles by ConnFail: kernel fairness (C)), or EMFILE all show up as an
  excuse.  moonshot_live_strong is the corollary under the explicit
  hypotheses that none of these happen.

  The excuse is GLOBAL (any of our ends, any process), not per logical
  connection: the per-connection chain front → backend is the proxy's own
  pairing, which is not visible in the run's labels.  A per-connection form
  is a later strengthening (it would quantify the pairing from the proxy's
  claim).

  TEMPORARY COPIES (remove at merge): poll_ev, out_poll, n_out_polls,
  send_took (honestL1BStmts, spike/echo-live-pol), restated on dec_res so
  that this file needs no PF-L1 theories.
*)
Theory moonshotLiveStmts
Ancestors
  l0sysFair l0sys l0sysEpisodes honestL0 honestL0World honestL1Model HttpSpecBodies HttpKvSpec
Libs
  preamble


(* ========================================================================
   Vocabulary
   ======================================================================== *)

(* Process k's events in the first n steps *)
Definition ptr_def:
  ptr (rs : num -> syslabel) k n = proc_events k (GENLIST rs n)
End


(* No outside process uses the ports: none connects to them, none listens
   on them (a connect to one completes only inside the system).  B2's
   "an unpaired episode reads nothing" (step12-gaps B2) should follow.
   TRUSTED-STYLE HYPOTHESIS (Q6), on a and b only, as for safety *)
Definition isolated_def:
  isolated ports (ss : num -> sysstate) (rs : num -> syslabel) ⇔
    ∀n. (∀k p. rs n = Env (EIncoming k p) ⇒ ¬MEM p ports) ∧
        (∀k j p. rs n = Env (EConnUp k j) ∧ (ss n).target (k, j) = SOME p ⇒ ¬MEM p ports) ∧
        (∀k j p. (ss (SUC n)).target (k, j) = SOME p ∧ MEM p ports ∧
                 is_end (ss (SUC n)) (k, j) ∧
                 ¬(sys_chan (ss (SUC n)) (k, j)).connecting ∧
                 ¬(sys_chan (ss (SUC n)) (k, j)).broken ⇒
                 (ss (SUC n)).peer (k, j) ≠ NONE)
End


(* ------------------------------------------------------------------------
   The observed excuses
   ------------------------------------------------------------------------ *)

(* D23's window on fd f (honestL1BStmts, COPY, on dec_res) *)
Definition poll_ev_def:
  poll_ev ev ⇔ ∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs
End

Definition out_poll_def:
  out_poll f ev ⇔
    ∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs ∧
              ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧
                  2 ≤ e MOD 4
End

Definition n_out_polls_def:
  n_out_polls f (evs : io_event list) = LENGTH (FILTER (out_poll f) evs)
End

Definition send_took_def:
  send_took f (IO_event nm conf bs) ⇔
    nm = ExtCall «sys_send» ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = f ∧
    ∃k. dec_res (MAP SND bs) = SOME (Ok k) ∧ 0 < k
End

(* Process k shows a D23 window: K polls listing f for output, and no send
   on f taking bytes.  (Wider than L1's drop condition: it does not ask
   that f be held throughout, so the excuse is, if anything, too generous) *)
Definition timed_out_sys_def:
  timed_out_sys K rs k ⇔
    ∃n pre span f. pre ++ span ≼ ptr rs k n ∧
      K ≤ n_out_polls f span ∧ EVERY (λe. poll_ev e ⇒ out_poll f e) span ∧
      ¬EXISTS (send_took f) span
End

(* D18 (c): process k's accepts fail infinitely often *)
Definition accepts_fail_sys_def:
  accepts_fail_sys (rs : num -> syslabel) k ⇔
    ∀n0. ∃n conf bytes out e v. n0 ≤ n ∧ rs n = Call k «sys_accept» conf bytes out ∧
                                dec_res out = SOME (Fail e v)
End

(* A call nm of process k failed with a hard (not retried) error *)
Definition hard_fail_def:
  hard_fail (rs : num -> syslabel) k nm ⇔
    ∃n conf bytes out e v. rs n = Call k nm conf bytes out ∧
                           dec_res out = SOME (Fail e v) ∧ ¬l1_transient e
End

(* The kernel broke one of k's connections, or failed one of its connects *)
Definition kern_broke_def:
  kern_broke (rs : num -> syslabel) k ⇔
    ∃n j e. (∃keep. rs n = Kern (Break k j e keep)) ∨ rs n = Kern (ConnFail k j e)
End

(* k exited before its program finished *)
Definition crashed_def:
  crashed S rs k ⇔ ∃n. rs n = Exit k ∧ ¬finished (EL k S) (ptr rs k n)
End

Definition sys_excuse_def:
  sys_excuse K S ss rs ⇔
    ∃k. k < LENGTH S ∧
        (kern_broke rs k ∨ hard_fail rs k «sys_connect» ∨ hard_fail rs k «sys_listen» ∨
         crashed S rs k ∨ timed_out_sys K rs k ∨ accepts_fail_sys rs k)
End

(* ------------------------------------------------------------------------
   The conclusions
   ------------------------------------------------------------------------ *)

(* Each logical connection i < N has its own CONNECT episode ep i of the
   client (a connection to the proxy's port a), on which, at some instant,
   the client has sent all of rqs i and read complete replies to all of
   them.  (Which replies: moonshot_view_safe) *)
Definition client_served_def:
  client_served cl a (N : num) (rqs : num -> brequest list) rs ⇔
    ∃ep. (∀(i : num) i'. i < N ∧ i' < N ∧ ep i = ep i' ⇒ i = i') ∧
         ∀i. i < N ⇒
             ∃n ans. l0_ep_role (ep i) (ptr rs cl n) = SOME (Connected a) ∧
                     l0_ep_sent (ep i) (ptr rs cl n) = brequests (rqs i) ∧
                     LENGTH ans = LENGTH (rqs i) ∧
                     reply_bytes ans ≼ l0_ep_recvd (ep i) (ptr rs cl n)
End

(* The client's program finishes and the client exits.  OWED, PENDING [R3]
   (close and shutdown at the handle layer): the chain is the client's
   half-close, the proxy forwarding the EOF, KV closing after the EOF, the
   proxy closing the front, the client reading EOF *)
Definition client_exits_def:
  client_exits S rs cl ⇔ ∃n. rs n = Exit cl ∧ finished (EL cl S) (ptr rs cl n)
End

(* ========================================================================
   THE LIVENESS HEADLINE (main form, with observed excuses)
   ======================================================================== *)

(* cprog a c N rqs: the client (connects to a, private listener c);
   pprog a b: the proxy (listens on a, connects to b); kprog b: KV.
   K: L1's write timeout pf_sendwait (D23) *)
Definition moonshot_sys_def:
  moonshot_sys cprog pprog kprog a b c N rqs : dec list list =
    [cprog a c N rqs; pprog a b; kprog b]
End

Definition moonshot_live_hyps_def:
  moonshot_live_hyps (a : num) (b : num) (c : num) (N : num) (rqs : num -> brequest list)
                     S ss rs ⇔
    (* the run, fair *)
    l0sys_irun S ss rs ∧ sched_fair S ss rs ∧ kernel_fair_obs ss rs ∧
    F1_sys S rs ∧ F2_sys S ss ∧
    (* no strangers on our ports *)
    isolated [a; b] ss rs ∧
    (* the configuration *)
    a < 65536 ∧ b < 65536 ∧ c < 65536 ∧ ALL_DISTINCT [a; b; c] ∧
    2 ≤ N ∧ N < 2 ** 62 ∧ (∀i. EVERY valid_brequest (rqs i))
End

Definition moonshot_live_def:
  moonshot_live K cprog pprog kprog ⇔
    ∀a b c N rqs ss rs.
      moonshot_live_hyps a b c N rqs (moonshot_sys cprog pprog kprog a b c N rqs) ss rs ⇒
      sys_excuse K (moonshot_sys cprog pprog kprog a b c N rqs) ss rs ∨
      (client_served 0 a N rqs rs ∧
       client_exits (moonshot_sys cprog pprog kprog a b c N rqs) rs 0)
End

(* The corollary, under the explicit hypothesis that no excuse happens.
   Each part is a fact of the run; the launch facts that make them
   plausible (start order, backlog ≥ N, fd limits ≥ 2N + 4 / N + 4, no OOM,
   peers reading within pf_sendwait polls) are a further tier, each needing
   its own explicit "no spurious failure" hypothesis, since L0 allows any
   connect, accept or listen to fail and any connection to break *)
Definition moonshot_live_strong_def:
  moonshot_live_strong K cprog pprog kprog ⇔
    ∀a b c N rqs ss rs.
      moonshot_live_hyps a b c N rqs (moonshot_sys cprog pprog kprog a b c N rqs) ss rs ∧
      ¬sys_excuse K (moonshot_sys cprog pprog kprog a b c N rqs) ss rs ⇒
      client_served 0 a N rqs rs ∧
      client_exits (moonshot_sys cprog pprog kprog a b c N rqs) rs 0
End
