(*
  Moonshot liveness (design/45 §4.2, steps 14–19): the statement of
  moonshot_live, as a DRAFT for review.  Nothing here is proved; the
  claims are definitions of propositions.

  WHAT IT SAYS.  Run the client, the proxy and KV as processes 0, 1 and 2
  of an infinite l0sys run (honest-ffi's step-17 l0sys_irun).  Assume:
   - the scheduler is fair (sched_fair, approved) and the kernel is fair in
     the OBSERVED form (kernel_fair_obs, user ruling; honest-ffi is writing
     it; the definition below is a PLACEHOLDER proposal);
   - connect fairness [F4] (approved), [F1] and [F2] per process (approved);
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
  settles by ConnFail: kernel fairness (4)), or EMFILE all show up as an
  excuse.  moonshot_live_strong is the corollary under the explicit
  hypotheses that none of these happen.

  The excuse is GLOBAL (any of our ends, any process), not per logical
  connection: the per-connection chain front → backend is the proxy's own
  pairing, which is not visible in the run's labels.  A per-connection form
  is a later strengthening (it would quantify the pairing from the proxy's
  claim).

  TEMPORARY COPIES (remove when the originals land):
   - l0sys_irun, can_step, sched_fair, kernel_fair, connect_try, connect_up,
     F4: honest-ffi's step-17 draft as sent to the user (2026-10-17, not
     committed anywhere);
   - call_fds, poll_ev, out_poll, n_out_polls, send_took, retried:
     honestL1PFRound / honestL1BStmts (spike/echo-live-pol), restated on
     dec_res so that this file needs no PF-L1 theories.
*)
Theory moonshotLiveStmts
Ancestors
  l0sys l0sysEpisodes honestL0 honestL0World honestL1Model HttpSpecBodies HttpKvSpec
Libs
  preamble

(* ========================================================================
   honest-ffi's step-17 draft (TEMPORARY COPY; user-approved except
   kernel_fair, which the main theorems replace by kernel_fair_obs)
   ======================================================================== *)

Definition l0sys_irun_def:
  l0sys_irun S (ss : num -> sysstate) (rs : num -> syslabel) ⇔
    sys_init S (ss 0) ∧ (∀n. sys_step (ss n) (rs n) (ss (SUC n))) ∧
    ∀k n. k < LENGTH S ⇒ ∃more. prog_makes (EL k S) (proc_events k (GENLIST rs n) ++ more)
End

Definition can_step_def:
  can_step S ss rs k n ⇔
    (ss n).alive k ∧
    ((∃nm conf bytes out s' more.
        prog_makes (EL k S) (proc_events k (GENLIST rs n) ++
                             [IO_event (ExtCall nm) conf (ZIP (bytes, out))] ++ more) ∧
        sys_step (ss n) (Call k nm conf bytes out) s') ∨
     prog_makes (EL k S) (proc_events k (GENLIST rs n)))
End

Definition sched_fair_def:
  sched_fair S ss rs ⇔
    ∀k. (∀n0. ∃n. n0 ≤ n ∧ can_step S ss rs k n) ⇒
        ∀n0. ∃n. n0 ≤ n ∧ ((∃nm c b o'. rs n = Call k nm c b o') ∨ rs n = Exit k)
End

(* The INTERNAL form: kept only as the source of the sanity lemma
   kernel_fair ⇒ kernel_fair_obs (user ruling) *)
Definition kernel_fair_def:
  kernel_fair ss rs ⇔
    (∀e n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧
                           (ss n).moved e < LENGTH (sys_chan (ss n) e).sent) ⇒ F) ∧
    (∀e n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧
                           (ss n).acked e < (ss n).moved e) ⇒ F) ∧
    (∀e n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧ (sys_chan (ss n) e).shut ∧
                           ¬(ss n).finned e ∧ (ss n).moved e = LENGTH (sys_chan (ss n) e).sent) ⇒ F) ∧
    (∀e n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (sys_chan (ss n) e).connecting ∧
                           ¬(sys_chan (ss n) e).closed) ⇒ F)
End

Definition connect_try_def:
  connect_try ss rs k p n ⇔
    (∃conf b out. rs n = Call k «sys_connect» conf b out ∧ w22n conf = p) ∧
    ∃k'. sys_room (ss n) k' p
End

Definition connect_up_def:
  connect_up ss rs k n ⇔
    let j = LENGTH (EL k (ss n).procs).chans in
      j < LENGTH (EL k (ss (SUC n)).procs).chans ∧
      ∃n'. n < n' ∧ is_end (ss n') (k, j) ∧ ¬(sys_chan (ss n') (k, j)).connecting ∧
           ¬(sys_chan (ss n') (k, j)).broken
End

Definition F4_def:
  F4 ss rs ⇔
    ∀k p. (∀n0. ∃n. n0 ≤ n ∧ connect_try ss rs k p n) ⇒
          ∀n0. ∃n. n0 ≤ n ∧ connect_try ss rs k p n ∧ connect_up ss rs k n
End

(* ========================================================================
   Vocabulary
   ======================================================================== *)

(* Process k's events in the first n steps *)
Definition ptr_def:
  ptr (rs : num -> syslabel) k n = proc_events k (GENLIST rs n)
End

(* The fds a call involves (honestL1PFRound.call_fds, COPY) *)
Definition call_fds_def:
  call_fds (nm : mlstring) (conf : word8 list) (ins : word8 list) =
    if nm = «sys_poll» then MAP pe_fd (pollfd_entries (DROP 16 ins))
    else [bytes_fd (TAKE 8 conf)]
End

(* Label l is process k's call nm involving fd f *)
Definition call_on_def:
  call_on k nm f l ⇔
    ∃conf bytes out. l = Call k nm conf bytes out ∧ MEM f (call_fds nm conf bytes)
End

(* A result L1 retries (honestL1PFRound.retried, COPY, on dec_res): any
   failed poll; an l1_transient error of any other call *)
Definition retried_lab_def:
  retried_lab (Call k nm conf bytes out) =
    (case dec_res out of
     | SOME (Fail e _) => nm = «sys_poll» ∨ l1_transient e
     | _ => F) ∧
  retried_lab _ = F
End

(* [F1] (D11′) for every process of the run, on its labels *)
Definition F1_sys_def:
  F1_sys S (rs : num -> syslabel) ⇔
    ∀k nm f. k < LENGTH S ∧ (∀n0. ∃n. n0 ≤ n ∧ call_on k nm f (rs n)) ⇒
             ∀n0. ∃n. n0 ≤ n ∧ call_on k nm f (rs n) ∧ ¬retried_lab (rs n)
End

(* [F2] (D12) for every process: each process's take choices are those of
   its initial L0 state (choices are functions of its history) *)
Definition F2_sys_def:
  F2_sys S (ss : num -> sysstate) ⇔
    ∀k j h n. k < LENGTH S ∧ 0 < n ⇒ 0 < (EL k (ss 0).procs).ch.takes j h 0 n
End

(* Process k ASKS for input on its channel j at step n: a recv on j's fd,
   or a poll listing j's fd for input (L1 recvs only what a poll showed, so
   a recv alone is not enough) *)
Definition asks_in_def:
  asks_in (ss : num -> sysstate) (rs : num -> syslabel) k j n ⇔
    ∃nm conf bytes out f.
      rs n = Call k nm conf bytes out ∧ l0_chan_of (EL k (ss n).procs) f = SOME j ∧
      ((nm = «sys_recv» ∧ LENGTH conf = 8 ∧ bytes_fd conf = f) ∨
       (nm = «sys_poll» ∧ ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 bytes))) ∧ ODD e))
End

Definition asks_io_def:
  asks_io ss rs k j ⇔ ∀n0:num. ∃n. n0 ≤ n ∧ asks_in ss rs k j n
End

(* PLACEHOLDER for honest-ffi's kernel_fair_obs (not yet written).  A
   proposal of its shape, as this draft needs it: delivery and EOF are owed
   only to a receiver that keeps ASKING.  This is what makes backpressure
   real in the model (l0sys inboxes are unbounded, so with unconditional
   delivery no sender could ever wait on a receiver, and the hypothesis
   would exclude the realistic run of a reader that stops reading).
    (1) bytes reach a receiver that asks infinitely often;
    (2) moved bytes are eventually acknowledged (they are in the
        receiver's kernel buffer: [T] §3.4);
    (3) the EOF reaches a receiver that asks infinitely often;
    (4) a pending connect settles.
   kernel_fair ⇒ kernel_fair_obs is immediate (each part is weaker).
   honest-ffi's version will state the conclusions on observed outcomes *)
Definition kernel_fair_obs_def:
  kernel_fair_obs ss rs ⇔
    (∀e k' j' n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e = SOME (k', j') ∧
                                (ss n).moved e < LENGTH (sys_chan (ss n) e).sent) ∧
                  asks_io ss rs k' j' ⇒ F) ∧
    (∀e n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧
                           (ss n).acked e < (ss n).moved e) ⇒ F) ∧
    (∀e k' j' n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e = SOME (k', j') ∧
                                (sys_chan (ss n) e).shut ∧ ¬(ss n).finned e ∧
                                (ss n).moved e = LENGTH (sys_chan (ss n) e).sent) ∧
                  asks_io ss rs k' j' ⇒ F) ∧
    (∀e n0. (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (sys_chan (ss n) e).connecting ∧
                           ¬(sys_chan (ss n) e).closed) ⇒ F)
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

(* The program, answered as recorded, ends normally after the calls evs *)
Definition finished_def:
  finished (prog : dec list) evs ⇔
    semantics_prog (init_state (replay_ffi evs)) init_env prog (Terminate Success evs)
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
    l0sys_irun S ss rs ∧ sched_fair S ss rs ∧ kernel_fair_obs ss rs ∧ F4 ss rs ∧
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
