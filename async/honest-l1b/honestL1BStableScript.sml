(*
  L3-09 (S4), l1pf_stable: with finitely many arrivals, the PF run settles.
  Past the last arrival the queue empties (queue_empty) and the fetches
  find nothing (fetch_stop); a quiet server then stops acting (SQ, its
  obligation, discharged per server); every call but the poll stops
  (only_polls, by F1) and L1's state settles (settle_idle, D23).  From
  then on every round is idle: no actions, not busy, pf_idle, a single
  poll, and the state and the world's arrivals no longer change.

  MAIN: l1pf_stable.
*)
Theory honestL1BStable
Ancestors
  honestL1PFOutLive honestL1PFOut honestL1BGone honestL1BSettleState honestL1BCallsStop honestL1BFetchStop honestL1BSettle
  honestL1BQuietWorld honestL1BModel honestL1PFConnRun honestL1PFLive honestL1PFModel
  honestL1Model honestL0World
Libs
  preamble

(* SQ (server quiet; L3-09 design §6a), the server's obligation: once
   nothing more is fetched, the server eventually stops acting, is not
   busy, and is told of nothing (it read what it was shown, and does not
   poll a closed handle) *)
Definition SQ_def:
  SQ lfd pol ifds bz m w0 ⇔
    ∀n0. (∀n. n0 ≤ n ⇒ rlog lfd pol ifds m w0 n = []) ⇒
         ∃n1. ∀n. n1 ≤ n ⇒
              new_actions (log_of m) (rhist lfd pol ifds m w0 n) = [] ∧
              ¬bz (rhist lfd pol ifds m w0 n) ∧
              pf_ready lfd (rstate lfd pol ifds m w0 n) (ifds (rhist lfd pol ifds m w0 n)) = []
End

(* No outbox entry holds bytes when the held fds' outboxes are empty: the
   outbox has one entry per fd and none empty (obwf), and only held fds
   have one (okeys) *)
Theorem held_out_entries[local]:
  EVERY (λf. outbox_of b f = [] ∧ P f) (MAP SND b.tbl ++ b.closing) ∧ obwf b ∧ okeys b ⇒
  EVERY (λ(f, bs). bs = []) b.outbox
Proof
  rw[EVERY_MEM, FORALL_PROD] >> CCONTR_TAC >>
  ‘outbox_of b p_1 = p_2’ by (irule obwf_outbox_of >> simp[]) >>
  ‘MEM p_1 (MAP SND b.tbl) ∨ MEM p_1 b.closing’ by (fs[okeys_def] >> first_x_assum irule >> simp[]) >>
  res_tac >> fs[]
QED

(* MAIN, (S4) *)
Theorem l1pf_stable:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S2 lfd pol ifds m w0 ∧
  ¬accepts_fail lfd pol ifds m w0 ∧ SQ lfd pol ifds bz m w0 ∧ quiet_after N w0 ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
    new_actions (log_of m) (rhist lfd pol ifds m w0 n) = [] ∧
    ¬bz (rhist lfd pol ifds m w0 n) ∧
    pf_idle lfd pol (rstate lfd pol ifds m w0 n) (ifds (rhist lfd pol ifds m w0 n)) ∧
    EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 n) ∧
    rstate lfd pol ifds m w0 (SUC n) = rstate lfd pol ifds m w0 n ∧
    N ≤ (rworld lfd pol ifds m w0 n).clock ∧ quiet_after N (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >>
  drule_all fetch_stop >> disch_then (qx_choose_then ‘Kf’ assume_tac) >>
  drule_all queue_empty >> disch_then (qx_choose_then ‘Kq’ assume_tac) >>
  drule_all run_quiet >> disch_then (qx_choose_then ‘Kw’ assume_tac) >>
  qpat_x_assum ‘SQ _ _ _ _ _ _’ (mp_tac o REWRITE_RULE[SQ_def]) >>
  disch_then (qspec_then ‘Kf’ mp_tac) >> impl_tac >- simp[] >>
  disch_then (qx_choose_then ‘Ks’ assume_tac) >>
  qabbrev_tac ‘K0 = Kf + Kq + Kw + Ks’ >>
  ‘∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                rlog lfd pol ifds m w0 k = [] ∧
                qof (rworld lfd pol ifds m w0 k) lfd = [] ∧
                N ≤ (rworld lfd pol ifds m w0 k).clock ∧
                quiet_after N (rworld lfd pol ifds m w0 k)’
    by (rpt strip_tac >> fs[Abbr ‘K0’]) >>
  drule only_polls >> rpt (disch_then drule) >> disch_then (qx_choose_then ‘Kp’ assume_tac) >>
  ‘∀k. K0 + Kp ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                     EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 k)’
    by (rpt strip_tac >> fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
        qexists_tac ‘k’ >> simp[]) >>
  drule settle_idle >> disch_then drule >> disch_then (qx_choose_then ‘K1’ assume_tac) >>
  qexists_tac ‘K0 + Kp + K1’ >> gen_tac >> strip_tac >>
  ‘K0 ≤ n ∧ K0 + Kp ≤ n ∧ K1 ≤ n ∧ Ks ≤ n’ by simp[Abbr ‘K0’] >>
  qpat_x_assum ‘∀k. K1 ≤ k ⇒ _’ (qspec_then ‘n’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘∀n. Ks ≤ n ⇒ _’ (qspec_then ‘n’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘∀k. K0 + Kp ≤ k ⇒ _’ (qspec_then ‘n’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘∀k. K0 ≤ k ⇒ _’ (qspec_then ‘n’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  ‘oassm lfd pol ifds m w0’ by simp[oassm_def] >>
  drule run_rel >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘okeys (rstate lfd pol ifds m w0 n).b’ by fs[out_rel_def] >>
  ‘obwf (rstate lfd pol ifds m w0 n).b’ by metis_tac[obwf_run] >>
  ‘EVERY (λ(f, bs). bs = []) (rstate lfd pol ifds m w0 n).b.outbox’
    by (irule held_out_entries >> fs[pf_held_def] >> metis_tac[]) >>
  fs[pf_idle_def, EVERY_MEM]
QED
