(*
  Run-level connect settling, model-generic (close-v2's part of the shared
  E1 progress layer): a pending connect settles (up, then promoted in the
  same tail, or refused) under the kernel's settle fairness and the
  fairness of its pending-error read.

  Per round k from n on, while the connect is pending (Pd) and the goal's
  other outcomes (D: e.g. the handle closed) don't hold: if the poll
  reports its fd writable or ERR/HUP (Wr k), its pending error is read
  (Ce k, sys_connerr attempted); if that read goes through (Ceok k) it is
  no longer pending after the round.  The kernel settles it: from some
  round on, a pending connect is reported (connects_settle).  With
  fairness at round granularity, it settles or D holds.

  MAIN: settle_lift.
*)
Theory e1SettleLift
Ancestors
  e1FlushLift
Libs
  preamble

Theorem settle_lift:
  ∀Pd Wr Ce Ceok D n.
    (∀k. n ≤ k ∧ Pd k ∧ ¬D k ⇒ (Wr k ⇒ Ce k) ∧ (Ceok k ⇒ ¬Pd (SUC k))) ∧
    (∃n0. ∀k. n0 ≤ k ∧ Pd k ∧ ¬D k ⇒ Wr k) ∧
    rfair Ce Ceok ⇒
    ∃k. n ≤ k ∧ (¬Pd k ∨ D k)
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘¬∃k. _’ (strip_assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM, DE_MORGAN_THM]) >>
  ‘∀k. n ≤ k ⇒ Pd k ∧ ¬D k’
    by (rpt strip_tac >> qpat_x_assum ‘∀k. ¬(n ≤ k) ∨ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘∀i. ∃k. i ≤ k ∧ Ce k’
    by (gen_tac >> qexists_tac ‘i + n + n0’ >> conj_tac >- decide_tac >>
        ‘n ≤ i + n + n0 ∧ n0 ≤ i + n + n0’ by decide_tac >> metis_tac[]) >>
  qpat_x_assum ‘rfair Ce Ceok’ (mp_tac o REWRITE_RULE [rfair_def]) >>
  disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀k. n ≤ k ⇒ Pd k ∧ ¬D k’ (qspec_then ‘k’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum ‘∀k. n ≤ k ⇒ Pd k ∧ ¬D k’ (qspec_then ‘SUC k’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘∀k. n ≤ k ∧ Pd k ∧ ¬D k ⇒ _’ (qspec_then ‘k’ mp_tac) >>
  impl_tac >- fs[] >> strip_tac >> res_tac
QED
