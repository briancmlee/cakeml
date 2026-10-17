(*
  Run-level flush progress, model-generic (close-v2's part of the shared
  E1 progress layer, agreed with honest-ffi): honest-l1's flush_progress
  argument with the run abstracted to its rounds' worlds wn and per-round
  predicates, so that E1 (and the proxy's drains direction) instantiate
  it with their own per-round lemma (pround_live's analogue).

  Per round k from n on, while f stays live (L) and the goal is not met:
  f stays live, c's flow is kept (cflow) and nothing is sent on c; some
  poll on f is attempted (P k); and if one goes through (Pok k) while
  nothing is in flight and the kernel takes a byte, a send on f is
  attempted (S k).  With drains (at the rounds), F2 and fairness at
  round granularity (attempted infinitely often ⇒ through infinitely
  often), a send on f goes through (Sok), or the goal's other outcomes
  (D: e.g. the outbox emptied) hold, or c breaks.

  MAIN: flush_lift.
*)
Theory e1FlushLift
Ancestors
  honestL1PFFlush honestL1PFOut honestL0World
Libs
  preamble

(* Fairness at round granularity *)
Definition rfair_def:
  rfair (P : num -> bool) (Q : num -> bool) ⇔
    (∀i. ∃k. i ≤ k ∧ P k) ⇒ ∀i. ∃k. i ≤ k ∧ Q k
End

(* arithmetic, clear of the quantified hypotheses *)
val ar_tac = rpt (qpat_x_assum ‘∀x. _’ kall_tac) >> decide_tac

Theorem flush_lift:
  ∀(wn : num -> l0world) L P Pok Sd Sdok D w0 c n.
    (∀k. n ≤ k ∧ L k ∧ ¬Sdok k ∧ ¬D k ∧ ¬(EL c (wn (SUC k)).chans).broken ⇒
         L (SUC k) ∧ cflow (wn k) (wn (SUC k)) c ∧ csent (wn (SUC k)) c = csent (wn k) c ∧
         P k ∧
         (Pok k ∧ ¬(EL c (wn k).chans).shut ∧ (EL c (wn k).chans).inflight = 0 ∧
          (∀hh. 0 < (wn k).ch.takes c hh 0 1) ⇒ Sd k)) ∧
    L n ∧ ¬(EL c (wn n).chans).shut ∧
    (∀m. (∀k. m ≤ k ⇒ csent (wn k) c = csent (wn m) c) ⇒
         ∃m'. m ≤ m' ∧ (EL c (wn m').chans).inflight = 0) ∧
    F2 w0 ∧ (∀k. (wn k).ch = w0.ch) ∧
    rfair P Pok ∧ rfair Sd Sdok ⇒
    ∃k. n ≤ k ∧ (Sdok k ∨ D k ∨ (EL c (wn (SUC k)).chans).broken)
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘¬∃k. _’ (strip_assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM, DE_MORGAN_THM]) >>
  ‘∀k. n ≤ k ⇒ ¬Sdok k ∧ ¬D k ∧ ¬(EL c (wn (SUC k)).chans).broken’
    by (rpt strip_tac >> qpat_x_assum ‘∀k. ¬(n ≤ k) ∨ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀k. ¬(n ≤ k) ∨ _’ kall_tac >>
  (* f live, nothing sent, from n on *)
  ‘∀d. L (n + d) ∧ csent (wn (n + d)) c = csent (wn n) c’
    by (Induct >- simp[] >>
        qpat_assum ‘∀k. n ≤ k ⇒ ¬Sdok k ∧ _’ (qspec_then ‘n + d’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_assum ‘∀k. n ≤ k ∧ L k ∧ _ ⇒ _’ (qspec_then ‘n + d’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> fs[ADD_CLAUSES]) >>
  ‘∀k. n ≤ k ⇒ L k ∧ csent (wn k) c = csent (wn n) c’
    by (rpt strip_tac >> qpat_x_assum ‘∀d. _’ (qspec_then ‘k - n’ mp_tac) >> simp[]) >>
  (* each round from n on keeps the flow, attempts a poll, and sends after one *)
  ‘∀k. n ≤ k ⇒
       cflow (wn k) (wn (SUC k)) c ∧ P k ∧
       (Pok k ∧ ¬(EL c (wn k).chans).shut ∧ (EL c (wn k).chans).inflight = 0 ∧
        (∀hh. 0 < (wn k).ch.takes c hh 0 1) ⇒ Sd k)’
    by (gen_tac >> strip_tac >>
        qpat_assum ‘∀k. n ≤ k ⇒ ¬Sdok k ∧ _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_assum ‘∀k. n ≤ k ⇒ L k ∧ _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_assum ‘∀k. n ≤ k ∧ L k ∧ _ ⇒ _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> simp[]) >>
  ‘∀a d. n ≤ a ⇒ cflow (wn a) (wn (a + d)) c’
    by (gen_tac >> Induct >- simp[] >> strip_tac >>
        irule cflow_trans >> qexists_tac ‘wn (a + d)’ >> simp[ADD_CLAUSES] >>
        qpat_assum ‘∀k. n ≤ k ⇒ cflow _ _ _ ∧ _’ (qspec_then ‘a + d’ mp_tac) >> simp[]) >>
  (* drains: nothing in flight at some n1, and so from n1 on *)
  ‘∃n1. n ≤ n1 ∧ (EL c (wn n1).chans).inflight = 0’
    by (qpat_x_assum ‘∀m. (∀k. m ≤ k ⇒ _) ⇒ _’ (qspec_then ‘n’ mp_tac) >>
        impl_tac >- (rpt strip_tac >> qpat_assum ‘∀k. n ≤ k ⇒ L k ∧ _’ drule >> simp[]) >>
        simp[]) >>
  ‘∀k. n1 ≤ k ⇒ (EL c (wn k).chans).inflight = 0 ∧ ¬(EL c (wn k).chans).shut ∧
                (∀hh. 0 < (wn k).ch.takes c hh 0 1)’
    by (gen_tac >> strip_tac >>
        ‘cflow (wn n1) (wn k) c’
          by (qpat_assum ‘∀a d. n ≤ a ⇒ _’ (qspecl_then [‘n1’, ‘k - n1’] mp_tac) >>
              impl_tac >- ar_tac >> ‘n1 + (k − n1) = k’ by ar_tac >> pop_assum (fn th => REWRITE_TAC [th])) >>
        ‘cflow (wn n) (wn k) c’
          by (qpat_assum ‘∀a d. n ≤ a ⇒ _’ (qspecl_then [‘n’, ‘k - n’] mp_tac) >>
              impl_tac >- ar_tac >> ‘n + (k − n) = k’ by ar_tac >> pop_assum (fn th => REWRITE_TAC [th])) >>
        ‘csent (wn k) c = csent (wn n1) c’
          by (‘n ≤ k’ by ar_tac >>
              qpat_assum ‘∀k. n ≤ k ⇒ L k ∧ _’ (qspec_then ‘k’ mp_tac) >>
              qpat_assum ‘∀k. n ≤ k ⇒ L k ∧ _’ (qspec_then ‘n1’ mp_tac) >> simp[]) >>
        qpat_x_assum ‘cflow (wn n1) _ _’ mp_tac >> qpat_x_assum ‘cflow (wn n) _ _’ mp_tac >>
        simp[cflow_def] >> rpt strip_tac >> fs[] >>
        qpat_x_assum ‘F2 _’ (mp_tac o REWRITE_RULE [F2_def]) >> simp[]) >>
  (* polls attempted every round from n on; through infinitely often *)
  ‘∀i. ∃k. i ≤ k ∧ Pok k’
    by (qpat_x_assum ‘rfair P Pok’ (irule o REWRITE_RULE [rfair_def]) >>
        gen_tac >> qexists_tac ‘i + n’ >> simp[] >>
        qpat_assum ‘∀k. n ≤ k ⇒ cflow _ _ _ ∧ _’ (qspec_then ‘i + n’ mp_tac) >> simp[]) >>
  (* so sends are attempted infinitely often; one goes through *)
  ‘∀i. ∃k. i ≤ k ∧ Sd k’
    by (gen_tac >>
        qpat_x_assum ‘∀i. ∃k. i ≤ k ∧ Pok k’ (qspec_then ‘i + n1’ strip_assume_tac) >>
        qexists_tac ‘k’ >>
        ‘i ≤ k ∧ n ≤ k ∧ n1 ≤ k’ by ar_tac >>
        conj_tac >- first_assum ACCEPT_TAC >>
        ‘(EL c (wn k).chans).inflight = 0 ∧ ¬(EL c (wn k).chans).shut ∧
         ∀hh. 0 < (wn k).ch.takes c hh 0 1’
          by (qpat_assum ‘∀k. n1 ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >>
              impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
        qpat_assum ‘∀k. n ≤ k ⇒ cflow _ _ _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
        first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘rfair Sd Sdok’ (mp_tac o REWRITE_RULE [rfair_def]) >>
  disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qpat_x_assum ‘∀k. n ≤ k ⇒ ¬Sdok k ∧ _’ (qspec_then ‘k’ mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_x_assum ‘Sdok k’ mp_tac >> qpat_x_assum ‘¬Sdok k’ mp_tac >> REWRITE_TAC[]
QED
