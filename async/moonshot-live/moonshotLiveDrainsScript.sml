(*
  Moonshot liveness, N5 (README §4): drains_of_asks, at l0sys level.

  If the receiver of a connection keeps ASKING (a recv, or a poll listing
  its fd for input, infinitely often), then once the sender stops sending,
  every byte it sent is eventually moved to the receiver and acknowledged
  to the sender, for good: in the sender's L0 world, nothing is left in
  flight.  This is the system-level step of the rank induction (the
  prototype's fl_zero_io).

  The kernel fairness is ISOLATED: drains_of_fair takes, for the one end,
  exactly the two facts it uses (delivery does not stall for ever; an
  acknowledgement does not stall for ever) as explicit premises, and
  mentions no fairness definition.  drains_of_asks is the only theorem
  that reads kernel_fair_obs (moonshotLiveStmts' placeholder), so swapping
  in honest-ffi's observed form is a change to that corollary alone.
*)
Theory moonshotLiveDrains
Ancestors
  moonshotLiveStmts l0sys l0sysCausal l0sysStep l0sysRun l0sysInvCall
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* Invariants along an infinite run *)

Theorem irun_sinv:
  l0sys_irun ps ss rs ⇒ ∀n. ∃css. sinv (GENLIST rs n) (ss n) css
Proof
  strip_tac >> Induct
  >- (qexists_tac ‘K []’ >> simp[] >> irule sinv_init >> qexists_tac ‘ps’ >>
      fs[l0sys_irun_def] >> rw[] >> irule l0_rely_small_ch >>
      fs[sys_init_def, LET_THM]) >>
  fs[] >> qexists_tac ‘step_css (ss n) (rs n) css’ >>
  simp[GENLIST, SNOC_APPEND] >> irule sinv_step >> fs[l0sys_irun_def]
QED

Theorem irun_ext:
  l0sys_irun ps ss rs ⇒ ∀n. sys_ext (ss n) (ss (SUC n))
Proof
  rpt strip_tac >> drule irun_sinv >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  irule sys_ext_step >> fs[l0sys_irun_def] >> metis_tac[]
QED

Theorem irun_kinv:
  l0sys_irun ps ss rs ⇒ ∀n. kinv (ss n)
Proof
  rpt strip_tac >> drule irun_sinv >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  fs[sinv_def]
QED

Theorem deliver_counters[simp]:
  (sys_deliver k a s).moved = s.moved ∧ (sys_deliver k a s).acked = s.acked
Proof
  simp[sys_deliver_def]
QED

Theorem pair_counters[simp]:
  (sys_pair e k p s).moved = s.moved ∧ (sys_pair e k p s).acked = s.acked
Proof
  simp[sys_pair_def, LET_THM]
QED

(* moved and acked only grow, and an acknowledgement never passes what
   moved *)
Theorem le_add_helper[local]:
  (∀x. f x ≤ g x : num) ⇒ f y ≤ g y ∧ f y ≤ n + g y
Proof
  rw[] >> first_x_assum (qspec_then ‘y’ mp_tac) >> simp[]
QED

Theorem step_counters:
  sys_step s r s' ⇒
  s.moved e ≤ s'.moved e ∧ s.acked e ≤ s'.acked e ∧
  ((∀e. s.acked e ≤ s.moved e) ⇒ s'.acked e ≤ s'.moved e)
Proof
  Cases_on ‘r’ >> TRY (rename1 ‘Kern kk’ >> Cases_on ‘kk’) >>
  TRY (rename1 ‘Env ee’ >> Cases_on ‘ee’) >>
  simp[sys_step_def, LET_THM] >> rpt strip_tac >> every_case_tac >>
  gvs[combinTheory.APPLY_UPDATE_THM] >> rw[] >> fs[] >> metis_tac[le_add_helper]
QED

Theorem irun_acked_le:
  l0sys_irun ps ss rs ⇒ ∀n e. (ss n).acked e ≤ (ss n).moved e
Proof
  strip_tac >> Induct
  >- fs[l0sys_irun_def, sys_init_def] >>
  ‘sys_step (ss n) (rs n) (ss (SUC n))’ by fs[l0sys_irun_def] >>
  metis_tac[step_counters]
QED

Theorem irun_mono:
  l0sys_irun ps ss rs ⇒
  ∀n n'. n ≤ n' ⇒ (ss n).moved e ≤ (ss n').moved e ∧ (ss n).acked e ≤ (ss n').acked e ∧
                  ∀e'. (ss n).peer e = SOME e' ⇒ (ss n').peer e = SOME e'
Proof
  strip_tac >> ‘∀d n. (ss n).moved e ≤ (ss (n + d)).moved e ∧ (ss n).acked e ≤ (ss (n + d)).acked e ∧
                      ∀e'. (ss n).peer e = SOME e' ⇒ (ss (n + d)).peer e = SOME e'’
    suffices_by (rw[] >> first_x_assum (qspecl_then [‘n' − n’, ‘n’] mp_tac) >> simp[]) >>
  Induct >> simp[] >> rpt gen_tac >>
  ‘sys_step (ss (n + d)) (rs (n + d)) (ss (SUC (n + d)))’ by fs[l0sys_irun_def] >>
  drule step_counters >> disch_then (qspec_then ‘e’ strip_assume_tac) >>
  ‘sys_ext (ss (n + d)) (ss (SUC (n + d)))’ by metis_tac[irun_ext] >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >> fs[ADD_CLAUSES] >>
  rw[] >> fs[sys_ext_def]
QED

(*---------------------------------------------------------------------------*)
(* N5 *)

(* The core, with the two kernel facts as premises: from n0 on, end e has
   its peer and has stopped sending (L bytes); its bytes do not stay
   undelivered for ever, nor unacknowledged for ever.  Then from some
   point on, all L bytes are moved and acknowledged *)
Theorem drains_of_fair:
  l0sys_irun ps ss rs ∧ (ss n0).peer e = SOME e' ∧
  (∀n. n0 ≤ n ⇒ LENGTH (sys_chan (ss n) e).sent = L) ∧
  ¬(∀n. n0 ≤ n ⇒ (ss n).moved e < LENGTH (sys_chan (ss n) e).sent) ∧
  (∀n1. ¬(∀n. n1 ≤ n ⇒ (ss n).acked e < (ss n).moved e)) ⇒
  ∃n2. n0 ≤ n2 ∧ ∀n. n2 ≤ n ⇒ (ss n).moved e = L ∧ (ss n).acked e = L
Proof
  strip_tac >> drule irun_mono >> disch_then (qspec_then ‘e’ assume_tac) >>
  drule irun_kinv >> strip_tac >> drule irun_acked_le >> strip_tac >>
  ‘∀n. n0 ≤ n ⇒ (ss n).moved e ≤ L’ by
    (rw[] >> ‘(ss n).peer e = SOME e'’ by metis_tac[] >>
     ‘kinv (ss n)’ by simp[] >> fs[kinv_def] >> res_tac >> metis_tac[]) >>
  ‘∃n1. n0 ≤ n1 ∧ (ss n1).moved e = L’ by
    (qpat_x_assum ‘¬∀n. _’ mp_tac >> simp[NOT_LESS] >> strip_tac >>
     qexists_tac ‘n’ >> simp[] >> res_tac >> fs[]) >>
  ‘∀n. n1 ≤ n ⇒ (ss n).moved e = L’ by
    (rpt strip_tac >> ‘(ss n1).moved e ≤ (ss n).moved e’ by metis_tac[] >>
     ‘(ss n).moved e ≤ L’ by (qpat_x_assum ‘∀n. n0 ≤ n ⇒ (ss n).moved e ≤ L’ irule >> simp[]) >>
     metis_tac[LESS_EQUAL_ANTISYM]) >>
  ‘∃n2. n1 ≤ n2 ∧ (ss n2).moved e ≤ (ss n2).acked e’ by
    (qpat_x_assum ‘∀n1. ¬∀n. _’ (qspec_then ‘n1’ mp_tac) >> simp[NOT_LESS]) >>
  qexists_tac ‘n2’ >> simp[] >> rpt strip_tac >> TRY (res_tac >> NO_TAC) >>
  ‘(ss n2).acked e ≤ (ss n).acked e’ by metis_tac[] >>
  ‘(ss n).acked e ≤ (ss n).moved e ∧ (ss n2).acked e ≤ (ss n2).moved e’ by simp[] >>
  ‘(ss n2).moved e = L ∧ (ss n).moved e = L’ by simp[] >> fs[]
QED

(* N5, from the kernel fairness: the receiver (k', j') of end e asks
   infinitely often; once e has stopped sending, its bytes are all moved
   and acknowledged for good.  The ONLY use of kernel_fair_obs *)
Theorem drains_of_asks:
  l0sys_irun ps ss rs ∧ kernel_fair_obs ss rs ∧
  (ss n0).peer e = SOME (k', j') ∧ asks_io ss rs k' j' ∧
  (∀n. n0 ≤ n ⇒ LENGTH (sys_chan (ss n) e).sent = L) ⇒
  ∃n2. n0 ≤ n2 ∧ ∀n. n2 ≤ n ⇒ (ss n).moved e = L ∧ (ss n).acked e = L
Proof
  strip_tac >>
  drule irun_mono >> disch_then (qspec_then ‘e’ assume_tac) >>
  drule irun_kinv >> strip_tac >>
  ‘∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e = SOME (k', j')’ by
    (rpt strip_tac >> ‘(ss n).peer e = SOME (k', j')’ by metis_tac[] >>
     ‘kinv (ss n)’ by simp[] >> fs[kinv_def] >> metis_tac[]) >>
  ‘¬(∀n. n0 ≤ n ⇒ (ss n).moved e < LENGTH (sys_chan (ss n) e).sent)’ by
    (strip_tac >>
     ‘∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e = SOME (k', j') ∧
                   (ss n).moved e < LENGTH (sys_chan (ss n) e).sent’ by metis_tac[] >>
     metis_tac[kernel_fair_obs_def]) >>
  ‘∀n1. ¬(∀n. n1 ≤ n ⇒ (ss n).acked e < (ss n).moved e)’ by
    (rpt strip_tac >>
     ‘∀n. n0 + n1 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧
                        (ss n).acked e < (ss n).moved e’ by
       (rpt strip_tac >> ‘n0 ≤ n ∧ n1 ≤ n’ by simp[] >>
        qpat_x_assum ‘∀n. n0 ≤ n ⇒ is_end _ _ ∧ _’ (qspec_then ‘n’ mp_tac) >>
        qpat_x_assum ‘∀n. n1 ≤ n ⇒ _’ (qspec_then ‘n’ mp_tac) >> simp[]) >>
     metis_tac[kernel_fair_obs_def]) >>
  drule_all drains_of_fair >> simp[]
QED
