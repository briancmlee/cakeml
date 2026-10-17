(*
  honestL1EPAsks on the run (a lemma layer for proxyL0Stmts.proxy_asks_claim,
  revision 9): on the EP L1's run with pol_never, if from round N on no
  poll lists f for input, while f's handle h stays in the interest set,
  then f's inbox is never empty from N on (else eround_asks lists f), it
  never grows, and each round that reads h shrinks it; so only finitely
  many rounds read h.  The run's invariants come from
  honestL1EPRefine.l1ep_refines_ehl.
*)
Theory honestL1EPAsksRun
Ancestors
  honestL1EPAsks honestL1EPRefine honestL1EPModel honestL1PFAsks honestL1PFRefine
  honestL1PFModel honestL0World
Libs
  preamble

(* The run, with pol_never *)
Definition nrun_def:
  nrun lfd ifds m w0 n = THE (erounds lfd pol_never ifds m (w0, einit) n)
End

Definition erhist_def:
  erhist lfd ifds m w0 n = FST (nrun lfd ifds m w0 n)
End

Definition erworld_def:
  erworld lfd ifds m w0 n = FST (FST (SND (nrun lfd ifds m w0 n)))
End

Definition erstate_def:
  erstate lfd ifds m w0 n = SND (FST (SND (nrun lfd ifds m w0 n)))
End

(* Round n's events *)
Definition erevs_def:
  erevs lfd ifds m w0 n =
    case eround lfd pol_never (ifds (erhist lfd ifds m w0 n))
           (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n)
           (new_actions (log_of m) (erhist lfd ifds m w0 n)) of
    | SOME (_, _, _, evs) => evs
    | NONE => []
End

(* The run's hypotheses (those of l1ep_refines_ehl, and that it runs) *)
Definition erun_ok_def:
  erun_ok lfd ifds m w0 ⇔
    l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
    (∀n. SND (ecm lfd pol_never ifds m w0 n) + 1 < dimword (:64)) ∧
    ∀n. erounds lfd pol_never ifds m (w0, einit) n ≠ NONE
End

(* Round k lists f for input in a poll *)
Definition easked_at_def:
  easked_at lfd ifds m w0 k f ⇔
    ∃bs e. MEM (IO_event (ExtCall «sys_poll») [0w] bs) (erevs lfd ifds m w0 k) ∧
           MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e
End

(* Round k's actions read h *)
Definition ereads_at_def:
  ereads_at lfd ifds m w0 k h ⇔
    ∃n. MEM (ERead h n) (new_actions (log_of m) (erhist lfd ifds m w0 k))
End

(* The hypotheses of the quiet stretch from round N *)
Definition equiet_from_def:
  equiet_from lfd ifds m w0 N h f ⇔
    erun_ok lfd ifds m w0 ∧ ekeep lfd h f (erstate lfd ifds m w0 N) ∧
    ∀k. N ≤ k ⇒ MEM h (ifds (erhist lfd ifds m w0 k)) ∧ ¬easked_at lfd ifds m w0 k f
End

Theorem erun_some:
  erun_ok lfd ifds m w0 ⇒
  erounds lfd pol_never ifds m (w0, einit) n =
    SOME (erhist lfd ifds m w0 n, (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n),
          FST (SND (SND (nrun lfd ifds m w0 n))), SND (SND (SND (nrun lfd ifds m w0 n))))
Proof
  rw[erun_ok_def, erhist_def, erworld_def, erstate_def, nrun_def] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘erounds lfd pol_never ifds m (w0, einit) n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[]
QED

(* Round n, from the run's state n to its state n + 1 *)
Theorem erun_round:
  erun_ok lfd ifds m w0 ⇒
  ∃snap log.
    eround lfd pol_never (ifds (erhist lfd ifds m w0 n))
      (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n)
      (new_actions (log_of m) (erhist lfd ifds m w0 n)) =
    SOME (snap, (erworld lfd ifds m w0 (SUC n), erstate lfd ifds m w0 (SUC n)), log,
          erevs lfd ifds m w0 n)
Proof
  strip_tac >>
  drule erun_some >> disch_then (qspec_then ‘SUC n’ mp_tac) >>
  drule erun_some >> disch_then (qspec_then ‘n’ mp_tac) >>
  simp[erounds_def] >> strip_tac >> simp[AllCaseEqs()] >> strip_tac >>
  simp[erevs_def]
QED

Theorem erun_inv:
  erun_ok lfd ifds m w0 ⇒
  eown lfd (erstate lfd ifds m w0 n) ∧
  l0owne lfd (erworld lfd ifds m w0 n) (erstate lfd ifds m w0 n) ∧
  l0_rely (erworld lfd ifds m w0 n) ∧ fds_lt (erworld lfd ifds m w0 n)
Proof
  strip_tac >> drule erun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  qpat_x_assum ‘erun_ok _ _ _ _’ (strip_assume_tac o REWRITE_RULE [erun_ok_def]) >>
  drule_all l1ep_refines_ehl >>
  disch_then (qspecl_then [‘ARB’, ‘ARB’] strip_assume_tac) >> fs[]
QED

Theorem ekeep_fopen:
  ekeep lfd h f es ∧ l0owne lfd w es ∧ l0_rely w ∧ fds_lt w ⇒ fopen f w
Proof
  rw[fopen_def] >> fs[l0owne_def, l0own_def, ekeep_def] >>
  qpat_x_assum ‘∀f. f = lfd ∨ _ ⇒ MEM f (l0_used w)’ irule >>
  simp[MEM_MAP, EXISTS_PROD] >> metis_tac[ALOOKUP_MEM]
QED

Theorem equiet_round:
  equiet_from lfd ifds m w0 N h f ∧ N ≤ k ∧ ekeep lfd h f (erstate lfd ifds m w0 k) ⇒
  ekeep lfd h f (erstate lfd ifds m w0 (SUC k)) ∧
  inb_of (erstate lfd ifds m w0 k).p f ≠ [] ∧
  LENGTH (inb_of (erstate lfd ifds m w0 (SUC k)).p f) ≤
    LENGTH (inb_of (erstate lfd ifds m w0 k).p f) ∧
  (ereads_at lfd ifds m w0 k h ⇒
   LENGTH (inb_of (erstate lfd ifds m w0 (SUC k)).p f) <
     LENGTH (inb_of (erstate lfd ifds m w0 k).p f))
Proof
  strip_tac >>
  ‘erun_ok lfd ifds m w0 ∧ MEM h (ifds (erhist lfd ifds m w0 k)) ∧
   ¬easked_at lfd ifds m w0 k f’
    by (qpat_x_assum ‘equiet_from _ _ _ _ _ _ _’ mp_tac >> simp[equiet_from_def]) >>
  drule erun_round >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘fopen f (erworld lfd ifds m w0 k)’
    by (irule ekeep_fopen >> drule erun_inv >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
        simp[] >> metis_tac[]) >>
  ‘eown lfd (erstate lfd ifds m w0 (SUC k))’ by (drule erun_inv >> simp[]) >>
  qpat_x_assum ‘¬easked_at _ _ _ _ _ _’ mp_tac >> simp[easked_at_def] >> strip_tac >>
  ‘inb_of (erstate lfd ifds m w0 k).p f ≠ []’
    by (strip_tac >> drule_all eround_asks >> metis_tac[]) >>
  simp[] >>
  drule eround_quiet_f >> rpt (disch_then drule) >>
  impl_tac >- metis_tac[] >> simp[ereads_at_def]
QED

Theorem equiet_fkeep:
  equiet_from lfd ifds m w0 N h f ⇒
  ∀d. ekeep lfd h f (erstate lfd ifds m w0 (N + d)) ∧
      inb_of (erstate lfd ifds m w0 (N + d)).p f ≠ [] ∧
      ∀d'. d ≤ d' ⇒ LENGTH (inb_of (erstate lfd ifds m w0 (N + d')).p f) ≤
                    LENGTH (inb_of (erstate lfd ifds m w0 (N + d)).p f)
Proof
  strip_tac >>
  ‘∀d. ekeep lfd h f (erstate lfd ifds m w0 (N + d))’
    by (Induct
        >- (qpat_x_assum ‘equiet_from _ _ _ _ _ _ _’ mp_tac >> simp[equiet_from_def])
        >> drule equiet_round >> disch_then (qspec_then ‘N + d’ mp_tac) >>
        simp[ADD_CLAUSES]) >>
  gen_tac >> conj_tac >- simp[] >>
  conj_tac
  >- (drule equiet_round >> disch_then (qspec_then ‘N + d’ mp_tac) >> simp[]) >>
  Induct >> simp[] >> strip_tac >>
  Cases_on ‘d = SUC d'’ >> simp[] >>
  ‘d ≤ d'’ by simp[] >> first_x_assum drule >>
  drule equiet_round >> disch_then (qspec_then ‘N + d'’ mp_tac) >>
  simp[ADD_CLAUSES]
QED

(* Only finitely many rounds read h *)
Theorem equiet_reads_finite:
  equiet_from lfd ifds m w0 N h f ⇒
  ∃M. ∀k. M ≤ k ⇒ ¬ereads_at lfd ifds m w0 k h
Proof
  strip_tac >> drule equiet_fkeep >> strip_tac >>
  ‘∀L d. LENGTH (inb_of (erstate lfd ifds m w0 (N + d)).p f) = L ⇒
         ∃M. ∀k. M ≤ k ⇒ ¬ereads_at lfd ifds m w0 k h’
    suffices_by (disch_then (qspecl_then [‘LENGTH (inb_of (erstate lfd ifds m w0 N).p f)’, ‘0’]
                               mp_tac) >> simp[]) >>
  completeInduct_on ‘L’ >> rpt strip_tac >>
  Cases_on ‘∃k. N + d ≤ k ∧ ereads_at lfd ifds m w0 k h’
  >- (pop_assum strip_assume_tac >>
      ‘k = N + (k - N)’ by simp[] >> qabbrev_tac ‘e = k - N’ >>
      qpat_x_assum ‘k = _’ SUBST_ALL_TAC >>
      ‘LENGTH (inb_of (erstate lfd ifds m w0 (N + e)).p f) ≤ L’
        by (qpat_x_assum ‘∀d. ekeep _ _ _ _ ∧ _’ (qspec_then ‘d’ strip_assume_tac) >>
            first_x_assum (qspec_then ‘e’ mp_tac) >> simp[]) >>
      ‘ekeep lfd h f (erstate lfd ifds m w0 (N + e))’
        by (qpat_x_assum ‘∀d. ekeep _ _ _ _ ∧ _’ (qspec_then ‘e’ strip_assume_tac)) >>
      drule equiet_round >> disch_then (qspec_then ‘N + e’ mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspec_then
        ‘LENGTH (inb_of (erstate lfd ifds m w0 (SUC (N + e))).p f)’ mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then ‘SUC e’ mp_tac) >> simp[ADD_CLAUSES])
  >> qexists_tac ‘N + d’ >> metis_tac[]
QED
