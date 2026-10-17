(*
  honestKvL0Asks on the run, for any policy (moonshot-proxy's
  honestL1PFAsksRun, spike/proxy-e4, has it for pol_never).  If from round
  N on no poll lists f for input while f's handle h stays in the interest
  set, then f's handle stays, f's inbox never grows, and in every round f's
  inbox is non-empty or the policy pauses f after the server's actions
  (paused_at); and only finitely many rounds read h while f's inbox is
  non-empty.  For pol_self hw (paused_self): a pause means f's outbox was
  over hw at the round's start, or the round wrote on h.

  MAIN: quiet_round, quiet_fkeep, quiet_reads_finite, paused_self.
*)
Theory honestKvL0AsksRun
Ancestors
  honestKvL0Asks honestL1PFOutLive honestL1PFLive honestL1PFRound honestL1PFInv
  honestL1PFRefine honestL1PFModel honestL0World
Libs
  preamble

(* Round k lists f for input in a poll *)
Definition asked_at_def:
  asked_at lfd pol ifds m w0 k f ⇔
    ∃bs e. MEM (IO_event (ExtCall «sys_poll») [0w] bs) (rrev lfd pol ifds m w0 k) ∧
           MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e
End

(* Round k's actions read h *)
Definition reads_at_def:
  reads_at lfd pol ifds m w0 k h ⇔
    ∃n. MEM (Read h n) (new_actions (log_of m) (rhist lfd pol ifds m w0 k))
End

(* The policy pauses f after round k's actions *)
Definition paused_at_def:
  paused_at lfd pol ifds m w0 k f ⇔
    ∃rs aevs wa pa.
      pacts lfd (rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)
        (new_actions (log_of m) (rhist lfd pol ifds m w0 k)) = SOME (rs, aevs, (wa, pa)) ∧
      pol pa f
End

(* The hypotheses of the quiet stretch from round N *)
Definition quiet_from_def:
  quiet_from lfd pol ifds m w0 N h f ⇔
    oassm lfd pol ifds m w0 ∧ fkeep lfd h f (rstate lfd pol ifds m w0 N) ∧
    ∀k. N ≤ k ⇒ MEM h (ifds (rhist lfd pol ifds m w0 k)) ∧ ¬asked_at lfd pol ifds m w0 k f
End

Theorem quiet_round:
  quiet_from lfd pol ifds m w0 N h f ∧ N ≤ k ∧ fkeep lfd h f (rstate lfd pol ifds m w0 k) ⇒
  fkeep lfd h f (rstate lfd pol ifds m w0 (SUC k)) ∧
  (inb_of (rstate lfd pol ifds m w0 k) f ≠ [] ∨ paused_at lfd pol ifds m w0 k f) ∧
  LENGTH (inb_of (rstate lfd pol ifds m w0 (SUC k)) f) ≤
    LENGTH (inb_of (rstate lfd pol ifds m w0 k) f) ∧
  (reads_at lfd pol ifds m w0 k h ∧ inb_of (rstate lfd pol ifds m w0 k) f ≠ [] ⇒
   LENGTH (inb_of (rstate lfd pol ifds m w0 (SUC k)) f) <
     LENGTH (inb_of (rstate lfd pol ifds m w0 k) f))
Proof
  strip_tac >>
  ‘oassm lfd pol ifds m w0 ∧ MEM h (ifds (rhist lfd pol ifds m w0 k)) ∧
   ¬asked_at lfd pol ifds m w0 k f’
    by (qpat_x_assum ‘quiet_from _ _ _ _ _ _ _ _’ mp_tac >> simp[quiet_from_def]) >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0’ by gvs[oassm_def] >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by metis_tac[winv_run] >>
  ‘psmall lfd (rstate lfd pol ifds m w0 k)’ by metis_tac[psmall_run] >>
  ‘pown lfd (rstate lfd pol ifds m w0 (SUC k))’ by metis_tac[run_rel] >>
  qpat_x_assum ‘¬asked_at _ _ _ _ _ _ _’ mp_tac >> simp[asked_at_def] >> strip_tac >>
  conj_tac
  >- (drule pround_quiet_f >> rpt (disch_then drule) >>
      impl_tac >- metis_tac[] >> simp[]) >>
  conj_tac
  >- (simp[paused_at_def] >> CCONTR_TAC >> gvs[] >>
      drule pround_asks_pol >> rpt (disch_then drule) >> strip_tac >>
      qpat_x_assum ‘∀bs e. _’ (qspecl_then [‘bs’, ‘e’] mp_tac) >> simp[]) >>
  drule pround_quiet_f >> rpt (disch_then drule) >>
  impl_tac >- metis_tac[] >> simp[reads_at_def] >> metis_tac[]
QED

Theorem quiet_fkeep:
  quiet_from lfd pol ifds m w0 N h f ⇒
  ∀d. fkeep lfd h f (rstate lfd pol ifds m w0 (N + d)) ∧
      ∀d'. d ≤ d' ⇒ LENGTH (inb_of (rstate lfd pol ifds m w0 (N + d')) f) ≤
                    LENGTH (inb_of (rstate lfd pol ifds m w0 (N + d)) f)
Proof
  strip_tac >>
  ‘∀d. fkeep lfd h f (rstate lfd pol ifds m w0 (N + d))’
    by (Induct
        >- (qpat_x_assum ‘quiet_from _ _ _ _ _ _ _ _’ mp_tac >> simp[quiet_from_def])
        >> drule quiet_round >> disch_then (qspec_then ‘N + d’ mp_tac) >>
        simp[ADD_CLAUSES]) >>
  gen_tac >> conj_tac >- simp[] >>
  Induct >> simp[] >> strip_tac >>
  Cases_on ‘d = SUC d'’ >> simp[] >>
  ‘d ≤ d'’ by simp[] >> first_x_assum drule >>
  drule quiet_round >> disch_then (qspec_then ‘N + d'’ mp_tac) >>
  simp[ADD_CLAUSES]
QED

(* Only finitely many rounds read h while f's inbox is non-empty *)
Theorem quiet_reads_finite:
  quiet_from lfd pol ifds m w0 N h f ⇒
  ∃M. ∀k. M ≤ k ∧ reads_at lfd pol ifds m w0 k h ⇒ inb_of (rstate lfd pol ifds m w0 k) f = []
Proof
  strip_tac >> drule quiet_fkeep >> strip_tac >>
  ‘∀L d. LENGTH (inb_of (rstate lfd pol ifds m w0 (N + d)) f) = L ⇒
         ∃M. ∀k. M ≤ k ∧ reads_at lfd pol ifds m w0 k h ⇒
                 inb_of (rstate lfd pol ifds m w0 k) f = []’
    suffices_by (disch_then (qspecl_then [‘LENGTH (inb_of (rstate lfd pol ifds m w0 N) f)’, ‘0’] mp_tac) >> simp[]) >>
  completeInduct_on ‘L’ >> rpt strip_tac >>
  Cases_on ‘∃k. N + d ≤ k ∧ reads_at lfd pol ifds m w0 k h ∧
                inb_of (rstate lfd pol ifds m w0 k) f ≠ []’
  >- (pop_assum strip_assume_tac >>
      ‘k = N + (k - N)’ by simp[] >> qabbrev_tac ‘e = k - N’ >>
      qpat_x_assum ‘k = N + e’ SUBST_ALL_TAC >>
      ‘LENGTH (inb_of (rstate lfd pol ifds m w0 (N + e)) f) ≤ L’
        by (qpat_x_assum ‘∀d. fkeep _ _ _ _ ∧ _’ (qspec_then ‘d’ strip_assume_tac) >>
            first_x_assum (qspec_then ‘e’ mp_tac) >> simp[]) >>
      ‘fkeep lfd h f (rstate lfd pol ifds m w0 (N + e))’
        by (qpat_x_assum ‘∀d. fkeep _ _ _ _ ∧ _’ (qspec_then ‘e’ strip_assume_tac)) >>
      drule quiet_round >> disch_then (qspec_then ‘N + e’ mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspec_then
        ‘LENGTH (inb_of (rstate lfd pol ifds m w0 (SUC (N + e))) f)’ mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then ‘SUC e’ mp_tac) >> simp[ADD_CLAUSES])
  >> qexists_tac ‘N + d’ >> metis_tac[]
QED

(* MAIN: for pol_self hw, a pause means f's outbox was over hw at the
   round's start, or the round wrote on h *)
Theorem paused_self:
  paused_at lfd (pol_self hw) ifds m w0 k f ∧ oassm lfd (pol_self hw) ifds m w0 ∧
  fkeep lfd h f (rstate lfd (pol_self hw) ifds m w0 k) ⇒
  hw < LENGTH (outbox_of (rstate lfd (pol_self hw) ifds m w0 k).b f) ∨
  ∃bs. MEM (Write h bs) (new_actions (log_of m) (rhist lfd (pol_self hw) ifds m w0 k)) ∧
       bs ≠ []
Proof
  rw[paused_at_def] >>
  ‘run_ok lfd (pol_self hw) ifds m w0 ∧ winv w0’ by gvs[oassm_def] >>
  ‘winv (rworld lfd (pol_self hw) ifds m w0 k)’ by metis_tac[winv_run] >>
  drule_all pacts_f >> strip_tac >>
  Cases_on ‘∀bs. MEM (Write h bs)
                 (new_actions (log_of m) (rhist lfd (pol_self hw) ifds m w0 k)) ⇒ bs = []’
  >- (qpat_x_assum ‘(∀bs. _) ⇒ _’ mp_tac >> impl_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum ‘pol_self _ _ _’ mp_tac >> simp[pol_self_def]) >>
  disj2_tac >> qpat_x_assum ‘¬∀bs. _’ mp_tac >> simp[NOT_FORALL_THM] >> metis_tac[]
QED
