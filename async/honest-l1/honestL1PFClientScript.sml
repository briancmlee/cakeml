(*
  Live-data, part (B) (design/36 §6): what L1 fetches on an fd f is client
  j's data in the version-2 world built from its run (psk), with
  j = cl (pcm a) f for f's accept round a; FEof / FReset on f become
  Eof2 j.  Then (A) and (B) together: what c's kernel inbox holds is
  eventually client j's data in psk, unless the episode ended.
*)
Theory honestL1PFClient
Ancestors
  honestL1PFStream honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel
  honestL1Model honestL0World honestL0 socketV2FFI asyncCore alist
Libs
  preamble

(* Client j's data, and whether it ended, in a list of v2 arrivals *)
Definition cdata_def:
  cdata j as =
    FLAT (MAP (λa. case a of Data2 i bs => if i = j then bs else [] | _ => []) as)
End

Definition cend_def:
  cend j as ⇔ MEM (Eof2 j) as
End

Theorem cdata_simps[simp]:
  cdata j [] = [] ∧
  cdata j (Data2 i bs :: as) = (if i = j then bs else []) ++ cdata j as ∧
  cdata j (Eof2 i :: as) = cdata j as ∧
  cdata j (Connect2 l :: as) = cdata j as ∧
  (cend j [] ⇔ F) ∧
  (cend j (Data2 i bs :: as) ⇔ cend j as) ∧
  (cend j (Eof2 i :: as) ⇔ i = j ∨ cend j as) ∧
  (cend j (Connect2 l :: as) ⇔ cend j as)
Proof
  rw[cdata_def, cend_def] >> metis_tac[]
QED

(* The fds a fetch log reports input on *)
Definition log_fds_def:
  log_fds l = FLAT (MAP (λx. case x of FData g bs => [g] | FEof g => [g]
                                     | FReset g => [g] | FConn g => []) l)
End

Definition log_conns_def:
  log_conns l = FLAT (MAP (λx. case x of FConn g => [g] | _ => []) l)
End

Theorem cl_other:
  ALL_DISTINCT (MAP SND cm) ∧ ALOOKUP cm f = SOME j ∧ MEM g (MAP FST cm) ∧ g ≠ f ⇒
  cl cm g ≠ j
Proof
  rw[cl_def] >> CASE_TAC >- gvs[ALOOKUP_NONE] >>
  strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
  metis_tac[snd_unique]
QED

(* arrs turns f's entries into client j's arrivals, given that every fd the
   log reports input on is mapped, and that f is not reconnected *)
Theorem arrs_client:
  ∀l cm k as cm' k'.
    arrs lfd (cm, k) l = (as, (cm', k')) ∧
    ALL_DISTINCT (MAP SND cm) ∧ EVERY (λi. i < k) (MAP SND cm) ∧
    ALOOKUP cm f = SOME j ∧
    (∀g. MEM g (log_fds l) ⇒ MEM g (MAP FST cm)) ∧ ¬MEM f (log_conns l) ⇒
    cdata j as = fdata f l ∧ (cend j as ⇔ fend f l) ∧ ALOOKUP cm' f = SOME j
Proof
  Induct >- simp[arrs_def] >>
  Cases >> rpt gen_tac >> simp[arrs_def] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[log_fds_def, log_conns_def]
  >- ((* FConn *)
      first_x_assum drule >> impl_tac
      >- (gvs[EVERY_MEM] >> rpt conj_tac >> rpt strip_tac >> gvs[] >>
          TRY (qpat_x_assum ‘∀i. MEM i _ ⇒ _’ drule >> simp[] >> NO_TAC) >>
          res_tac >> gvs[]) >>
      simp[])
  >> first_x_assum drule >> simp[] >> strip_tac >> simp[] >>
  ‘cl cm c = j ⇔ c = f’
    by (eq_tac
        >- (strip_tac >> CCONTR_TAC >>
            ‘MEM c (MAP FST cm)’
              by (qpat_x_assum ‘∀g. _ ⇒ MEM g (MAP FST cm)’ (qspec_then ‘c’ mp_tac) >>
                  simp[]) >>
            metis_tac[cl_other]) >>
        rw[] >> simp[cl_def]) >>
  simp[] >> rw[] >> gvs[]
QED

Theorem log_simps[simp]:
  log_fds [] = [] ∧ log_conns [] = [] ∧
  log_fds (x :: l) = (case x of FData g bs => [g] | FEof g => [g]
                              | FReset g => [g] | FConn g => []) ++ log_fds l ∧
  log_conns (x :: l) = (case x of FConn g => [g] | _ => []) ++ log_conns l ∧
  log_fds (l1 ++ l2) = log_fds l1 ++ log_fds l2 ∧
  log_conns (l1 ++ l2) = log_conns l1 ++ log_conns l2
Proof
  simp[log_fds_def, log_conns_def]
QED

(* The fetch reports input only on the fds it was given, never the listener *)
Theorem pf_fetch_fds:
  ∀fs ws ws' log evs.
    pf_fetch lfd hw fs ws = SOME (ws', log, evs) ⇒
    ∀g. MEM g (log_fds log) ⇒ MEM g fs ∧ g ≠ lfd
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >> PairCases_on ‘ws’ >>
  simp[Once pf_fetch_def] >> rw[] >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >> simp[] >>
  rw[] >> gvs[]
QED

(* The fetch never reports a new connection on an fd in use *)
Theorem pf_fetch_conns:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ MEM f (l0_used w) ⇒
    ¬MEM f (log_conns log)
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >>
  simp[Once pf_fetch_def] >> rw[] >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  ‘MEM f (l0_used w1)’
    by (gvs[sys_accept_def, sys_recv_def] >> drule l0_do_used >> simp[]) >>
  first_x_assum drule_all >> simp[] >>
  ‘l0_rely w ∧ fds_lt w’ by fs[winv_def] >>
  ‘¬MEM (n2w k) (l0_used w)’ by (irule sys_accept_fresh >> metis_tac[]) >>
  strip_tac >> strip_tac >> gvs[]
QED

(* A round's log reports input only on mapped fds, and never reconnects an
   open f *)
Theorem pround_client:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ fl w f R ∧ fkeep lfd h f ps ⇒
  (∀g. MEM g (log_fds log) ⇒ MEM g (MAP FST cm)) ∧ ¬MEM f (log_conns log)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule_all pacts_hacts >> strip_tac >>
  drule_all pacts_fl >> strip_tac >>
  drule_all pacts_winv >> strip_tac >>
  drule_all l1_polls_fl >> strip_tac >>
  drule_all l1_polls_winv >> strip_tac >>
  drule_all l1_flush_fl >> strip_tac >>
  drule_all l1_flush_winv >> strip_tac >>
  drule_all l1_flush_f >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> drule pf_fetch_fds >> disch_then drule >> simp[MEM_FILTER] >>
      strip_tac >> drule in_fds_poll_set >> simp[] >> strip_tac >>
      ‘ALL_DISTINCT (MAP FST pa.b.tbl)’ by gvs[pown_def] >>
      drule_all tbl_alookup_exists >> strip_tac >>
      gvs[pv_rel_def] >> metis_tac[])
  >> irule pf_fetch_conns >> rpt (goal_assum drule) >> metis_tac[fl_used]
QED
