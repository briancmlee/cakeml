(*
  An fd at end-of-file leaves the handle table (design/47 D, close step;
  D27): on the PF echo run, if L1 holds f under handle h with f's EOF
  seen, then some round k ≥ n still holds f under h and round k + 1 holds
  f under no handle (it was closed, or moved to closing, by the Read at
  EOF).

  While f stays in the table at EOF, nothing more is fetched on it (the
  fetch wants no input on an fd at EOF), so L1's input of f only shrinks,
  and each Read of h takes at least one byte or, once the input is used
  up, closes f.  The echo reads h within three rounds
  (echo_read_soon_eof), so the input runs out and f leaves.

  MAIN: echo_eof_leave (from the generic eof_leave).
*)
Theory honestEchoL0EofLeave
Ancestors
  honestEchoL0EofRead honestEchoL0Stop honestEchoL0Obl honestL1PFObl honestL1PFS4w
  honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel honestL1Steps
  honestL1Model
Libs
  preamble

(* ------------------------------------------------------------------------
   Within a round's actions
   ------------------------------------------------------------------------ *)

(* f is at EOF under h alone, awaits no handle, and every handle is issued *)
Definition einv_def:
  einv lfd h f ps ⇔
    ALOOKUP ps.b.tbl h = SOME f ∧ (∀h'. MEM (h', f) ps.b.tbl ⇒ h' = h) ∧
    MEM f ps.eof ∧ ¬MEM f ps.acq ∧ f ≠ lfd ∧
    (∀h' g. ALOOKUP ps.b.tbl h' = SOME g ⇒ ∃i. i < ps.b.nxt ∧ h' = l1hdl lfd i)
End

(* f is in neither the table nor the accept queue *)
Definition gout_def:
  gout f ps ⇔ ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq
End

Theorem MEM_SND_ALOOKUP[local]:
  MEM f (MAP SND l) ⇔ ∃h. MEM (h, f) l
Proof
  simp[MEM_MAP, EXISTS_PROD]
QED

Theorem ALOOKUP_FILTER_KEY[local]:
  ∀l. ALOOKUP (FILTER (λp. FST p ≠ c) l) k = if k = c then NONE else ALOOKUP l k
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem pdo_gout[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ gout f ps ⇒ gout f ps'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule l1_close_b >> strip_tac) >> TRY (drule l1do_write_tbl >> strip_tac) >>
  gvs[gout_def, set_inb_def, MEM_SND_ALOOKUP, ADELKEY_def, MEM_FILTER]
QED

Theorem pacts_gout[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ gout f ps ⇒ gout f ps'
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  metis_tac[pdo_gout]
QED

Theorem pdo_einv[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ einv lfd h f ps ⇒
  (einv lfd h f ps' ∧ LENGTH (inb_of ps' f) ≤ LENGTH (inb_of ps f) ∧
   (∀kk. a = Read h kk ⇒ LENGTH (inb_of ps' f) < LENGTH (inb_of ps f))) ∨
  gout f ps'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept: the new handle is fresh, its fd is not f *)
      qpat_x_assum ‘_ = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘ps.acq’ >> gvs[AllCaseEqs()] >> disj1_tac >>
      qpat_x_assum ‘einv _ _ _ _’ mp_tac >> simp[einv_def, inb_of_def] >> strip_tac >>
      ‘∃i. i < ps.b.nxt ∧ h = hdl lfd i’ by metis_tac[] >>
      ‘hdl lfd ps.b.nxt ≠ h’
        by (gvs[] >> simp[Once EQ_SYM_EQ] >> irule hdl_fresh >> fs[]) >>
      simp[] >> rpt conj_tac >> rw[] >>
      TRY (qexists_tac ‘ps.b.nxt’ >> simp[] >> NO_TAC) >>
      TRY (gvs[] >> NO_TAC) >>
      qpat_x_assum ‘∀h'' g. _’ drule >> strip_tac >> qexists_tac ‘i'’ >> simp[])
  >- ((* Read *)
      Cases_on ‘ALOOKUP ps.b.tbl c’ >> gvs[] >>
      TRY (strip_tac >> gvs[einv_def] >> NO_TAC) >>
      rename1 ‘ALOOKUP _ c = SOME g’ >>
      ‘g = f ⇔ c = h’ by (gvs[einv_def] >> metis_tac[SOME_11, ALOOKUP_MEM]) >>
      Cases_on ‘c = h’
      >- ((* f's own handle *)
          gvs[] >> Cases_on ‘inb_of ps f = []’ >> gvs[AllCaseEqs()] >>
          TRY (PairCases_on ‘z’ >> gvs[] >> drule l1_close_b >> strip_tac) >>
          FIRST [
            gvs[einv_def] >> NO_TAC,
            disj1_tac >> gvs[einv_def, set_inb_def] >> Cases_on ‘inb_of ps f’ >> gvs[] >> NO_TAC,
            TRY disj2_tac >> qpat_x_assum ‘einv _ _ _ _’ mp_tac >>
            simp[einv_def, gout_def, MEM_SND_ALOOKUP, ADELKEY_def, MEM_FILTER, FORALL_PROD] >>
            metis_tac[]])
      >> (* another handle: g ≠ f *)
      disj1_tac >> gvs[AllCaseEqs()] >> TRY (PairCases_on ‘z’ >> gvs[]) >>
      TRY (drule l1_close_b >> strip_tac) >>
      gvs[einv_def, set_inb_def, inb_of_set_inb, ADELKEY_def, MEM_FILTER, ALOOKUP_FILTER_KEY] >>
      rw[] >> gvs[inb_of_def, ALOOKUP_FILTER_KEY] >> metis_tac[])
  >> (* Write *)
  disj1_tac >> gvs[AllCaseEqs()] >> PairCases_on ‘z’ >> gvs[] >>
  drule l1do_write_tbl >> strip_tac >> gvs[einv_def, inb_of_def]
QED

Theorem pacts_einv[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ einv lfd h f ps ⇒
    (einv lfd h f ps' ∧ LENGTH (inb_of ps' f) ≤ LENGTH (inb_of ps f) ∧
     ((∃kk. MEM (Read h kk) acts) ⇒ LENGTH (inb_of ps' f) < LENGTH (inb_of ps f))) ∨
    gout f ps'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> PairCases_on ‘ws1’ >>
  drule_all pdo_einv >> strip_tac
  >- (first_x_assum drule_all >> strip_tac >> simp[] >> rpt strip_tac >> disj1_tac >>
      gvs[] >>
      TRY (‘LENGTH (inb_of ps' f) < LENGTH (inb_of ws11 f)’ by metis_tac[]) >>
      TRY (‘LENGTH (inb_of ws11 f) < LENGTH (inb_of ps f)’ by metis_tac[]) >>
      decide_tac)
  >> disj2_tac >> metis_tac[pacts_gout]
QED

(* ------------------------------------------------------------------------
   The round's tail
   ------------------------------------------------------------------------ *)

Theorem pf_fetch_eofkeep[local]:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ MEM f ps.eof ∧ f ≠ lfd ⇒
    MEM f ps'.eof ∧ inb_of ps' f = inb_of ps f
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  ‘¬wants_input lfd pol ps f’ by simp[wants_input_def] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  ‘h ≠ f’ by (strip_tac >> gvs[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs()] >> strip_tac >> pairarg_tac >> gvs[AllCaseEqs()] >>
      first_x_assum drule >> simp[inb_of_def])
  >> simp[AllCaseEqs()] >> strip_tac >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[inb_of_set_inb]
QED

Theorem pf_tail_eofkeep[local]:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ MEM f ps.eof ∧ f ≠ lfd ⇒
  MEM f ps'.eof ∧ inb_of ps' f = inb_of ps f ∧ ps'.b.tbl = ps.b.tbl
Proof
  strip_tac >> drule pf_tail_tbl >> strip_tac >> simp[] >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  qspecl_then [‘FILTER (λf. MEM f (in_fds (pf_poll_set lfd pol ps hs))) (readable_fds rv)’,
               ‘w2’, ‘ps with b := b2’, ‘w3’, ‘ps3'’, ‘log’, ‘gevs’]
    mp_tac pf_fetch_eofkeep >>
  simp[] >> simp[inb_of_def]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem ALL_DISTINCT_SND[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (a, v) l ∧ MEM (b, v) l ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem pown_einv[local]:
  pown lfd ps ∧ ALOOKUP ps.b.tbl h = SOME f ∧ MEM f ps.eof ⇒ einv lfd h f ps
Proof
  rw[pown_def, einv_def] >> imp_res_tac ALOOKUP_MEM >>
  ‘MEM f (MAP SND ps.b.tbl)’ by (simp[MEM_SND_ALOOKUP] >> metis_tac[]) >>
  gvs[ALL_DISTINCT_APPEND] >> rpt strip_tac >> res_tac >> metis_tac[ALL_DISTINCT_SND]
QED

Theorem pround_einv:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ pown lfd ps ∧
  ALOOKUP ps.b.tbl h = SOME f ∧ MEM f ps.eof ⇒
  (ALOOKUP ps'.b.tbl h = SOME f ∧ MEM f ps'.eof ∧
   LENGTH (inb_of ps' f) ≤ LENGTH (inb_of ps f) ∧
   ((∃kk. MEM (Read h kk) acts) ⇒ LENGTH (inb_of ps' f) < LENGTH (inb_of ps f))) ∨
  ¬MEM f (MAP SND ps'.b.tbl)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pown_einv >> strip_tac >>
  drule_all pacts_einv >> strip_tac
  >- (‘MEM f ws11.eof ∧ f ≠ lfd’ by fs[einv_def] >>
      drule_all pf_tail_eofkeep >> strip_tac >> disj1_tac >> gvs[einv_def])
  >> disj2_tac >> drule pf_tail_tbl >> strip_tac >> gvs[gout_def]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem step_einv[local]:
  run_hyp lfd pol ifds m w0 ⇒
  ∀n h f.
    ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧ MEM f (rstate lfd pol ifds m w0 n).eof ⇒
    (ALOOKUP (rstate lfd pol ifds m w0 (SUC n)).b.tbl h = SOME f ∧ MEM f (rstate lfd pol ifds m w0 (SUC n)).eof ∧
     LENGTH (inb_of (rstate lfd pol ifds m w0 (SUC n)) f) ≤ LENGTH (inb_of (rstate lfd pol ifds m w0 n) f) ∧
     ((∃kk. MEM (Read h kk) (new_actions (log_of m) (rhist lfd pol ifds m w0 n))) ⇒
      LENGTH (inb_of (rstate lfd pol ifds m w0 (SUC n)) f) < LENGTH (inb_of (rstate lfd pol ifds m w0 n) f))) ∨
    ¬MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC n)).b.tbl)
Proof
  rpt strip_tac >> ‘run_ok lfd pol ifds m w0’ by fs[run_hyp_def] >>
  drule_then (qspec_then ‘n’ strip_assume_tac) prun_step >>
  ‘pown lfd (rstate lfd pol ifds m w0 n)’ by metis_tac[run_pown] >>
  drule pround_einv >> simp[]
QED

Theorem span_einv[local]:
  run_hyp lfd pol ifds m w0 ∧ ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧ MEM f (rstate lfd pol ifds m w0 n).eof ⇒
  ∀d. (∃k. n ≤ k ∧ ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME f ∧ ¬MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl)) ∨
      (ALOOKUP (rstate lfd pol ifds m w0 (n + d)).b.tbl h = SOME f ∧ MEM f (rstate lfd pol ifds m w0 (n + d)).eof ∧
       LENGTH (inb_of (rstate lfd pol ifds m w0 (n + d)) f) ≤ LENGTH (inb_of (rstate lfd pol ifds m w0 n) f))
Proof
  strip_tac >> Induct >- simp[] >>
  qpat_x_assum ‘_ ∨ _’ strip_assume_tac >- (disj1_tac >> metis_tac[]) >>
  ‘n + SUC d = SUC (n + d)’ by decide_tac >> pop_assum SUBST1_TAC >>
  drule step_einv >> disch_then (qspecl_then [‘n + d’, ‘h’, ‘f’] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac
  >- (disj2_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      irule LESS_EQ_TRANS >>
      qexists_tac ‘LENGTH (inb_of (rstate lfd pol ifds m w0 (n + d)) f)’ >>
      conj_tac >> first_assum ACCEPT_TAC)
  >> disj1_tac >> qexists_tac ‘n + d’ >> simp[]
QED

Theorem eof_leave:
  run_hyp lfd pol ifds m w0 ∧
  (∀n. ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧
       MEM f (rstate lfd pol ifds m w0 n).eof ⇒
       ∃i kk. i ≤ 3 ∧ MEM (Read h kk) (new_actions (log_of m) (rhist lfd pol ifds m w0 (n + i)))) ∧
  ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧
  MEM f (rstate lfd pol ifds m w0 n).eof ⇒
  ∃k. n ≤ k ∧ ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME f ∧
      ¬MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl)
Proof
  strip_tac >>
  ‘∀x n1. LENGTH (inb_of (rstate lfd pol ifds m w0 n1) f) = x ∧ ALOOKUP (rstate lfd pol ifds m w0 n1).b.tbl h = SOME f ∧
         MEM f (rstate lfd pol ifds m w0 n1).eof ⇒
         ∃k. n1 ≤ k ∧ ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME f ∧
             ¬MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl)’ suffices_by metis_tac[] >>
  completeInduct_on ‘x’ >> rpt strip_tac >>
  qpat_assum ‘∀n. ALOOKUP _ _ = SOME f ∧ _ ⇒ ∃i kk. _’ (qspec_then ‘n1’ mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.INST [‘n’ |-> ‘n1’] span_einv) >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then ‘i’ strip_assume_tac) >- metis_tac[] >>
  drule step_einv >> disch_then (qspecl_then [‘n1 + i’, ‘h’, ‘f’] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac
  >- (‘LENGTH (inb_of (rstate lfd pol ifds m w0 (SUC (n1 + i))) f) < x’
        by (‘LENGTH (inb_of (rstate lfd pol ifds m w0 (SUC (n1 + i))) f) < LENGTH (inb_of (rstate lfd pol ifds m w0 (n1 + i)) f)’
              by metis_tac[] >> decide_tac) >>
      first_x_assum drule >> disch_then (qspec_then ‘SUC (n1 + i)’ mp_tac) >>
      simp[] >> strip_tac >> qexists_tac ‘k’ >> simp[])
  >> qexists_tac ‘n1 + i’ >> simp[]
QED

(* MAIN: on the PF echo run, an fd held at EOF leaves the handle table *)
Theorem echo_eof_leave:
  echo_run lfdn pol w0 ∧
  ALOOKUP (rstate (n2w lfdn) pol EI ES w0 n).b.tbl h = SOME f ∧
  MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof ⇒
  ∃k. n ≤ k ∧ ALOOKUP (rstate (n2w lfdn) pol EI ES w0 k).b.tbl h = SOME f ∧
      ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl)
Proof
  strip_tac >> irule eof_leave >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      ‘∃i kk. i ≤ 3 ∧ MEM (Read h kk)
                (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 (n' + i)))’
        by (irule echo_read_soon_eof >> simp[]) >>
      qexistsl_tac [‘i’, ‘kk’] >> fs[])
  >> metis_tac[echo_run_hyp]
QED
