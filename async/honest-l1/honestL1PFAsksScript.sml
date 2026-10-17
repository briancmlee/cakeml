(*
  When the prefetching L1 asks for input on an fd (a lemma layer for the
  proxy's asks claim, proxyL0Stmts.proxy_asks_claim, revision 9): with
  pol_never, a round that starts with L1 holding none of f's input, f's
  handle open and in the interest set, lists f for input in its poll.
  Unlike honestL1PFRound.pround_f, nothing is assumed of f's channel (no
  pending input) or of the round's writes.
*)
Theory honestL1PFAsks
Ancestors
  honestL1PFRound honestL1PFInv honestL1PFRefine honestL1PFModel honestL1Inv honestL1Model
  honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World honestL0
  asyncCore asyncLevel1 ffi
Libs
  preamble

(* The poll event of a poll set lists each of its entries *)
Theorem sys_poll_lists:
  sys_poll fes w = SOME (out, w', ev) ∧ l0_rely w ∧ small f ∧ e < 4 ∧ MEM (f, e) fes ⇒
  ∃bs. ev = IO_event (ExtCall «sys_poll») [0w] bs ∧
       MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs))))
Proof
  simp[sys_poll_def] >> strip_tac >>
  ‘LENGTH out = LENGTH (poll_buf fes)’
    by (gvs[l0_do_buf_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_buf_cases >> strip_tac >> simp[MAP_ZIP] >>
  simp[poll_buf_def, DROP_APPEND, pollfd_entries_buf, MAP_MAP_o, MEM_MAP] >>
  qexists_tac ‘pfd_bytes (f, e)’ >> conj_tac
  >- (drule_all pe_pfd_bytes >> simp[]) >>
  qexists_tac ‘(f, e)’ >> simp[]
QED

(* One round: L1 holds none of f's input at its start, and f's handle h is
   open and in the interest set: the round's poll lists f for input *)
Theorem pround_asks:
  pround lfd pol_never hs (w, ps) acts = SOME (snap, ws', log, evs) ∧
  winv w ∧ fkeep lfd h f ps ∧ psmall lfd ps ∧ MEM h hs ∧ inb_of ps f = [] ⇒
  ∃bs e. MEM (IO_event (ExtCall «sys_poll») [0w] bs) evs ∧
         MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all pacts_f >> strip_tac >>
  ‘psmall lfd pa’ by metis_tac[pacts_psmall] >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol_never pa hs’ >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) fes’
    by (qunabbrev_tac ‘fes’ >> irule pf_poll_set_small >> first_assum ACCEPT_TAC) >>
  ‘wants_input lfd pol_never pa f’
    by (qpat_x_assum ‘fkeep _ _ _ pa’ mp_tac >>
        simp[fkeep_def, wants_input_def, pol_never_def]) >>
  ‘(∃e. MEM (f, e) fes) ∧ (∀e. MEM (f, e) fes ⇒ ODD e)’
    by (qunabbrev_tac ‘fes’ >>
        qpat_x_assum ‘fkeep _ _ _ pa’ (strip_assume_tac o REWRITE_RULE [fkeep_def]) >>
        drule_all pf_poll_set_f >> simp[]) >>
  qpat_x_assum ‘l1_polls _ _ = _’ mp_tac >> simp[l1_polls_def, AllCaseEqs()] >>
  strip_tac >>
  ‘l0_rely wa’ by gvs[winv_def] >>
  ‘sys_poll fes wa = SOME (out, w1, ev)’ by asm_rewrite_tac[] >>
  ‘ODD e’ by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  ‘small f ∧ e < 4’
    by (qpat_x_assum ‘EVERY _ fes’ mp_tac >> simp[EVERY_MEM] >>
        disch_then drule >> simp[]) >>
  drule_all sys_poll_lists >> strip_tac >>
  qexistsl_tac [‘bs’, ‘e’] >>
  qpat_x_assum ‘_ ++ _ = tevs’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘[_] = pevs’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘ev = _’ SUBST_ALL_TAC >> simp[]
QED

(* The fetch leaves an fd it does not fetch on alone *)
Theorem pf_fetch_other:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ¬MEM f fs ⇒
    ps'.b = ps.b ∧ inb_of ps' f = inb_of ps f ∧ (MEM f ps'.eof ⇔ MEM f ps.eof)
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule >> simp[]) >>
  IF_CASES_TAC >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on ‘l0_res_of out’ >> gvs[] >> every_case_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[set_inb_fields]
QED

Theorem fkeep_inj:
  fkeep lfd h f ps ∧ ALOOKUP ps.b.tbl c = SOME f ⇒ c = h
Proof
  rw[fkeep_def]
QED

(* One action, seen from f's inbox: it never grows; a read of h takes from it *)
Theorem pdo_inb_f:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ fkeep lfd h f ps ⇒
  LENGTH (inb_of ps' f) ≤ LENGTH (inb_of ps f) ∧
  (∀k. a = Read h k ∧ inb_of ps f ≠ [] ⇒ LENGTH (inb_of ps' f) < LENGTH (inb_of ps f))
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- (gvs[AllCaseEqs()])
  >- (Cases_on ‘ALOOKUP ps.b.tbl c’ >> gvs[] >- (strip_tac >> gvs[fkeep_def]) >>
      rename1 ‘ALOOKUP _ c = SOME g’ >>
      ‘g = f ⇔ c = h’
        by (eq_tac >> strip_tac
            >- (irule fkeep_inj >> gvs[] >> metis_tac[])
            >> gvs[fkeep_def]) >>
      gvs[AllCaseEqs(), set_inb_fields] >> TRY (PairCases_on ‘z’) >> gvs[] >>
      rw[] >> gvs[inb_of_def] >> Cases_on ‘ALOOKUP ps.inb f’ >> gvs[] >>
      rename1 ‘bs ≠ []’ >> Cases_on ‘bs’ >> gvs[])
  >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[]
QED

(* A round's actions, seen from f's inbox *)
Theorem pacts_inb_f:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ fkeep lfd h f ps ⇒
    LENGTH (inb_of ps' f) ≤ LENGTH (inb_of ps f) ∧
    ((∃k. MEM (Read h k) acts) ∧ inb_of ps f ≠ [] ⇒
     LENGTH (inb_of ps' f) < LENGTH (inb_of ps f))
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo _ _ _ = SOME (r, (w1, ps1), evs1)’ >>
  drule_all pdo_f >> strip_tac >>
  drule_all pdo_inb_f >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac >- decide_tac >>
  simp[PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac
  >- (gvs[] >> first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >> decide_tac)
  >> Cases_on ‘inb_of ps1 f = []’
  >- (gvs[] >> Cases_on ‘inb_of ps f’ >> gvs[])
  >> ‘LENGTH (inb_of ps' f) < LENGTH (inb_of ps1 f)’ by metis_tac[] >>
  decide_tac
QED

Theorem fkeep_tail:
  fkeep lfd h f pa ∧ ps'.b.tbl = pa.b.tbl ∧ ps'.b.nxt = pa.b.nxt ∧
  (∀x. MEM x ps'.b.closing ⇒ MEM x pa.b.closing) ∧ ¬MEM f ps'.eof ∧ pown lfd ps' ⇒
  fkeep lfd h f ps'
Proof
  rw[fkeep_def] >> TRY (metis_tac[]) >>
  ‘MEM f (MAP SND ps'.b.tbl)’
    by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[ALOOKUP_MEM]) >>
  gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* One round with no poll listing f for input: f's handle stays, L1 fetches
   nothing on f, so f's inbox does not grow, and a read of h takes from it *)
Theorem pround_quiet_f:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ fkeep lfd h f ps ∧ psmall lfd ps ∧ pown lfd ps' ∧
  (∀bs e. MEM (IO_event (ExtCall «sys_poll») [0w] bs) evs ∧
          MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ⇒ ¬ODD e) ⇒
  fkeep lfd h f ps' ∧ LENGTH (inb_of ps' f) ≤ LENGTH (inb_of ps f) ∧
  ((∃k. MEM (Read h k) acts) ∧ inb_of ps f ≠ [] ⇒
   LENGTH (inb_of ps' f) < LENGTH (inb_of ps f))
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), l1_polls_def] >> strip_tac >> gvs[] >>
  drule_all pacts_f >> strip_tac >>
  drule_all pacts_inb_f >> strip_tac >>
  ‘psmall lfd pa’ by metis_tac[pacts_psmall] >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol pa hs’ >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) fes’
    by (qunabbrev_tac ‘fes’ >> irule pf_poll_set_small >> first_assum ACCEPT_TAC) >>
  ‘l0_rely wa’ by gvs[winv_def] >>
  ‘∀e. MEM (f, e) fes ⇒ ¬ODD e’
    by (rpt strip_tac >>
        qpat_x_assum ‘sys_poll _ _ = _’ assume_tac >>
        ‘small f ∧ e < 4’
          by (qpat_x_assum ‘EVERY _ fes’ mp_tac >> simp[EVERY_MEM] >>
              disch_then drule >> simp[]) >>
        drule_all sys_poll_lists >> strip_tac >>
        qpat_x_assum ‘∀bs e. _’ (qspecl_then [‘bs’, ‘e’] mp_tac) >>
        qpat_x_assum ‘ev = _’ SUBST_ALL_TAC >> simp[]) >>
  ‘¬MEM f (in_fds fes)’
    by (simp[in_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> qx_gen_tac ‘e’ >>
        qpat_x_assum ‘∀e. MEM (f, e) fes ⇒ _’ (qspec_then ‘e’ mp_tac) >>
        Cases_on ‘MEM (f, e) fes’ >> simp[]) >>
  ‘winv w1’
    by (qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
        drule_at (Pos last) winv_do_buf >> simp[]) >>
  qpat_x_assum ‘l1_flush _ _ = _’ assume_tac >>
  drule_all l1_flush_f >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule pf_fetch_other >> disch_then (qspec_then ‘f’ mp_tac) >>
  impl_tac >- simp[MEM_FILTER] >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3), _, _)’ >>
  qabbrev_tac ‘ps4 = stall_step (pf_held ps3) (outbox_of pa.b) log ps3’ >>
  ‘¬MEM f ps3.b.closing’
    by (qpat_x_assum ‘fkeep _ _ _ pa’ mp_tac >> simp[fkeep_def]) >>
  ‘¬MEM f ps4.b.closing’
    by (simp[Abbr ‘ps4’] >> qpat_x_assum ‘fkeep _ _ _ pa’ mp_tac >> simp[fkeep_def]) >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >>
  drule_all l1_reap_f >> strip_tac >>
  rpt conj_tac
  >- (‘ps3.b = b2’ by (qpat_x_assum ‘ps3.b = _’ mp_tac >> simp[]) >>
      ‘b2.tbl = pa.b.tbl ∧ b2.nxt = pa.b.nxt ∧ b2.closing = pa.b.closing’
        by (qpat_x_assum ‘∀f. winv w2 ∧ _’ (qspec_then ‘f’ strip_assume_tac) >> simp[]) >>
      ‘¬MEM f ps3.eof’
        by (qpat_x_assum ‘MEM f ps3.eof ⇔ _’ (REWRITE_TAC o single) >>
            qpat_x_assum ‘fkeep _ _ _ pa’ mp_tac >> simp[fkeep_def]) >>
      irule fkeep_tail >>
      qpat_x_assum ‘pown _ _’ (irule_at Any) >> simp[Abbr ‘ps4’] >>
      qexists_tac ‘pa’ >> qpat_x_assum ‘fkeep _ _ _ pa’ (REWRITE_TAC o single) >>
      qpat_x_assum ‘∀x. MEM x b4.closing ⇒ _’ mp_tac >>
      qpat_x_assum ‘b4.tbl = _’ (REWRITE_TAC o single) >>
      qpat_x_assum ‘b4.nxt = _’ (REWRITE_TAC o single) >> simp[])
  >> simp[Abbr ‘ps4’]
QED
