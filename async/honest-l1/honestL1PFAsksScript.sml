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
  honestL1PFRound honestL1PFInv honestL1PFModel honestL1Inv honestL1Model
  honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World honestL0
  asyncCore asyncLevel1 ffi
Libs
  preamble

(* The poll event of a poll set lists each of its entries *)
Theorem sys_poll_lists:
  sys_poll fes w = SOME (out, w', ev) ∧ l0_rely w ∧
  EVERY (λ(g, e). small g ∧ e < 4) fes ∧ MEM (f, e) fes ⇒
  ∃bs. ev = IO_event (ExtCall «sys_poll») [0w] bs ∧
       MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs))))
Proof
  simp[sys_poll_def] >> strip_tac >>
  ‘LENGTH out = LENGTH (poll_buf fes)’
    by (gvs[l0_do_buf_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_buf_cases >> strip_tac >> simp[MAP_ZIP] >>
  simp[poll_buf_def, DROP_APPEND, pollfd_entries_buf, MAP_MAP_o, MEM_MAP] >>
  qexists_tac ‘pfd_bytes (f, e)’ >> conj_tac
  >- (gvs[EVERY_MEM] >> first_x_assum drule >> simp[] >> strip_tac >>
      drule_all pe_pfd_bytes >> simp[]) >>
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
  drule_all sys_poll_lists >> strip_tac >>
  qexistsl_tac [‘bs’, ‘e’] >>
  qpat_x_assum ‘_ ++ _ = tevs’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘[_] = pevs’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘ev = _’ SUBST_ALL_TAC >> simp[]
QED
