(*
  The output side of the proxy's asks claim (proxyL0Stmts.proxy_asks_claim,
  revision 9; S4 of the plan): on the EP L1's run, if from round N on
  nothing is written to g's handle h and h keeps naming g, then g's
  outbox is empty at some round.  Without writes the outbox never grows;
  once it stops shrinking, each round raises g's stall count, and at
  pf_sendwait L1 drops g's output itself (D23).  No world fact beyond
  what the run's invariants give: no drains, F1 or F2.

  okeep is honestL1EPAsks.ekeep without its EOF clause (a read of h at
  EOF auto-closes h; then h is gone for good, hgone, which a round end
  where h still names g rules out).
*)
Theory honestL1EPOutStall
Ancestors
  honestL1EPAsksRun honestL1EPAsks honestL1EPRefine honestL1EPModel honestL1PFOutLive
  honestL1PFOut honestL1PFAsks honestL1PFRound honestL1PFRefine honestL1PFInv honestL1PFModel
  honestL1Model honestL1Props honestL1Steps honestL0WorldProps honestL0Rely honestL0World
  honestL0 asyncCore asyncLevel1 ffi
Libs
  preamble

(* L1's view of g's handle h, for g's output *)
Definition okeep_def:
  okeep lfd h g es ⇔
    ALOOKUP es.p.b.tbl h = SOME g ∧ (∀h'. ALOOKUP es.p.b.tbl h' = SOME g ⇒ h' = h) ∧
    ¬MEM g es.p.b.closing ∧ ¬MEM g es.p.acq ∧ g ≠ lfd ∧
    ALOOKUP es.ctbl h = NONE ∧ ¬MEM g (MAP SND es.ctbl) ∧
    ∃j. h = l1hdl lfd j ∧ j < es.p.b.nxt ∧ j + 1 < dimword (:64)
End

(* h was issued and has left both tables: it never comes back *)
Definition hgone_def:
  hgone lfd h es ⇔
    ALOOKUP es.p.b.tbl h = NONE ∧ ALOOKUP es.ctbl h = NONE ∧
    ∃j. h = l1hdl lfd j ∧ j < es.p.b.nxt ∧ j + 1 < dimword (:64)
End

Theorem hdl_new:
  h = l1hdl lfd j ∧ j < nxt ∧ j + 1 < dimword (:64) ∧
  hdln (w2n lfd) nxt < 18446744073709551616 ⇒
  hdl lfd nxt ≠ h
Proof
  rw[] >> strip_tac >>
  ‘l1hdln (w2n lfd) j < dimword (:64)’ by simp[l1hdln_lt] >>
  qspecl_then [‘lfd’, ‘nxt’, ‘j’] mp_tac (Q.GENL [‘lfd’, ‘i’, ‘j’] l1hdl_11) >>
  gvs[]
QED

Theorem okeep_b:
  okeep lfd h g es ∧ b'.tbl = es.p.b.tbl ∧ b'.nxt = es.p.b.nxt ∧
  (∀x. MEM x b'.closing ⇒ MEM x es.p.b.closing) ⇒
  okeep lfd h g (es with p := es.p with b := b')
Proof
  rw[okeep_def] >> metis_tac[]
QED

Theorem okeep_adel:
  okeep lfd h g es ∧ k ≠ h ∧ k' ≠ g ∧ b'.tbl = ADELKEY k es.p.b.tbl ∧ b'.nxt = es.p.b.nxt ∧
  (∀x. MEM x b'.closing ⇒ MEM x es.p.b.closing ∨ x = k') ⇒
  okeep lfd h g (es with p := es.p with <| b := b'; eof := eof' |>)
Proof
  rw[okeep_def, ALOOKUP_ADELKEY] >> metis_tac[]
QED

Theorem okeep_ec_del:
  okeep lfd h g es ∧ k ≠ h ⇒ okeep lfd h g (ec_del k k' es)
Proof
  rw[okeep_def, ec_del_def, ALOOKUP_ADELKEY] >> fs[MEM_MAP, MEM_FILTER, ADELKEY_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The actions
   ------------------------------------------------------------------------ *)

Theorem edo_stalls:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒ es'.p.stalls = es.p.stalls
Proof
  Cases_on ‘a’ >> simp[edo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’ >> gvs[]) >> TRY (PairCases_on ‘x’ >> gvs[]) >>
  imp_res_tac pdo_stalls >> gvs[ec_del_def]
QED

Theorem eacts_stalls:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ⇒ es'.p.stalls = es.p.stalls
Proof
  Induct >> simp[eacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac edo_stalls >> first_x_assum drule >> simp[]
QED

Theorem forget_outbox_of:
  outbox_of (forget g b) f = (if f = g then [] else outbox_of b f) ∧
  (forget g b).tbl = b.tbl ∧ (forget g b).nxt = b.nxt
Proof
  simp[forget_def, outbox_of_set_outbox] >> rw[outbox_of_def, set_outbox_def]
QED

Theorem l1_close_other:
  l1_close f (w, b) = SOME ((w', b'), evs) ⇒
  (f ≠ g ⇒ outbox_of b' g = outbox_of b g) ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧
  (∀x. MEM x b'.closing ⇒ MEM x b.closing)
Proof
  rw[l1_close_def, AllCaseEqs()] >> simp[forget_outbox_of] >>
  fs[forget_def, set_outbox_def, MEM_FILTER]
QED

Theorem l1do_write_other:
  l1do lfd (w, b) (Write h' bs) = SOME (r, (w', b'), evs) ⇒
  ((∀x. ALOOKUP b.tbl h' = SOME x ⇒ x ≠ g) ⇒ outbox_of b' g = outbox_of b g) ∧
  b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧ b'.closing = b.closing
Proof
  simp[l1do_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[outbox_of_set_outbox, outbox_of_after_send_other] >>
  simp[set_outbox_def, after_send_def] >> every_case_tac >> simp[set_outbox_def]
QED

Theorem edo_hgone:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ hgone lfd h es ⇒ hgone lfd h es'
Proof
  Cases_on ‘a’ >> simp[edo_def] >> strip_tac
  >- (gvs[pdo_def, AllCaseEqs(), hgone_def] >> TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC) >>
      mp_tac (Q.INST [‘lfd’ |-> ‘c’, ‘nxt’ |-> ‘es.p.b.nxt’, ‘h’ |-> ‘l1hdl c j’] hdl_new) >>
      simp[l1hdl_hdl] >> strip_tac >> qexists_tac ‘j’ >> simp[])
  >- (Cases_on ‘ALOOKUP es.ctbl c’ >> gvs[]
      >- (Cases_on ‘pdo lfd (w, es.p) (Read c n)’ >> gvs[] >> PairCases_on ‘x’ >> gvs[] >>
          qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> rw[AllCaseEqs()] >>
          TRY (PairCases_on ‘z’) >> gvs[] >> TRY (drule l1_close_other >> strip_tac) >>
          gvs[hgone_def, ALOOKUP_ADELKEY] >> rw[] >> gvs[] >> qexists_tac ‘j’ >> simp[])
      >> gvs[AllCaseEqs()] >> TRY (PairCases_on ‘z’) >> gvs[] >>
      TRY (drule l1_close_other >> strip_tac) >>
      gvs[hgone_def, ec_del_def, ALOOKUP_ADELKEY] >> rw[] >> gvs[] >> qexists_tac ‘j’ >> simp[])
  >- (gvs[AllCaseEqs()] >> PairCases_on ‘z’ >> gvs[pdo_def] >> pairarg_tac >> gvs[] >>
      drule l1do_write_other >> strip_tac >> gvs[hgone_def] >> qexists_tac ‘j’ >> simp[])
  >- (gvs[AllCaseEqs(), hgone_def] >> TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC) >>
      mp_tac (Q.INST [‘nxt’ |-> ‘es.p.b.nxt’, ‘h’ |-> ‘l1hdl lfd j’] hdl_new) >>
      simp[l1hdl_hdl] >> strip_tac >> qexists_tac ‘j’ >> simp[])
  >> gvs[]
QED

Theorem okeep_hdl_new:
  okeep lfd h g es ∧ hdln (w2n lfd) es.p.b.nxt < 18446744073709551616 ⇒
  hdl lfd es.p.b.nxt ≠ h
Proof
  rw[okeep_def] >> irule hdl_new >> simp[] >> metis_tac[]
QED

Theorem okeep_accept:
  okeep lfd h g es ∧ hdl lfd es.p.b.nxt ≠ h ∧ f ≠ g ∧ (∀x. MEM x q ⇒ MEM x es.p.acq) ⇒
  okeep lfd h g (es with p := es.p with
                   <| b := es.p.b with <| tbl := (hdl lfd es.p.b.nxt, f) :: es.p.b.tbl;
                                          nxt := es.p.b.nxt + 1 |>; acq := q |>)
Proof
  rw[okeep_def] >> TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC)
  >- (qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[])
  >> strip_tac >> qpat_x_assum ‘∀x. MEM x q ⇒ _’ drule >>
  qpat_x_assum ‘¬MEM g es.p.acq’ mp_tac >> simp[]
QED

Theorem edo_read_okeep:
  edo lfd pol (w, es) (ERead k n) = SOME (r, (w', es'), evs) ∧ okeep lfd h g es ∧ fopen g w ⇒
  okeep lfd h g es' ∧ fopen g w' ∧ outbox_of es'.p.b g = outbox_of es.p.b g ∨
  hgone lfd h es'
Proof
  simp[edo_def] >> strip_tac >>
  Cases_on ‘ALOOKUP es.ctbl k’ >> gvs[]
  >- (Cases_on ‘pdo lfd (w, es.p) (Read k n)’ >> gvs[] >> PairCases_on ‘x’ >> gvs[] >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      Cases_on ‘ALOOKUP es.p.b.tbl k’ >> simp[]
      >- (strip_tac >> gvs[] >> disj1_tac >>
          ‘es with p := es.p = es’ by simp[fetch "honestL1EPModel" "l1e_component_equality"] >> simp[]) >>
      rename1 ‘ALOOKUP _ k = SOME g'’ >>
      ‘g' = g ⇔ k = h’
        by (qpat_x_assum ‘okeep _ _ _ _’ mp_tac >> simp[okeep_def] >> metis_tac[SOME_11]) >>
      Cases_on ‘inb_of es.p g' ≠ []’ >> simp[]
      >- (strip_tac >> gvs[] >> disj1_tac >>
          qpat_x_assum ‘okeep _ _ _ _’ mp_tac >> simp[okeep_def]) >>
      Cases_on ‘MEM g' es.p.eof’ >> simp[]
      >- (Cases_on ‘k = h’
          >- (gvs[] >> rw[] >> TRY (PairCases_on ‘z’) >> gvs[] >>
              TRY (drule l1_close_other >> strip_tac) >> disj2_tac >>
              qpat_x_assum ‘okeep _ _ _ _’ mp_tac >>
              simp[okeep_def, hgone_def, ALOOKUP_ADELKEY] >> metis_tac[]) >>
          ‘g' ≠ g’ by simp[] >>
          IF_CASES_TAC >> simp[]
          >- (Cases_on ‘l1_close g' (w, es.p.b with tbl := ADELKEY k es.p.b.tbl)’ >> simp[] >>
              PairCases_on ‘x’ >> simp[] >> strip_tac >> gvs[] >> disj1_tac >>
              drule_all l1_close_fopen >> strip_tac >>
              drule l1_close_other >> disch_then (qspec_then ‘g’ strip_assume_tac) >> gvs[] >>
              irule okeep_adel >> simp[MEM_FILTER] >> metis_tac[])
          >> strip_tac >> gvs[] >> disj1_tac >> simp[outbox_of_def] >>
          irule okeep_adel >> simp[] >> metis_tac[]) >>
      strip_tac >> gvs[] >> disj1_tac >>
      ‘es with p := es.p = es’ by simp[fetch "honestL1EPModel" "l1e_component_equality"] >> simp[])
  >> rename1 ‘ALOOKUP es.ctbl k = SOME g'’ >>
  ‘k ≠ h’ by (strip_tac >> gvs[okeep_def]) >>
  ‘g' ≠ g’
    by (drule ALOOKUP_MEM >> rpt strip_tac >> gvs[okeep_def, MEM_MAP] >> metis_tac[SND]) >>
  disj1_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> simp[] >>
  Cases_on ‘l1_close g' (w, es.p.b)’ >> gvs[] >> PairCases_on ‘x’ >> gvs[] >>
  drule_all l1_close_fopen >> strip_tac >>
  drule l1_close_other >> disch_then (qspec_then ‘g’ strip_assume_tac) >> gvs[] >>
  ‘(ec_del k g' (es with p := es.p with b := x1)).p.b = x1’ by simp[ec_del_def] >>
  simp[] >> irule okeep_ec_del >> simp[] >> irule okeep_b >> simp[MEM_FILTER]
QED

Theorem edo_okeep:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ okeep lfd h g es ∧ fopen g w ∧
  (∀bs. a ≠ EWrite h bs) ⇒
  okeep lfd h g es' ∧ fopen g w' ∧ outbox_of es'.p.b g = outbox_of es.p.b g ∨
  hgone lfd h es'
Proof
  Cases_on ‘a’ >> strip_tac
  >- (disj1_tac >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >>
      simp[edo_def, pdo_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      simp[outbox_of_def] >> irule okeep_accept >> simp[] >>
      drule_all okeep_hdl_new >> simp[] >> strip_tac >>
      qpat_x_assum ‘okeep _ _ _ _’ mp_tac >> simp[okeep_def] >> metis_tac[MEM])
  >- (drule_all edo_read_okeep >> simp[])
  >- (disj1_tac >> rename1 ‘EWrite k bs’ >>
      ‘k ≠ h’ by (strip_tac >> gvs[]) >>
      qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def, AllCaseEqs()] >> strip_tac >>
      gvs[] >> PairCases_on ‘z’ >> gvs[pdo_def] >> pairarg_tac >> gvs[] >>
      rename1 ‘l1do _ _ _ = SOME (r0, (w', b'), evs)’ >>
      ‘l0_rely w’ by fs[fopen_def] >>
      drule_all l1do_write_l0 >> strip_tac >>
      drule l1do_write_other >> strip_tac >>
      ‘∀x. ALOOKUP es.p.b.tbl k = SOME x ⇒ x ≠ g’
        by (qpat_x_assum ‘okeep _ _ _ _’ mp_tac >> simp[okeep_def] >> metis_tac[]) >>
      qpat_x_assum ‘∀g. _ ∧ _’ (qspec_then ‘g’ strip_assume_tac) >>
      qpat_x_assum ‘(∀x. _) ⇒ _’
        (fn th => qpat_x_assum ‘∀x. ALOOKUP _ k = SOME x ⇒ _’ (strip_assume_tac o MATCH_MP th)) >>
      ‘fopen g w'’ by gvs[fopen_def, fds_lt_def] >> simp[] >>
      irule okeep_b >> simp[])
  >- (disj1_tac >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      ‘l0_rely w ∧ fds_lt w ∧ MEM g (l0_used w)’ by fs[fopen_def] >>
      drule_all sys_connect_l0 >> strip_tac >>
      ‘fopen g w'’ by gvs[fopen_def] >> simp[] >>
      ‘n2w (res_val out) ≠ g’ by (strip_tac >> gvs[]) >>
      ‘hdl lfd es.p.b.nxt ≠ h’ by (irule okeep_hdl_new >> simp[] >> metis_tac[]) >>
      simp[outbox_of_def] >> qpat_x_assum ‘okeep _ _ _ es’ mp_tac >> simp[okeep_def] >>
      rw[] >> TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC) >> metis_tac[])
  >> disj1_tac >> gvs[edo_def]
QED

Theorem eacts_okeep:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ (∀bs. ¬MEM (EWrite h bs) acts) ⇒
    (okeep lfd h g es ∧ fopen g w ⇒
     okeep lfd h g es' ∧ fopen g w' ∧ outbox_of es'.p.b g = outbox_of es.p.b g ∨
     hgone lfd h es') ∧
    (hgone lfd h es ⇒ hgone lfd h es')
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘edo _ _ _ _ = SOME (r, (w1, es1), evs1)’ >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (strip_tac >> drule edo_okeep >> disch_then (qspecl_then [‘h’, ‘g’] mp_tac) >>
      simp[] >> strip_tac >> metis_tac[])
  >> strip_tac >> drule_all edo_hgone >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The tail
   ------------------------------------------------------------------------ *)

(* The stall step on an fd it holds whose outbox survived and did not
   shrink: every count of g goes up by one, and g has a count ≥ 1 *)
Theorem stall_step_up:
  outbox_of (stall_step hfs ob log ps).b g ≠ [] ∧
  ¬(LENGTH (outbox_of ps.b g) < LENGTH (ob g)) ∧
  MEM g (MAP SND ps.b.tbl) ∧ MEM g hfs ⇒
  (∃n. 1 ≤ n ∧ MEM (g, n) (stall_step hfs ob log ps).stalls) ∧
  ∀m. MEM (g, m) ps.stalls ⇒ MEM (g, m + 1) (stall_step hfs ob log ps).stalls
Proof
  simp[stall_step_def, FOLDL_drop_out] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘MAP fn A ++ MAP fn B’ >>
  qabbrev_tac ‘hs1 = MAP fn A ++ MAP fn B’ >>
  ‘outbox_of ps.b g ≠ [] ∧ ¬MEM g (MAP FST (FILTER (λ(f,n). pf_sendwait ≤ n) hs1))’
    by (qpat_x_assum ‘(if _ then _ else _) ≠ _’ mp_tac >> rw[]) >>
  ‘∀n. fn (g, n) = if MEM (FReset g) log then (g, pf_sendwait) else (g, n + 1)’
    by simp[Abbr ‘fn’] >>
  ‘∀n. MEM (g, n) A ∨ MEM (g, n) B ⇒
       ¬MEM (FReset g) log ∧ MEM (g, n + 1) (FILTER (λ(f,n). n < pf_sendwait) hs1)’
    by (gen_tac >> strip_tac >>
        ‘MEM (fn (g, n)) hs1’
          by (simp[Abbr ‘hs1’, MEM_MAP] >> metis_tac[]) >>
        qpat_x_assum ‘¬MEM g (MAP FST _)’ mp_tac >>
        pop_assum mp_tac >>
        qpat_x_assum ‘∀n. fn _ = _’ (fn th => rewrite_tac [th]) >>
        Cases_on ‘MEM (FReset g) log’ >>
        simp[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[LESS_EQ_REFL, NOT_LESS]) >>
  qpat_x_assum ‘∀n. MEM (g, n) A ∨ _ ⇒ _’ (strip_assume_tac o SIMP_RULE bool_ss [DISJ_IMP_THM, FORALL_AND_THM]) >>
  conj_tac
  >- (Cases_on ‘MEM g (MAP FST ps.stalls)’
      >- (pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_MAP, EXISTS_PROD]) >>
          rename1 ‘MEM (g, n0) ps.stalls’ >>
          ‘MEM (g, n0) A’ by (simp[Abbr ‘A’, MEM_FILTER] >> asm_rewrite_tac[]) >>
          qpat_x_assum ‘∀n. MEM (g, n) A ⇒ _’ (drule_then strip_assume_tac) >>
          qexists_tac ‘n0 + 1’ >> simp[])
      >> ‘MEM (g, 0) B’
           by (simp[Abbr ‘B’, MEM_MAP, MEM_FILTER, MEM_nub] >> conj_tac
               >- (qpat_x_assum ‘MEM g (MAP SND _)’ mp_tac >> simp[MEM_MAP] >> metis_tac[])
               >> qpat_x_assum ‘¬MEM g (MAP FST _)’ mp_tac >> simp[MEM_MAP]) >>
         qpat_x_assum ‘∀n. MEM (g, n) B ⇒ _’ (drule_then strip_assume_tac) >>
         qexists_tac ‘1’ >> fs[])
  >> rpt strip_tac >>
  ‘MEM (g, m) A’ by (simp[Abbr ‘A’, MEM_FILTER] >> asm_rewrite_tac[]) >>
  qpat_x_assum ‘∀n. MEM (g, n) A ⇒ _’ (drule_then strip_assume_tac)
QED

Theorem okeep_promote:
  okeep lfd h g es ⇒ okeep lfd h g (promote es with settling := sl)
Proof
  simp[okeep_def, promote_fields] >> strip_tac >>
  ‘ALOOKUP (FILTER (λ(h, f). cstat_of es f = CUp) es.ctbl) h = NONE’
    by simp[ALOOKUP_FILTER_NONE] >>
  simp[ALOOKUP_APPEND, ALOOKUP_FILTER_NONE, MEM_MAP, MEM_FILTER] >> rpt conj_tac
  >- (rpt strip_tac >> every_case_tac >> gvs[] >> drule ALOOKUP_MEM >>
      simp[MEM_FILTER] >> strip_tac >> gvs[MEM_MAP] >> metis_tac[SND])
  >- (rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[])
  >> metis_tac[]
QED

(* The end of the tail: promotion, with g not waiting to be accepted at
   the end (L1's ownership) *)
Theorem okeep_tail:
  okeep lfd h g es ∧ es5.p.b.tbl = es.p.b.tbl ∧ es5.p.b.nxt = es.p.b.nxt ∧
  (∀x. MEM x es5.p.b.closing ⇒ MEM x es.p.b.closing) ∧
  es5.ctbl = es.ctbl ∧ eown lfd (promote es5 with settling := sl) ⇒
  okeep lfd h g (promote es5 with settling := sl)
Proof
  strip_tac >>
  ‘okeep lfd h g (es5 with p := es5.p with acq := [])’
    by (qpat_x_assum ‘okeep _ _ _ es’ mp_tac >> simp[okeep_def] >> metis_tac[]) >>
  drule okeep_promote >> disch_then (qspec_then ‘sl’ mp_tac) >>
  simp[okeep_def, promote_fields, cstat_of_def] >> strip_tac >>
  qpat_x_assum ‘eown _ _’ mp_tac >> simp[eown_def, promote_fields, ALL_DISTINCT_APPEND] >>
  strip_tac >> strip_tac >>
  ‘MEM g (MAP SND es.p.b.tbl)’
    by (qpat_x_assum ‘okeep _ _ _ es’ mp_tac >> simp[okeep_def, MEM_MAP, EXISTS_PROD] >>
        metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum ‘∀e. _ ⇒ ¬MEM e es5.p.acq’ (qspec_then ‘g’ mp_tac) >> simp[]
QED

Theorem hgone_tail:
  hgone lfd h es ∧ es5.p.b.tbl = es.p.b.tbl ∧ es5.p.b.nxt = es.p.b.nxt ∧ es5.ctbl = es.ctbl ⇒
  hgone lfd h (promote es5 with settling := sl)
Proof
  simp[hgone_def, promote_fields, ALOOKUP_APPEND, ALOOKUP_FILTER_NONE] >> strip_tac >>
  simp[ALOOKUP_FILTER_NONE]
QED

Theorem promote_outbox:
  (promote es).p.b.outbox = es.p.b.outbox ∧ (promote es).p.stalls = es.p.stalls
Proof
  simp[promote_def]
QED

Theorem etail_out:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ eown lfd es' ⇒
  (okeep lfd h g es ⇒
   okeep lfd h g es' ∧
   LENGTH (outbox_of es'.p.b g) ≤ LENGTH (outbox_of es.p.b g) ∧
   (outbox_of es'.p.b g ≠ [] ∧ LENGTH (outbox_of es'.p.b g) = LENGTH (outbox_of es.p.b g) ⇒
    (∃n. 1 ≤ n ∧ MEM (g, n) es'.p.stalls) ∧
    ∀m. MEM (g, m) es.p.stalls ⇒ MEM (g, m + 1) es'.p.stalls)) ∧
  (hgone lfd h es ⇒ hgone lfd h es')
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> rpt VAR_EQ_TAC >>
  drule l1_flush_b >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule honestL1PFConnRunTheory.pf_fetch_b >> strip_tac >> drule pf_fetch_stalls >> strip_tac >>
  qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule l1_reap_b >> strip_tac >>
  qpat_x_assum ‘settle_fds _ _ = _’ assume_tac >> drule settle_fds_p >> strip_tac >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3'’ >>
  qmatch_goalsub_abbrev_tac ‘promote es5 with settling := sl’ >>
  ‘ps3'.b = b2 ∧ ps3'.stalls = es.p.stalls’
    by (qpat_x_assum ‘ps3'.b = _’ mp_tac >> qpat_x_assum ‘ps3'.stalls = _’ mp_tac >> simp[]) >>
  ‘es5.p.b = b4 ∧ es5.p.stalls = ps3.stalls ∧ es5.ctbl = es.ctbl’
    by (qpat_x_assum ‘es5.p = _’ (REWRITE_TAC o single) >>
        qpat_x_assum ‘es5.ctbl = _’ (REWRITE_TAC o single) >> simp[]) >>
  ‘ps3.b.tbl = b2.tbl ∧ ps3.b.nxt = b2.nxt ∧ ps3.b.closing = b2.closing ∧
   LENGTH (outbox_of ps3.b g) ≤ LENGTH (outbox_of b2 g) ∧
   (outbox_of ps3.b g ≠ [] ⇒ outbox_of ps3.b g = outbox_of b2 g)’
    by (qpat_x_assum ‘ps3'.b = b2’ (fn th => simp[Abbr ‘ps3’, stall_step_def, FOLDL_drop_out, th]) >>
        rw[]) >>
  ‘b4.tbl = es.p.b.tbl ∧ b4.nxt = es.p.b.nxt ∧ ∀x. MEM x b4.closing ⇒ MEM x es.p.b.closing’
    by (qpat_x_assum ‘∀x. MEM x b4.closing ⇒ _’ mp_tac >>
        qpat_x_assum ‘b4.tbl = _’ mp_tac >> qpat_x_assum ‘b4.nxt = _’ mp_tac >>
        simp[]) >>
  ‘outbox_of (promote es5 with settling := sl).p.b g = outbox_of b4 g ∧
   (promote es5 with settling := sl).p.stalls = ps3.stalls’
    by simp[outbox_of_def, promote_outbox] >>
  pop_assum (fn th => REWRITE_TAC [th]) >> pop_assum (fn th => REWRITE_TAC [th]) >>
  conj_tac
  >- (strip_tac >>
      conj_tac >- (irule okeep_tail >> qpat_x_assum ‘okeep _ _ _ es’ (irule_at Any) >> simp[]) >>
      ‘outbox_of b4 g = outbox_of ps3.b g’
        by (qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule l1_reap_other >>
            disch_then (qspec_then ‘g’ mp_tac) >> impl_tac
            >- (qpat_x_assum ‘okeep _ _ _ es’ mp_tac >> simp[okeep_def]) >>
            simp[]) >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      ‘LENGTH (outbox_of b2 g) ≤ LENGTH (outbox_of es.p.b g)’
        by (qpat_x_assum ‘l1_flush _ _ = _’ assume_tac >> drule l1_flush_le >> simp[]) >>
      conj_tac >- simp[] >>
      strip_tac >>
      ‘outbox_of ps3.b g = outbox_of b2 g’ by simp[] >>
      ‘MEM g (MAP SND b2.tbl)’
        by (qpat_x_assum ‘okeep _ _ _ es’ mp_tac >> simp[okeep_def, MEM_MAP, EXISTS_PROD] >>
            metis_tac[ALOOKUP_MEM]) >>
      qspecl_then [‘pf_held ps3'’, ‘outbox_of es.p.b’, ‘log’, ‘ps3'’, ‘g’] mp_tac
        (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’, ‘g’] stall_step_up) >>
      qpat_x_assum ‘ps3'.stalls = es.p.stalls’ (fn th => REWRITE_TAC [th]) >>
      simp[Abbr ‘ps3’] >> disch_then irule >>
      qpat_x_assum ‘ps3'.b = b2’ (fn th => REWRITE_TAC [th, pf_held_def, MEM_APPEND]) >>
      simp[] >> qpat_x_assum ‘MEM g (MAP SND b2.tbl)’ mp_tac >>
      qpat_x_assum ‘b2.tbl = es.p.b.tbl’ (fn th => REWRITE_TAC [th]))
  >> strip_tac >> irule hgone_tail >> qpat_x_assum ‘hgone _ _ es’ (irule_at Any) >> simp[]
QED

(* ------------------------------------------------------------------------
   A round
   ------------------------------------------------------------------------ *)

Theorem eround_out:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
  okeep lfd h g es ∧ fopen g w ∧ eown lfd es' ∧ ALOOKUP es'.p.b.tbl h = SOME g ∧
  (∀bs. ¬MEM (EWrite h bs) acts) ⇒
  okeep lfd h g es' ∧
  LENGTH (outbox_of es'.p.b g) ≤ LENGTH (outbox_of es.p.b g) ∧
  (outbox_of es'.p.b g ≠ [] ∧ LENGTH (outbox_of es'.p.b g) = LENGTH (outbox_of es.p.b g) ⇒
   (∃n. 1 ≤ n ∧ MEM (g, n) es'.p.stalls) ∧
   ∀m. MEM (g, m) es.p.stalls ⇒ MEM (g, m + 1) es'.p.stalls)
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> rpt VAR_EQ_TAC >>
  PairCases_on ‘ws1’ >> rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, wa, ea)’ >>
  drule_all eacts_okeep >> disch_then (qspec_then ‘g’ strip_assume_tac) >>
  drule eacts_stalls >> strip_tac >>
  qpat_x_assum ‘etail _ _ _ _ = _’ assume_tac >>
  drule_all etail_out >> disch_then (qspecl_then [‘h’, ‘g’] strip_assume_tac) >>
  ‘okeep lfd h g ea ∧ outbox_of ea.p.b g = outbox_of es.p.b g ∨ hgone lfd h ea’
    by metis_tac[] >>
  gvs[] >> TRY (‘hgone lfd h es'’ by metis_tac[] >> gvs[hgone_def] >> NO_TAC) >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

(* The hypotheses of an unwritten stretch from round N: h names g *)
Definition eunwr_from_def:
  eunwr_from lfd ifds m w0 N h g ⇔
    erun_ok lfd ifds m w0 ∧ okeep lfd h g (erstate lfd ifds m w0 N) ∧
    ∀k. N ≤ k ⇒ ALOOKUP (erstate lfd ifds m w0 k).p.b.tbl h = SOME g ∧
                ∀bs. ¬MEM (EWrite h bs) (new_actions (log_of m) (erhist lfd ifds m w0 k))
End

Theorem okeep_fopen:
  okeep lfd h g es ∧ l0owne lfd w es ∧ l0_rely w ∧ fds_lt w ⇒ fopen g w
Proof
  rw[fopen_def] >> fs[l0owne_def, l0own_def, okeep_def] >>
  qpat_x_assum ‘∀f. f = lfd ∨ _ ⇒ MEM f (l0_used w)’ irule >>
  simp[MEM_MAP, EXISTS_PROD] >> metis_tac[ALOOKUP_MEM]
QED

Theorem eunwr_round:
  eunwr_from lfd ifds m w0 N h g ∧ N ≤ k ∧ okeep lfd h g (erstate lfd ifds m w0 k) ⇒
  okeep lfd h g (erstate lfd ifds m w0 (SUC k)) ∧
  LENGTH (outbox_of (erstate lfd ifds m w0 (SUC k)).p.b g) ≤
    LENGTH (outbox_of (erstate lfd ifds m w0 k).p.b g) ∧
  (outbox_of (erstate lfd ifds m w0 (SUC k)).p.b g ≠ [] ∧
   LENGTH (outbox_of (erstate lfd ifds m w0 (SUC k)).p.b g) =
     LENGTH (outbox_of (erstate lfd ifds m w0 k).p.b g) ⇒
   (∃n. 1 ≤ n ∧ MEM (g, n) (erstate lfd ifds m w0 (SUC k)).p.stalls) ∧
   ∀n. MEM (g, n) (erstate lfd ifds m w0 k).p.stalls ⇒
       MEM (g, n + 1) (erstate lfd ifds m w0 (SUC k)).p.stalls)
Proof
  strip_tac >>
  ‘erun_ok lfd ifds m w0 ∧
   ALOOKUP (erstate lfd ifds m w0 (SUC k)).p.b.tbl h = SOME g ∧
   ∀bs. ¬MEM (EWrite h bs) (new_actions (log_of m) (erhist lfd ifds m w0 k))’
    by (qpat_x_assum ‘eunwr_from _ _ _ _ _ _ _’ mp_tac >> simp[eunwr_from_def]) >>
  drule erun_round >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule erun_inv >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule erun_inv >> disch_then (qspec_then ‘SUC k’ strip_assume_tac) >>
  ‘fopen g (erworld lfd ifds m w0 k)’ by metis_tac[okeep_fopen] >>
  drule eround_out >> disch_then (qspecl_then [‘h’, ‘g’] mp_tac) >> simp[]
QED

Theorem eunwr_okeep:
  eunwr_from lfd ifds m w0 N h g ⇒ ∀d. okeep lfd h g (erstate lfd ifds m w0 (N + d))
Proof
  strip_tac >> Induct
  >- (qpat_x_assum ‘eunwr_from _ _ _ _ _ _ _’ mp_tac >> simp[eunwr_from_def]) >>
  drule eunwr_round >> disch_then (qspec_then ‘N + d’ mp_tac) >> simp[ADD_CLAUSES]
QED

(* Every stall count is below pf_sendwait (the stall step drops at it) *)
Theorem etail_stalls_lt:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ⇒
  ∀f n. MEM (f, n) es'.p.stalls ⇒ n < pf_sendwait
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> rpt VAR_EQ_TAC >>
  qpat_x_assum ‘settle_fds _ _ = _’ assume_tac >> drule settle_fds_p >> strip_tac >>
  simp[promote_def] >> qpat_x_assum ‘es5.p = _’ (REWRITE_TAC o single) >>
  simp[apply_early_def] >> rpt strip_tac >> drule stall_step_entry >> simp[]
QED

Theorem eround_stalls_lt:
  eround lfd pol hs ws acts = SOME (snap, (w', es'), log, evs) ⇒
  ∀f n. MEM (f, n) es'.p.stalls ⇒ n < pf_sendwait
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> rpt VAR_EQ_TAC >>
  PairCases_on ‘ws1’ >> drule etail_stalls_lt >> simp[]
QED

Theorem pf_sendwait_stall:
  MEM (g, n) (erstate lfd ifds m w0 k).p.stalls ∧ erun_ok lfd ifds m w0 ⇒ n < pf_sendwait
Proof
  Cases_on ‘k’
  >- (strip_tac >> drule erun_some >> disch_then (qspec_then ‘0’ mp_tac) >>
      simp[erounds_def] >> strip_tac >> gvs[einit_def, pinit_def])
  >> strip_tac >> drule erun_round >> disch_then (qspec_then ‘n'’ strip_assume_tac) >>
  drule eround_stalls_lt >> disch_then drule >> simp[]
QED

(* A non-increasing sequence of numbers is eventually constant *)
Theorem nonincr_stable:
  (∀d. f (SUC d) ≤ (f d : num)) ⇒ ∃D. ∀d. D ≤ d ⇒ f d = f D
Proof
  strip_tac >>
  ‘∀a d. f (a + d) ≤ f a’
    by (gen_tac >> Induct >> simp[] >>
        irule LESS_EQ_TRANS >> qexists_tac ‘f (a + d)’ >> simp[ADD_CLAUSES]) >>
  ‘∀v a. f a = v ⇒ ∃D. ∀d. D ≤ d ⇒ f d = f D’
    suffices_by (disch_then (qspecl_then [‘f 0’, ‘0’] mp_tac) >> simp[]) >>
  completeInduct_on ‘v’ >> rpt strip_tac >>
  Cases_on ‘∀d. a ≤ d ⇒ f d = f a’ >- metis_tac[] >>
  gvs[NOT_LESS_EQUAL] >>
  ‘f d ≤ f a’ by (qpat_x_assum ‘∀a d. _’ (qspecl_then [‘a’, ‘d − a’] mp_tac) >> simp[]) >>
  ‘f d < f a’ by simp[] >>
  first_x_assum (qspec_then ‘f d’ mp_tac) >> simp[] >> metis_tac[]
QED

(* MAIN: g's outbox is empty at some round from N on *)
Theorem eunwr_empties:
  eunwr_from lfd ifds m w0 N h g ⇒
  ∃k. N ≤ k ∧ outbox_of (erstate lfd ifds m w0 k).p.b g = []
Proof
  strip_tac >> CCONTR_TAC >>
  qabbrev_tac ‘ob = λk. outbox_of (erstate lfd ifds m w0 k).p.b g’ >>
  qabbrev_tac ‘st = λk. (erstate lfd ifds m w0 k).p.stalls’ >>
  ‘∀k. N ≤ k ⇒ ob k ≠ []’
    by (rpt strip_tac >> qpat_x_assum ‘¬∃k. _’ mp_tac >> simp[] >>
        qexists_tac ‘k’ >> fs[Abbr ‘ob’]) >>
  drule eunwr_okeep >> strip_tac >>
  ‘∀k. N ≤ k ⇒
       LENGTH (ob (SUC k)) ≤ LENGTH (ob k) ∧
       (LENGTH (ob (SUC k)) = LENGTH (ob k) ⇒
        (∃n. 1 ≤ n ∧ MEM (g, n) (st (SUC k))) ∧
        ∀n. MEM (g, n) (st k) ⇒ MEM (g, n + 1) (st (SUC k)))’
    by (rpt gen_tac >> strip_tac >>
        ‘okeep lfd h g (erstate lfd ifds m w0 k)’
          by (qpat_x_assum ‘∀d. okeep _ _ _ _’ (qspec_then ‘k − N’ mp_tac) >> simp[]) >>
        ‘ob (SUC k) ≠ []’ by simp[] >>
        drule eunwr_round >> disch_then (qspec_then ‘k’ mp_tac) >>
        fs[Abbr ‘ob’, Abbr ‘st’]) >>
  ‘∀d. LENGTH (ob (N + SUC d)) ≤ LENGTH (ob (N + d))’
    by (gen_tac >> ‘N + SUC d = SUC (N + d)’ by simp[] >> simp[]) >>
  pop_assum (strip_assume_tac o MATCH_MP
    (BETA_RULE (Q.INST [‘f’ |-> ‘λd. LENGTH (ob (N + d))’] nonincr_stable))) >>
  ‘∀k. N + D ≤ k ⇒ LENGTH (ob (SUC k)) = LENGTH (ob k)’
    by (rpt strip_tac >>
        qpat_assum ‘∀d. D ≤ d ⇒ _’ (qspec_then ‘SUC k − N’ mp_tac) >>
        qpat_assum ‘∀d. D ≤ d ⇒ _’ (qspec_then ‘k − N’ mp_tac) >>
        ‘N + (SUC k − N) = SUC k ∧ N + (k − N) = k ∧ D ≤ SUC k − N ∧ D ≤ k − N’
          by (qpat_x_assum ‘N + D ≤ k’ mp_tac >> simp[]) >>
        ntac 4 (pop_assum (fn th => REWRITE_TAC [th])) >>
        ntac 2 (disch_then SUBST1_TAC) >> REFL_TAC) >>
  ‘∀i. ∃n. SUC i ≤ n ∧ MEM (g, n) (st (SUC (N + D + i)))’
    by (Induct
        >- (qpat_x_assum ‘∀k. N ≤ k ⇒ LENGTH _ ≤ _ ∧ _’ (qspec_then ‘N + D’ mp_tac) >>
            simp[] >> metis_tac[])
        >> qpat_x_assum ‘∃n. _’ strip_assume_tac >>
           qpat_x_assum ‘∀k. N ≤ k ⇒ LENGTH _ ≤ _ ∧ _’ (qspec_then ‘SUC (N + D + i)’ mp_tac) >>
           impl_tac >- simp[] >> strip_tac >>
           ‘LENGTH (ob (SUC (SUC (N + D + i)))) = LENGTH (ob (SUC (N + D + i)))’
             by (qpat_x_assum ‘∀k. N + D ≤ k ⇒ _’ irule >> simp[]) >>
           qpat_x_assum ‘_ = _ ⇒ _’ (fn th => strip_assume_tac (MATCH_MP th (ASSUME (lhand (concl th))))) >>
           ‘SUC (N + D + SUC i) = SUC (SUC (N + D + i))’ by simp[] >>
           pop_assum SUBST1_TAC >> qexists_tac ‘n + 1’ >> simp[]) >>
  first_x_assum (qspec_then ‘pf_sendwait’ strip_assume_tac) >>
  ‘erun_ok lfd ifds m w0’ by fs[eunwr_from_def] >>
  ‘n < pf_sendwait’ by (irule pf_sendwait_stall >> fs[Abbr ‘st’] >> metis_tac[]) >>
  simp[]
QED
