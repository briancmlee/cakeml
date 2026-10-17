(*
  When the prefetching L1 with connects asks for input on an fd (a lemma
  layer for the proxy's asks claim, proxyL0Stmts.proxy_asks_claim,
  revision 9): honestL1PFAsks on the EP model, which is what the proxy
  runs on.  The world invariant of the PF lemmas (winv) does not hold here
  (its noconn fails once a connect is pending), so these use only L0's
  rely, the fd bound and that f is open, and keep their own view of f's
  handle (ekeep).
*)
Theory honestL1EPAsks
Ancestors
  honestL1EPRefine honestL1EPModel honestL1PFAsks honestL1PFRound honestL1PFRefine honestL1PFInv
  honestL1PFModel honestL1Model honestL1Steps honestL1Inv
  honestL0WorldProps honestL0Rely honestL0World honestL0 asyncCore asyncLevel1 ffi
Libs
  preamble

(* L1's view of f's handle h: h names f and nothing else does; f is not at
   EOF, not closing, not waiting to be accepted, not a connect's fd; h is
   not a connect handle and was issued within the handle bound *)
Definition ekeep_def:
  ekeep lfd h f es ⇔
    ALOOKUP es.p.b.tbl h = SOME f ∧ (∀h'. ALOOKUP es.p.b.tbl h' = SOME f ⇒ h' = h) ∧
    ¬MEM f es.p.eof ∧ ¬MEM f es.p.b.closing ∧ ¬MEM f es.p.acq ∧ f ≠ lfd ∧
    ALOOKUP es.ctbl h = NONE ∧ ¬MEM f (MAP SND es.ctbl) ∧
    ∃j. h = l1hdl lfd j ∧ j < es.p.b.nxt ∧ j + 1 < dimword (:64)
End

(* The world facts the lemmas carry *)
Definition fopen_def:
  fopen f w ⇔ l0_rely w ∧ fds_lt w ∧ MEM f (l0_used w)
End

Theorem ekeep_new_hdl:
  ekeep lfd h f es ∧ l1hdln (w2n lfd) es.p.b.nxt < dimword (:64) ⇒
  l1hdl lfd es.p.b.nxt ≠ h
Proof
  rw[ekeep_def] >> strip_tac >>
  ‘l1hdln (w2n lfd) j < dimword (:64)’ by simp[l1hdln_lt] >>
  qspecl_then [‘lfd’, ‘es.p.b.nxt’, ‘j’] mp_tac (Q.GENL [‘lfd’, ‘i’, ‘j’] l1hdl_11) >>
  simp[]
QED

Theorem ekeep_new_hdl':
  ekeep lfd h f es ∧ hdln (w2n lfd) es.p.b.nxt < 18446744073709551616 ⇒
  hdl lfd es.p.b.nxt ≠ h
Proof
  strip_tac >> drule ekeep_new_hdl >> simp[l1hdl_hdl]
QED

(* A change of L1's buffers that keeps the table and the handle count and
   only drops closing fds *)
Theorem ekeep_b:
  ekeep lfd h f es ∧ b'.tbl = es.p.b.tbl ∧ b'.nxt = es.p.b.nxt ∧
  (∀x. MEM x b'.closing ⇒ MEM x es.p.b.closing) ⇒
  ekeep lfd h f (es with p := es.p with b := b')
Proof
  rw[ekeep_def] >> metis_tac[]
QED

(* An EOF auto-close of another handle g of fd g' *)
Theorem ekeep_adel:
  ekeep lfd h f es ∧ g ≠ h ∧ g' ≠ f ∧ b'.tbl = ADELKEY g es.p.b.tbl ∧ b'.nxt = es.p.b.nxt ∧
  (∀x. MEM x b'.closing ⇒ MEM x es.p.b.closing ∨ x = g') ∧ (∀x. MEM x eof' ⇒ MEM x es.p.eof) ⇒
  ekeep lfd h f (es with p := es.p with <| b := b'; eof := eof' |>)
Proof
  rw[ekeep_def, ALOOKUP_ADELKEY] >> metis_tac[]
QED

Theorem ekeep_ec_del:
  ekeep lfd h f es ∧ g ≠ h ⇒ ekeep lfd h f (ec_del g g' es)
Proof
  rw[ekeep_def, ec_del_def, ALOOKUP_ADELKEY] >> fs[MEM_MAP, MEM_FILTER, ADELKEY_def] >> metis_tac[]
QED

Theorem l1_close_fopen:
  l1_close g (w, b) = SOME ((w', b'), evs) ∧ fopen f w ∧ g ≠ f ⇒
  fopen f w' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧ b'.closing = FILTER ($≠ g) b.closing
Proof
  rw[fopen_def] >> drule_all l1_close_l0 >> strip_tac >> simp[] >>
  gvs[fds_lt_def] >> metis_tac[]
QED

Theorem edo_accept_ekeep:
  edo lfd pol (w, es) (EAccept l) = SOME (r, (w', es'), evs) ∧ ekeep lfd h f es ⇒
  ekeep lfd h f es' ∧ w' = w ∧ inb_of es'.p f = inb_of es.p f
Proof
  simp[edo_def, pdo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all ekeep_new_hdl' >> strip_tac >>
  gvs[ekeep_def, inb_of_def] >> rw[] >> gvs[] >>
  qexists_tac ‘j’ >> simp[]
QED

Theorem edo_connect_ekeep:
  edo lfd pol (w, es) (EConnect a) = SOME (r, (w', es'), evs) ∧ ekeep lfd h f es ∧ fopen f w ⇒
  ekeep lfd h f es' ∧ fopen f w' ∧ inb_of es'.p f = inb_of es.p f
Proof
  simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  ‘l0_rely w ∧ fds_lt w ∧ MEM f (l0_used w)’ by fs[fopen_def] >>
  drule_all sys_connect_l0 >> strip_tac >> gvs[fopen_def] >>
  TRY (simp[inb_of_def] >> NO_TAC) >>
  drule_all ekeep_new_hdl' >> strip_tac >>
  ‘n2w (res_val out) ≠ f’ by (strip_tac >> gvs[]) >>
  gvs[ekeep_def, inb_of_def] >> qexists_tac ‘j’ >> simp[]
QED

Theorem edo_level_ekeep:
  edo lfd pol (w, es) (ELevel g) = SOME (r, (w', es'), evs) ⇒ w' = w ∧ es' = es
Proof
  simp[edo_def]
QED

Theorem edo_write_ekeep:
  edo lfd pol (w, es) (EWrite g bs) = SOME (r, (w', es'), evs) ∧ ekeep lfd h f es ∧ fopen f w ⇒
  ekeep lfd h f es' ∧ fopen f w' ∧ inb_of es'.p f = inb_of es.p f
Proof
  simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘z’ >> gvs[pdo_def] >> pairarg_tac >> gvs[] >>
  rename1 ‘l1do _ _ _ = SOME (r0, (w', b'), evs)’ >>
  ‘l0_rely w’ by fs[fopen_def] >>
  drule_all l1do_write_l0 >> strip_tac >>
  ‘b'.tbl = es.p.b.tbl ∧ b'.nxt = es.p.b.nxt ∧ b'.closing = es.p.b.closing’
    by (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >>
        simp[l1do_def, AllCaseEqs()] >> rw[] >>
        simp[set_outbox_def, after_send_def] >> every_case_tac >> simp[set_outbox_def]) >>
  conj_tac
  >- (‘es with p := es.p with b := b' = es with p := es.p with b := b'’ by simp[] >>
      drule_then (qspec_then ‘b'’ mp_tac) ekeep_b >> simp[])
  >> gvs[fopen_def, fds_lt_def, inb_of_def]
QED

Theorem edo_read_ekeep:
  edo lfd pol (w, es) (ERead g n) = SOME (r, (w', es'), evs) ∧ ekeep lfd h f es ∧ fopen f w ⇒
  ekeep lfd h f es' ∧ fopen f w' ∧
  LENGTH (inb_of es'.p f) ≤ LENGTH (inb_of es.p f) ∧
  (g = h ∧ inb_of es.p f ≠ [] ⇒ LENGTH (inb_of es'.p f) < LENGTH (inb_of es.p f))
Proof
  simp[edo_def] >> strip_tac >>
  Cases_on ‘ALOOKUP es.ctbl g’ >> gvs[]
  >- (Cases_on ‘pdo lfd (w, es.p) (Read g n)’ >> gvs[] >> PairCases_on ‘x’ >> gvs[] >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      Cases_on ‘ALOOKUP es.p.b.tbl g’ >> simp[]
      >- (strip_tac >> gvs[] >> rpt strip_tac >> gvs[ekeep_def]) >>
      rename1 ‘ALOOKUP _ g = SOME g'’ >>
      ‘g' = f ⇔ g = h’
        by (qpat_x_assum ‘ekeep _ _ _ _’ mp_tac >> simp[ekeep_def] >> metis_tac[SOME_11]) >>
      Cases_on ‘inb_of es.p g' ≠ []’ >> simp[]
      >- (strip_tac >> gvs[] >>
          conj_tac >- (qpat_x_assum ‘ekeep _ _ _ _’ mp_tac >> simp[ekeep_def]) >>
          Cases_on ‘g = h’ >> gvs[] >> Cases_on ‘inb_of es.p f’ >> gvs[]) >>
      Cases_on ‘MEM g' es.p.eof’ >> simp[]
      >- (‘g' ≠ f’ by (strip_tac >> gvs[ekeep_def]) >>
          ‘g ≠ h’ by (strip_tac >> gvs[]) >>
          IF_CASES_TAC >> simp[]
          >- (Cases_on ‘l1_close g' (w, es.p.b with tbl := ADELKEY g es.p.b.tbl)’ >> simp[] >>
              PairCases_on ‘x’ >> simp[] >> strip_tac >> gvs[] >>
              drule_all l1_close_fopen >> strip_tac >> simp[inb_of_def] >>
              irule ekeep_adel >> simp[MEM_FILTER] >>
              metis_tac[])
          >> strip_tac >> gvs[] >> simp[inb_of_def] >>
          irule ekeep_adel >> simp[MEM_FILTER] >> metis_tac[]) >>
      strip_tac >> gvs[] >> strip_tac >> gvs[])
  >> rename1 ‘ALOOKUP es.ctbl g = SOME g'’ >>
  ‘g ≠ h’ by (strip_tac >> gvs[ekeep_def]) >>
  ‘g' ≠ f’
    by (drule ALOOKUP_MEM >> rpt strip_tac >> gvs[ekeep_def, MEM_MAP] >> metis_tac[SND]) >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> simp[] >>
  Cases_on ‘l1_close g' (w, es.p.b)’ >> gvs[] >> PairCases_on ‘x’ >> gvs[] >>
  drule_all l1_close_fopen >> strip_tac >> simp[] >>
  rpt conj_tac >>
  FIRST [simp[ec_del_def, inb_of_def] >> NO_TAC,
         irule ekeep_ec_del >> simp[] >> irule ekeep_b >> simp[MEM_FILTER]]
QED

(* One action *)
Theorem edo_ekeep:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ ekeep lfd h f es ∧ fopen f w ⇒
  ekeep lfd h f es' ∧ fopen f w' ∧
  LENGTH (inb_of es'.p f) ≤ LENGTH (inb_of es.p f) ∧
  (∀k. a = ERead h k ∧ inb_of es.p f ≠ [] ⇒ LENGTH (inb_of es'.p f) < LENGTH (inb_of es.p f))
Proof
  Cases_on ‘a’ >> strip_tac
  >- (drule_all edo_accept_ekeep >> simp[] >> strip_tac >> gvs[])
  >- (drule_all edo_read_ekeep >> simp[])
  >- (drule_all edo_write_ekeep >> simp[])
  >- (drule_all edo_connect_ekeep >> simp[])
  >> drule edo_level_ekeep >> simp[]
QED

(* A round's actions *)
Theorem eacts_ekeep:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ ekeep lfd h f es ∧ fopen f w ⇒
    ekeep lfd h f es' ∧ fopen f w' ∧
    LENGTH (inb_of es'.p f) ≤ LENGTH (inb_of es.p f) ∧
    ((∃k. MEM (ERead h k) acts) ∧ inb_of es.p f ≠ [] ⇒
     LENGTH (inb_of es'.p f) < LENGTH (inb_of es.p f))
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘edo _ _ _ _ = SOME (r, (w1, es1), evs1)’ >>
  drule_all edo_ekeep >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rpt conj_tac >- simp[] >- simp[] >- decide_tac >>
  simp[PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac
  >- (gvs[] >> first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >> decide_tac)
  >> Cases_on ‘inb_of es1.p f = []’
  >- (gvs[] >> Cases_on ‘inb_of es.p f’ >> gvs[])
  >> ‘LENGTH (inb_of es'.p f) < LENGTH (inb_of es1.p f)’ by metis_tac[] >>
  decide_tac
QED

(* The tail's steps on L1's buffers, whatever the world *)
Theorem l1_flush_b:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒
    st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧ st'.closing = st.closing
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> strip_tac >> gvs[after_send_def] >>
  every_case_tac >> gvs[set_outbox_def]
QED

Theorem l1_reap_b:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒
    st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧ ∀x. MEM x st'.closing ⇒ MEM x st.closing
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >>
  simp[AllCaseEqs(), l1_close_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> gvs[forget_def, set_outbox_def, MEM_FILTER]
QED

Theorem settle_fds_p:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ es'.p = es.p ∧ es'.ctbl = es.ctbl
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> every_case_tac >> gvs[]
QED

Theorem foldl_drop_out:
  ∀l b. (FOLDL drop_out b l).tbl = b.tbl ∧ (FOLDL drop_out b l).nxt = b.nxt ∧
        (FOLDL drop_out b l).closing = b.closing
Proof
  Induct >> simp[]
QED

Theorem ekeep_promote:
  ekeep lfd h f es ⇒ ekeep lfd h f (promote es with settling := sl)
Proof
  simp[ekeep_def, promote_fields] >> strip_tac >>
  ‘ALOOKUP (FILTER (λ(h, f). cstat_of es f = CUp) es.ctbl) h = NONE’
    by simp[ALOOKUP_FILTER_NONE] >>
  simp[ALOOKUP_APPEND, ALOOKUP_FILTER_NONE, MEM_MAP, MEM_FILTER] >> rpt conj_tac
  >- (rpt strip_tac >> every_case_tac >> gvs[] >> drule ALOOKUP_MEM >>
      simp[MEM_FILTER] >> strip_tac >> gvs[MEM_MAP] >> metis_tac[SND])
  >- (rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[])
  >> metis_tac[]
QED

(* The end of the tail: promotion, with f not waiting to be accepted at
   the end (L1's ownership) *)
Theorem ekeep_tail:
  ekeep lfd h f es ∧ es5.p.b.tbl = es.p.b.tbl ∧ es5.p.b.nxt = es.p.b.nxt ∧
  (∀x. MEM x es5.p.b.closing ⇒ MEM x es.p.b.closing) ∧ ¬MEM f es5.p.eof ∧
  es5.ctbl = es.ctbl ∧ eown lfd (promote es5 with settling := sl) ⇒
  ekeep lfd h f (promote es5 with settling := sl)
Proof
  strip_tac >>
  ‘ekeep lfd h f (es5 with p := es5.p with acq := [])’
    by (qpat_x_assum ‘ekeep _ _ _ es’ mp_tac >> simp[ekeep_def] >> metis_tac[]) >>
  drule ekeep_promote >> disch_then (qspec_then ‘sl’ mp_tac) >>
  simp[ekeep_def, promote_fields, cstat_of_def] >> strip_tac >>
  qpat_x_assum ‘eown _ _’ mp_tac >> simp[eown_def, promote_fields, ALL_DISTINCT_APPEND] >>
  strip_tac >> strip_tac >>
  ‘MEM f (MAP SND es.p.b.tbl)’
    by (qpat_x_assum ‘ekeep _ _ _ es’ mp_tac >> simp[ekeep_def, MEM_MAP, EXISTS_PROD] >>
        metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum ‘∀e. _ ⇒ ¬MEM e es5.p.acq’ (qspec_then ‘f’ mp_tac) >> simp[]
QED

(* The tail, when its poll does not list f for input: f's handle stays and
   f's inbox is unchanged (no world fact needed) *)
Theorem etail_keep:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ ekeep lfd h f es ∧
  eown lfd es' ∧ ¬MEM f (in_fds (pf_poll_set lfd pol es.p hs)) ⇒
  ekeep lfd h f es' ∧ inb_of es'.p f = inb_of es.p f
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> rpt VAR_EQ_TAC >>
  drule l1_flush_b >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule pf_fetch_other >> disch_then (qspec_then ‘f’ mp_tac) >>
  impl_tac >- simp[MEM_FILTER, in_fds_pend] >> strip_tac >>
  qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule l1_reap_b >> strip_tac >>
  qpat_x_assum ‘settle_fds _ _ = _’ assume_tac >> drule settle_fds_p >> strip_tac >>
  ‘ps3'.b = b2’ by (qpat_x_assum ‘ps3'.b = _’ mp_tac >> simp[]) >>
  ‘es5.p.eof = ps3'.eof ∧ es5.p.b = b4 ∧ es5.p.inb = ps3'.inb’
    by (qpat_x_assum ‘es5.p = _’ (REWRITE_TAC o single) >> simp[stall_step_def]) >>
  ‘b4.tbl = es.p.b.tbl ∧ b4.nxt = es.p.b.nxt ∧ ∀x. MEM x b4.closing ⇒ MEM x es.p.b.closing’
    by (qpat_x_assum ‘∀x. MEM x b4.closing ⇒ _’ mp_tac >>
        qpat_x_assum ‘b4.tbl = _’ mp_tac >> qpat_x_assum ‘b4.nxt = _’ mp_tac >>
        simp[stall_step_def, foldl_drop_out]) >>
  ‘¬MEM f es.p.eof’ by (qpat_x_assum ‘ekeep _ _ _ es’ mp_tac >> simp[ekeep_def]) >>
  conj_tac
  >- (irule ekeep_tail >> qpat_x_assum ‘ekeep _ _ _ es’ (irule_at Any) >> simp[])
  >> simp[promote_fields, inb_of_def] >>
  qpat_x_assum ‘es5.p.inb = _’ (REWRITE_TAC o single) >>
  qpat_x_assum ‘inb_of ps3' f = _’ mp_tac >> simp[inb_of_def]
QED

Theorem pf_poll_set_lt4:
  EVERY (λ(g, e). e < 4) (pf_poll_set lfd pol ps hs)
Proof
  rw[pf_poll_set_def, EVERY_MEM, MEM_FLAT, MEM_MAP, MEM_FILTER, FORALL_PROD, PULL_EXISTS] >>
  gvs[AllCaseEqs()] >> every_case_tac >> gvs[] >> rw[] >>
  Cases_on ‘y’ >> gvs[]
QED

Theorem fopen_small:
  fopen f w ⇒ small f
Proof
  rw[fopen_def] >> drule_all fds_lt_small >> simp[fds_small_def, small_def]
QED

(* One round: L1 holds none of f's input after the round's actions' start,
   f's handle h is open and in the interest set: the round's poll lists f
   for input *)
Theorem eround_asks:
  eround lfd pol_never hs (w, es) acts = SOME (snap, ws', log, evs) ∧
  ekeep lfd h f es ∧ fopen f w ∧ MEM h hs ∧ inb_of es.p f = [] ⇒
  ∃bs e. MEM (IO_event (ExtCall «sys_poll») [0w] bs) evs ∧
         MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> rpt VAR_EQ_TAC >>
  PairCases_on ‘ws1’ >> rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, wa, ea)’ >>
  drule_all eacts_ekeep >> strip_tac >>
  ‘inb_of ea.p f = []’ by (Cases_on ‘inb_of ea.p f’ >> gvs[]) >>
  qpat_x_assum ‘etail _ _ _ _ = _’ mp_tac >> simp[etail_def, AllCaseEqs()] >> strip_tac >>
  rpt VAR_EQ_TAC >>
  ‘wants_input lfd pol_never ea.p f’
    by (qpat_x_assum ‘ekeep _ _ _ ea’ mp_tac >>
        simp[ekeep_def, wants_input_def, pol_never_def]) >>
  ‘∃e. MEM (f, e) (pf_poll_set lfd pol_never ea.p hs) ∧ ODD e’
    by (qpat_x_assum ‘ekeep _ _ _ ea’ (strip_assume_tac o REWRITE_RULE [ekeep_def]) >>
        drule_all pf_poll_set_f >> metis_tac[]) >>
  ‘e < 4’
    by (‘EVERY (λ(g, e). e < 4) (pf_poll_set lfd pol_never ea.p hs)’
          by simp[pf_poll_set_lt4] >>
        pop_assum mp_tac >> simp[EVERY_MEM, FORALL_PROD] >> disch_then drule >> simp[]) >>
  ‘small f ∧ l0_rely wa’ by (drule fopen_small >> fs[fopen_def]) >>
  qpat_x_assum ‘l1_polls _ _ = _’ mp_tac >> simp[l1_polls_def, AllCaseEqs()] >>
  strip_tac >> rpt VAR_EQ_TAC >>
  ‘MEM (f, e) (pf_poll_set lfd pol_never ea.p hs ++ MAP (λf. (f, 2n)) (pend_fds ea))’
    by simp[] >>
  qpat_x_assum ‘sys_poll _ _ = _’ assume_tac >>
  drule_all sys_poll_lists >> strip_tac >>
  qexistsl_tac [‘bs’, ‘e’] >> rpt VAR_EQ_TAC >> simp[]
QED

(* One round with no poll listing f for input: f's handle stays, f's inbox
   does not grow, and a read of h takes from it *)
Theorem eround_quiet_f:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
  ekeep lfd h f es ∧ fopen f w ∧ eown lfd es' ∧
  (∀bs e. MEM (IO_event (ExtCall «sys_poll») [0w] bs) evs ∧
          MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ⇒ ¬ODD e) ⇒
  ekeep lfd h f es' ∧ LENGTH (inb_of es'.p f) ≤ LENGTH (inb_of es.p f) ∧
  ((∃k. MEM (ERead h k) acts) ∧ inb_of es.p f ≠ [] ⇒
   LENGTH (inb_of es'.p f) < LENGTH (inb_of es.p f))
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> rpt VAR_EQ_TAC >>
  PairCases_on ‘ws1’ >> rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, wa, ea)’ >>
  drule_all eacts_ekeep >> strip_tac >>
  ‘¬MEM f (in_fds (pf_poll_set lfd pol ea.p hs))’
    by (simp[in_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> qx_gen_tac ‘e’ >>
        Cases_on ‘MEM (f, e) (pf_poll_set lfd pol ea.p hs)’ >> simp[] >>
        ‘e < 4’
          by (‘EVERY (λ(g, e). e < 4) (pf_poll_set lfd pol ea.p hs)’
                by simp[pf_poll_set_lt4] >>
              pop_assum mp_tac >> simp[EVERY_MEM, FORALL_PROD] >> disch_then drule >> simp[]) >>
        ‘small f ∧ l0_rely wa’ by (drule fopen_small >> fs[fopen_def]) >>
        qpat_x_assum ‘etail _ _ _ _ = _’ mp_tac >>
        simp[etail_def, AllCaseEqs(), l1_polls_def] >> strip_tac >> rpt VAR_EQ_TAC >>
        ‘MEM (f, e) (pf_poll_set lfd pol ea.p hs ++ MAP (λf. (f, 2n)) (pend_fds ea))’
          by simp[] >>
        qpat_x_assum ‘sys_poll _ _ = _’ assume_tac >>
        drule_all sys_poll_lists >> strip_tac >>
        qpat_x_assum ‘(_, _, _) = (rv, _, pevs)’ mp_tac >> simp[] >> strip_tac >>
        qpat_x_assum ‘∀bs e. _’ (qspecl_then [‘bs’, ‘e’] mp_tac) >>
        rpt VAR_EQ_TAC >> simp[]) >>
  drule_all etail_keep >> strip_tac >> simp[]
QED
