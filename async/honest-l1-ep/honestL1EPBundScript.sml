(*
  L1's invariant before each action of an E1 round (ebund) and what each
  action keeps of it, split off honestL1EPTotal (whose totality part the
  per-round progress theories need on their own).
  NOT YET BUILDING on r3-close + (A): edo_ebund, edo_nxt, edo_ctbl_old,
  ecm_step_conns need re-proof (the client re-proof on R3).
*)
Theory honestL1EPBund
Ancestors
  honestL1EPTotal honestL1EPRefine honestL1EPModel honestL1PFClose honestL1PFInv honestL1PFRefine
  honestL1Inv honestL1PFModel honestL1Model endpointHLModel honestL0Rely honestL0World honestL0
  alist
Libs
  preamble

(* ------------------------------------------------------------------------
   L1's invariant before each action of a round (also a failing one): the
   refinement's, with SOME layer world.  ev_act needs the layer world's
   choices to match the action's result; ev_rel does not look at them
   (the allocation only at channels that exist), so they are overwritten
   ------------------------------------------------------------------------ *)

Definition ebund_def:
  ebund lfd wl es ⇔
    eown lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ∧
    ∃a cm w hs. ev_rel lfd a cm es w ∧ ehs_rel hs es
End

Theorem cl_lt:
  MEM f (MAP FST cm) ∧ EVERY (λj. j < n) (MAP SND cm) ⇒ cl cm f < n
Proof
  rw[cl_def] >> CASE_TAC >- gvs[ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  first_x_assum drule >> simp[]
QED

Theorem ev_rel_choices:
  ev_rel lfd a cm es w ∧
  w'.listening = w.listening ∧ w'.reserved = w.reserved ∧ w'.takes = w.takes ∧
  w'.open_fds = w.open_fds ∧ w'.chans = w.chans ∧
  (∀j used. j < LENGTH w.chans ⇒ w'.alloc j used = w.alloc j used) ⇒
  ev_rel lfd a cm es w'
Proof
  rw[ev_rel_def] >> first_x_assum drule >> strip_tac >> simp[] >>
  ‘cl cm f < LENGTH w.chans’ by (irule cl_lt >> simp[]) >>
  simp[]
QED

Theorem edo_ebund:
  ebund lfd wl es ∧ edo lfd pol (wl, es) act = SOME (r, (wl', es'), evs) ⇒ ebund lfd wl' es'
Proof
  simp[ebund_def] >> strip_tac >>
  qabbrev_tac
    ‘w1 = w with <| nosock := (λk. if k = w.nconnects then r = EConnected NONE else w.nosock k);
                    alloc := (λj used. if j = LENGTH w.chans ∧ rfds es' [r] ≠ []
                                       then HD (rfds es' [r]) else w.alloc j used) |>’ >>
  ‘ev_rel lfd a cm es w1’
    by (irule ev_rel_choices >> qexists_tac ‘w’ >> simp[Abbr ‘w1’]) >>
  qpat_x_assum ‘ev_rel lfd a cm es w’ kall_tac >>
  drule ev_act >> rpt (disch_then drule) >>
  disch_then (qspec_then ‘case r of ELvl x => x | _ => 0’ mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[Abbr ‘w1’]
      >- (rpt strip_tac >> simp[Abbr ‘w1’] >>
          Cases_on ‘r’ >> gvs[rfds_def, conn_hdls_def] >>
          rename1 ‘EConnected oh’ >> Cases_on ‘oh’ >> gvs[conn_hdls_def])
      >- (rpt strip_tac >> gvs[edo_def, AllCaseEqs()])) >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem eacts_ebund:
  ∀acts wl es rs evs wl' es'.
    ebund lfd wl es ∧ eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ⇒
    ebund lfd wl' es'
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘edo _ _ _ _ = SOME (_, ws1, _)’ >>
  PairCases_on ‘ws1’ >> drule_all edo_ebund >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* ------------------------------------------------------------------------
   What a round does to the handles (for a computation that does not
   accept): the tail fetches no connection, the connect table only shrinks
   in the tail, connects number their handles from nxt, and an old
   handle's connect entry is the one it had at the round's start
   ------------------------------------------------------------------------ *)

Theorem pf_fetch_noconn:
  ∀fs w ps ws' log evs.
    ¬MEM lfd fs ∧ pf_fetch lfd pol fs (w, ps) = SOME (ws', log, evs) ⇒ ∀g. ¬MEM (FConn g) log
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >>
  simp[Once pf_fetch_def] >> rw[] >- metis_tac[] >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  qpat_x_assum ‘(_, _) = _’ mp_tac >> rw[AllCaseEqs()] >> simp[]
QED

Theorem lfd_not_in_fds:
  eown lfd es ∧ ¬MEM lfd hs ⇒
  ¬MEM lfd (in_fds (pf_poll_set lfd pol es.p hs ++ MAP (λf. (f, 2n)) (pend_fds es)))
Proof
  strip_tac >>
  ‘¬MEM lfd (MAP SND es.p.b.tbl)’ by gvs[eown_def] >>
  simp[in_fds_def, pf_poll_set_def, FILTER_APPEND, MEM_MAP, MEM_FILTER, MEM_FLAT,
       EXISTS_PROD, PULL_EXISTS] >>
  rw[] >> CCONTR_TAC >> gvs[] >> every_case_tac >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem etail_noconn:
  eown lfd es ∧ ¬MEM lfd hs ∧
  etail lfd pol hs (w, es) = SOME (rdy, ws', log, evs) ⇒ ∀g. ¬MEM (FConn g) log
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all lfd_not_in_fds >> disch_then (qspec_then ‘pol’ assume_tac) >>
  drule_at (Pos last) pf_fetch_noconn >> simp[MEM_FILTER]
QED

Theorem settle_fds_ctbl:
  ∀fs w es w' es' evs. settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ es'.ctbl = es.ctbl
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> first_x_assum drule >> every_case_tac >> simp[]
QED

Theorem etail_ctbl:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ∧ ALOOKUP es.ctbl h = NONE ⇒
  ALOOKUP es'.ctbl h = NONE
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule settle_fds_ctbl >> simp[apply_early_def, promote_def] >> strip_tac >>
  simp[ALOOKUP_FILTER_NONE]
QED

Theorem pdo_nxt:
  pdo lfd (w, ps) (Read h n) = SOME (r, (w', ps'), evs) ∨
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs) ⇒
  ps'.b.nxt = ps.b.nxt
Proof
  rw[pdo_def, AllCaseEqs()] >> gvs[] >> PairCases_on ‘z’ >>
  gvs[l1_close_def, AllCaseEqs(), forget_def, l1do_def]
QED

Theorem edo_nxt:
  edo lfd pol (wl, es) act = SOME (r, (wl', es'), evs) ∧ (∀l. act ≠ EAccept l) ⇒
  es'.p.b.nxt = es.p.b.nxt + LENGTH (conn_hdls [r]) ∧
  ∀hd. MEM hd (conn_hdls [r]) ⇒ hd = hdl lfd es.p.b.nxt
Proof
  Cases_on ‘act’ >> simp[edo_def, AllCaseEqs()] >> strip_tac >> gvs[conn_hdls_def] >>
  TRY (PairCases_on ‘z’) >> gvs[ec_del_def, conn_hdls_def]
  >- (‘z2.b.nxt = es.p.b.nxt’ by metis_tac[pdo_nxt] >> Cases_on ‘z0’ >> simp[conn_hdls_def])
  >- gvs[l1_close_def, AllCaseEqs(), forget_def]
  >- (‘z2.b.nxt = es.p.b.nxt’ by metis_tac[pdo_nxt] >> simp[conn_hdls_def])
QED

Theorem eown_ciss:
  eown lfd es ⇒ ciss lfd es
Proof
  rw[eown_def, ciss_def] >> metis_tac[]
QED

Theorem hdl_11:
  i + 1 < dimword (:64) ∧ j + 1 < dimword (:64) ∧ hdl lfd i = hdl lfd j ⇒ i = j
Proof
  strip_tac >>
  ‘w2n lfd < dimword (:64)’ by simp[w2n_lt] >>
  ‘hdln (w2n lfd) i MOD dimword (:64) = hdln (w2n lfd) i ∧
   hdln (w2n lfd) j MOD dimword (:64) = hdln (w2n lfd) j’
    by (conj_tac >> irule LESS_MOD >> simp[asyncHLModelTheory.hdln_def] >> rw[] >> gvs[]) >>
  qpat_x_assum ‘hdl _ _ = _’ mp_tac >> REWRITE_TAC[asyncHLModelTheory.hdl_def, n2w_11] >>
  ASM_REWRITE_TAC[] >> rw[asyncHLModelTheory.hdln_def]
QED

Theorem edo_ctbl_old:
  edo lfd pol (wl, es) act = SOME (r, (wl', es'), evs) ∧
  eown lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ∧
  ALOOKUP es'.ctbl h = SOME f ∧ j < es.p.b.nxt ∧ h = hdl lfd j ⇒
  ALOOKUP es.ctbl h = SOME f ∧ cstat_of es' f = cstat_of es f
Proof
  strip_tac >> Cases_on ‘∃p. act = EConnect p’
  >- (gvs[] >> Cases_on ‘r = EConnected NONE’
      >- gvs[edo_def, AllCaseEqs()] >>
      ‘∀g. es'.ctbl = (hdl lfd es.p.b.nxt, g) :: es.ctbl ⇒
           ¬MEM g (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl)’
        by metis_tac[edo_connect_fresh] >>
      qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def, AllCaseEqs()] >> strip_tac >>
      gvs[] >>
      ‘j + 1 < dimword (:64) ∧ es.p.b.nxt + 1 < dimword (:64)’
        by (‘w2n lfd < dimword (:64)’ by simp[w2n_lt] >>
            gvs[asyncHLModelTheory.hdln_def] >> every_case_tac >> gvs[]) >>
      ‘hdl lfd j ≠ hdl lfd es.p.b.nxt’
        by (strip_tac >> drule_at (Pos last) hdl_11 >> simp[]) >>
      gvs[] >>
      ‘MEM f (MAP SND es.ctbl)’ by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >>
                                    metis_tac[]) >>
      ‘f ≠ n2w (res_val out)’ by metis_tac[] >>
      simp[cstat_of_def, ALOOKUP_ADELKEY]) >>
  Cases_on ‘act’ >> gvs[edo_def, AllCaseEqs()] >> TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (simp[cstat_of_def] >> NO_TAC) >>
  rename1 ‘ec_del hh ff’ >> gvs[ec_del_def, ALOOKUP_ADELKEY] >>
  ‘ALL_DISTINCT (MAP SND es.ctbl)’ by gvs[eown_def, ALL_DISTINCT_APPEND] >>
  ‘ff ≠ f’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  simp[cstat_of_def, ALOOKUP_ADELKEY]
QED

Theorem eacts_nxt:
  ∀acts wl es rs evs wl' es'.
    EVERY (λa. ∀l. a ≠ EAccept l) acts ∧
    eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ⇒
    es'.p.b.nxt = es.p.b.nxt + LENGTH (conn_hdls rs) ∧
    ∀hd. MEM hd (conn_hdls rs) ⇒ ∃j. es.p.b.nxt ≤ j ∧ j < es'.p.b.nxt ∧ hd = hdl lfd j
Proof
  Induct >> simp[eacts_def, conn_hdls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘edo _ _ _ _ = SOME (r, ws1, _)’ >>
  PairCases_on ‘ws1’ >> drule_all edo_nxt >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  ONCE_REWRITE_TAC[conn_hdls_cons] >> simp[] >> rw[]
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘es.p.b.nxt’ >> simp[] >>
      Cases_on ‘conn_hdls [r]’ >> gvs[])
  >> first_x_assum drule >> strip_tac >> qexists_tac ‘j’ >> simp[]
QED

Theorem eacts_ctbl_old:
  ∀acts wl es rs evs wl' es' h f j.
    ebund lfd wl es ∧ eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ∧
    ALOOKUP es'.ctbl h = SOME f ∧ j < es.p.b.nxt ∧ h = hdl lfd j ⇒
    ALOOKUP es.ctbl h = SOME f ∧ cstat_of es' f = cstat_of es f
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘edo _ _ _ _ = SOME (r, ws1, _)’ >>
  PairCases_on ‘ws1’ >>
  drule_all edo_ebund >> strip_tac >>
  ‘eown lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl’ by gvs[ebund_def] >>
  ‘es.p.b.nxt ≤ ws11.p.b.nxt’ by metis_tac[edo_ciss, eown_ciss] >>
  ‘j < ws11.p.b.nxt’ by simp[] >>
  first_x_assum drule_all >> strip_tac >>
  drule edo_ctbl_old >> disch_then (qspecl_then [‘j’, ‘hdl lfd j’, ‘f’] mp_tac) >>
  simp[]
QED

(* An old handle with no connect entry gets none *)
Theorem eacts_ctbl_none:
  ebund lfd wl es ∧ eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ∧
  ALOOKUP es.ctbl (hdl lfd j) = NONE ∧ j < es.p.b.nxt ⇒
  ALOOKUP es'.ctbl (hdl lfd j) = NONE
Proof
  strip_tac >> Cases_on ‘ALOOKUP es'.ctbl (hdl lfd j)’ >> simp[] >>
  drule eacts_ctbl_old >> disch_then drule >>
  disch_then (qspecl_then [‘hdl lfd j’, ‘x’, ‘j’] mp_tac) >> simp[]
QED

(* An old handle read with data has no connect entry after (when its
   entry, if any, was refused at the start) *)
Theorem eacts_ctbl_gone:
  ∀acts wl es rs evs wl' es' k hd n y j.
    ebund lfd wl es ∧ eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ∧
    k < LENGTH acts ∧ EL k acts = ERead hd n ∧ EL k rs = EGot y ∧
    hd = hdl lfd j ∧ j < es.p.b.nxt ∧
    (∀f. ALOOKUP es.ctbl hd = SOME f ⇒ cstat_of es f = CRefused) ⇒
    ALOOKUP es'.ctbl hd = NONE
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘edo _ _ _ _ = SOME (r, ws1, _)’ >>
  PairCases_on ‘ws1’ >>
  drule_all edo_ebund >> strip_tac >>
  ‘eown lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl’ by gvs[ebund_def] >>
  ‘es.p.b.nxt ≤ ws11.p.b.nxt’ by metis_tac[edo_ciss, eown_ciss] >>
  Cases_on ‘k’ >> gvs[]
  >- (‘ALOOKUP es.ctbl (hdl lfd j) = NONE’
        by (Cases_on ‘ALOOKUP es.ctbl (hdl lfd j)’ >> simp[] >>
            first_x_assum drule >> strip_tac >>
            qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def, FORALL_PROD]) >>
      ‘ALOOKUP ws11.ctbl (hdl lfd j) = NONE’
        by (qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >> rw[] >>
            PairCases_on ‘z’ >> gvs[]) >>
      qpat_x_assum ‘eacts _ _ (ws10, ws11) _ = _’ assume_tac >>
      drule_at (Pos (el 2)) eacts_ctbl_none >> simp[]) >>
  first_x_assum (qspecl_then [‘ws10’, ‘ws11’, ‘rs'’, ‘evs'’, ‘wl'’, ‘es'’, ‘n'’, ‘n’, ‘y’, ‘j’]
                  mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >>
               drule edo_ctbl_old >> disch_then (qspecl_then [‘j’, ‘hdl lfd j’, ‘f’] mp_tac) >>
               simp[]) >>
  simp[]
QED

Theorem hdl_not_lfd:
  j + 1 < dimword (:64) ⇒ hdl lfd j ≠ lfd
Proof
  strip_tac >>
  ‘w2n lfd < dimword (:64)’ by simp[w2n_lt] >>
  ‘hdln (w2n lfd) j < dimword (:64)’ by (simp[asyncHLModelTheory.hdln_def] >> rw[] >> gvs[]) >>
  simp[asyncHLModelTheory.hdl_def] >> strip_tac >>
  ‘w2n (n2w (hdln (w2n lfd) j) : word64) = w2n lfd’ by simp[] >>
  qpat_x_assum ‘n2w _ = lfd’ kall_tac >>
  ‘hdln (w2n lfd) j MOD dimword (:64) = hdln (w2n lfd) j’ by simp[LESS_MOD] >>
  qpat_x_assum ‘w2n _ = w2n lfd’ mp_tac >> REWRITE_TAC[w2n_n2w] >> ASM_REWRITE_TAC[] >>
  rw[asyncHLModelTheory.hdln_def]
QED

(* A round that fetches no connection adds its connects' channels only *)
Theorem ecm_step_conns:
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  eacts lfd pol ws (new_actions (log_of m) h) = SOME (rs, aevs, ws1) ∧
  etail lfd pol (ifds h) ws1 = SOME (rdy, ws2, log, tevs) ∧
  (∀g. ¬MEM (FConn g) log) ⇒
  SND (ecm lfd pol ifds m w0 (SUC n)) = SND (ecm lfd pol ifds m w0 n) + LENGTH (conn_hdls rs)
Proof
  strip_tac >>
  ‘erounds lfd pol ifds m (w0, einit) (SUC n) =
     SOME (h ++ [ssnap rdy rs], ws2, evs ++ (aevs ++ tevs), logs ++ [log])’
    by simp[erounds_def, eround_def] >>
  drule erounds_logs >> strip_tac >>
  ‘LENGTH logs = n’ by gvs[] >>
  ‘elog lfd pol ifds m w0 n = log’
    by (qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ mp_tac >>
        simp[elog_def, EL_APPEND2]) >>
  ‘econ lfd pol ifds m w0 n = rfds (SND ws1) rs’ by simp[econ_def, eacts_of_def] >>
  simp[ecm_SUC, ecm1_def] >> pairarg_tac >> simp[] >>
  Cases_on ‘arrs lfd (cnew k (rfds (SND ws1) rs) ++ cm, k + LENGTH (rfds (SND ws1) rs)) log’ >>
  PairCases_on ‘r’ >> drule arrs_count >> simp[rfds_length] >> strip_tac >>
  ‘FILTER (λx. ∃g. x = FConn g) log = []’
    by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED
