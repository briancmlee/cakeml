(*
  [R3] L1's own invariant on every run, with EClose and EShut (task D,
  option (a); for close-v2's E1 EClose refinement and e1_conn_live).

  honestL1EPRefine proves eown only bundled with the handle layer's world
  (ev_act, ev_tail), whose EClose/EShut are no step yet, so only for runs
  without them (noclose).  Here L1's part alone: eown0 (eown without its
  "no shutdown queued" conjunct) and L0's side (l0owne, the rely, the fd
  bound) hold after every action (EClose and EShut included), the tail and
  the queued shutdowns, so on every run.

  MAIN: eround_eown0, eown_run.
*)
Theory honestL1EPOwnRun
Ancestors
  honestL1EPRefine honestL1EPOut honestL1EPModel honestL1PFClose honestL1PFRefine
  honestL1PFModel honestL1Model honestL1Steps
  honestL0Rely honestL0World honestL0WorldProps honestL0
  asyncCore alist
Libs
  preamble

(* eown without es.shq = [] ∧ es.shut = [] *)
Definition eown0_def:
  eown0 lfd es ⇔
    pown lfd es.p ∧
    ALL_DISTINCT (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl) ∧
    ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl) ∧
    (∀h f. ALOOKUP es.ctbl h = SOME f ⇒
       (∃i. i < es.p.b.nxt ∧ h = hdl lfd i) ∧ cstat_of es f ≠ CUp) ∧
    (∀f. MEM f (MAP FST es.early) ⇒ MEM f (MAP SND es.ctbl) ∧ cstat_of es f = CPending) ∧
    ALL_DISTINCT (MAP FST es.early) ∧ EVERY (λ(f, c). c ≠ CPending) es.early ∧
    (∀h. MEM h es.settling ⇒ ∃i. i < es.p.b.nxt ∧ h = hdl lfd i)
End

Theorem eown_eown0:
  eown lfd es ⇔ eown0 lfd es ∧ es.shq = [] ∧ es.shut = []
Proof
  simp[eown_def, eown0_def] >> metis_tac[]
QED

Theorem eown0_proj:
  eown0 lfd es ⇔ eown lfd (es with <| shq := []; shut := [] |>)
Proof
  simp[eown_def, eown0_def, cstat_of_def]
QED

Theorem eown0_sh[simp]:
  (eown0 lfd (es with shq := q) ⇔ eown0 lfd es) ∧
  (eown0 lfd (es with shut := s) ⇔ eown0 lfd es) ∧
  (l0owne lfd w (es with shq := q) ⇔ l0owne lfd w es) ∧
  (l0owne lfd w (es with shut := s) ⇔ l0owne lfd w es)
Proof
  simp[eown0_def, l0owne_def, l0own_def, cstat_of_def]
QED

Theorem with_p_self[local,simp]:
  (es : l1e) with p := es.p = es
Proof
  simp[honestL1EPModelTheory.l1e_component_equality]
QED

(* ------------------------------------------------------------------------
   Changing the prefetching part
   ------------------------------------------------------------------------ *)

Theorem eown0_p:
  eown0 lfd es ∧ pown lfd ps' ∧ es.p.b.nxt ≤ ps'.b.nxt ∧
  (∀g. MEM g (MAP SND ps'.b.tbl) ∨ MEM g ps'.b.closing ∨ MEM g ps'.acq ⇒
       ¬MEM g (MAP SND es.ctbl)) ∧
  (∀k. MEM k (MAP FST ps'.b.tbl) ⇒ ¬MEM k (MAP FST es.ctbl)) ⇒
  eown0 lfd (es with p := ps')
Proof
  simp[eown0_def, cstat_of_def] >> strip_tac >>
  ‘¬MEM lfd (MAP SND es.ctbl)’ by gvs[ALL_DISTINCT_APPEND] >>
  ‘ALL_DISTINCT (MAP SND es.ctbl) ∧ ALL_DISTINCT (MAP FST es.ctbl)’ by gvs[ALL_DISTINCT_APPEND] >>
  qpat_x_assum ‘pown _ ps'’ mp_tac >> simp[pown_def] >> strip_tac >>
  rpt conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ _’ drule >> strip_tac >>
      simp[] >> qexists_tac ‘i’ >> simp[])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac >> qexists_tac ‘i’ >> simp[]
QED

(* The held fds and the handles do not grow *)
Theorem eown0_p_sub:
  eown0 lfd es ∧ pown lfd ps' ∧ es.p.b.nxt ≤ ps'.b.nxt ∧
  (∀g. MEM g (MAP SND ps'.b.tbl) ∨ MEM g ps'.b.closing ∨ MEM g ps'.acq ⇒
       MEM g (MAP SND es.p.b.tbl) ∨ MEM g es.p.b.closing ∨ MEM g es.p.acq) ∧
  (∀k. MEM k (MAP FST ps'.b.tbl) ⇒ MEM k (MAP FST es.p.b.tbl)) ⇒
  eown0 lfd (es with p := ps')
Proof
  strip_tac >> irule eown0_p >> simp[] >>
  ‘ALL_DISTINCT (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl) ∧
   ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl)’ by gvs[eown0_def] >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem pown_nxt:
  pown lfd ps ∧ ps.b.nxt ≤ n ⇒ pown lfd (ps with b := ps.b with nxt := n)
Proof
  simp[pown_def, inb_of_def] >> rw[] >> res_tac >> qexists_tac ‘i’ >> simp[]
QED

Theorem eown0_settling_sub:
  eown0 lfd es ∧ (∀h. MEM h s ⇒ MEM h es.settling) ⇒ eown0 lfd (es with settling := s)
Proof
  simp[eown0_def, cstat_of_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The actions
   ------------------------------------------------------------------------ *)

Theorem pdo_accept_eown0:
  eown0 lfd es ∧ pdo lfd (w, es.p) (Accept l) = SOME (r, (w', ps'), evs) ⇒
  eown0 lfd (es with p := ps')
Proof
  simp[pdo_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘es.p.acq = f :: q’ >>
  qabbrev_tac ‘hn = hdl l es.p.b.nxt’ >>
  ‘∀i. i < es.p.b.nxt ⇒ hdl l i ≠ hn’
    by (rw[Abbr ‘hn’] >> irule hdl_fresh >> gvs[l1hdl_hdl]) >>
  ‘¬MEM hn (MAP FST es.p.b.tbl) ∧ ¬MEM hn (MAP FST es.ctbl)’
    by (qpat_x_assum ‘eown0 _ _’ mp_tac >> simp[eown0_def, pown_def, l1hdl_hdl] >> strip_tac >>
        conj_tac >> strip_tac >> gvs[MEM_MAP, EXISTS_PROD] >> rename1 ‘MEM (hn, g) _’
        >- (‘ALOOKUP es.p.b.tbl hn = SOME g’ by (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[ALL_DISTINCT_APPEND]) >>
            first_x_assum drule >> strip_tac >> metis_tac[])
        >> ‘ALOOKUP es.ctbl hn = SOME g’ by (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[ALL_DISTINCT_APPEND]) >>
        qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ _’ drule >> strip_tac >> metis_tac[]) >>
  ‘f ≠ l ∧ ¬MEM f (MAP SND es.p.b.tbl) ∧ ¬MEM f q ∧ ¬MEM f es.p.b.closing ∧
   ¬MEM f (MAP SND es.ctbl)’
    by (gvs[eown0_def, pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘∀g. MEM g (MAP SND es.p.b.tbl) ∨ MEM g es.p.b.closing ∨ MEM g es.p.acq ⇒
       ¬MEM g (MAP SND es.ctbl)’ by (gvs[eown0_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘∀k. MEM k (MAP FST es.p.b.tbl) ⇒ ¬MEM k (MAP FST es.ctbl)’
    by (gvs[eown0_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  irule eown0_p >> simp[] >> rpt conj_tac >>
  TRY (rpt strip_tac >> gvs[] >> metis_tac[] >> NO_TAC) >>
  qpat_x_assum ‘eown0 _ _’ mp_tac >> simp[eown0_def, pown_def, inb_of_def, l1hdl_hdl] >>
  strip_tac >> gvs[ALL_DISTINCT_APPEND] >> rpt conj_tac >>
  TRY (metis_tac[] >> NO_TAC) >>
  rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (qexists_tac ‘es.p.b.nxt’ >> gvs[markerTheory.Abbrev_def]) >>
  qpat_x_assum ‘∀h f'. ALOOKUP es.p.b.tbl h = SOME f' ⇒ _’ drule >> strip_tac >>
  qexists_tac ‘i’ >> simp[]
QED

Theorem eown0_ec_del:
  eown0 lfd es ∧ ALOOKUP es.ctbl h = SOME f ∧ ¬MEM f (MAP FST es.early) ⇒
  eown0 lfd (ec_del h f es)
Proof
  strip_tac >>
  ‘ALL_DISTINCT (MAP FST es.ctbl) ∧ ALL_DISTINCT (MAP SND es.ctbl)’
    by gvs[eown0_def, ALL_DISTINCT_APPEND] >>
  ‘∀g. MEM g (MAP SND (ADELKEY h es.ctbl)) ⇔ MEM g (MAP SND es.ctbl) ∧ g ≠ f’
    by metis_tac[MEM_SND_ADELKEY] >>
  qpat_x_assum ‘eown0 _ _’ mp_tac >>
  simp[eown0_def, cstat_of_ec_del] >> simp[ec_del_def] >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, ALL_DISTINCT_MAP_FST_ADELKEY, ALL_DISTINCT_MAP_SND_ADELKEY,
      MEM_FST_ADELKEY, ALOOKUP_ADELKEY, MEM_FILTER, FILTER_ALL_DISTINCT] >>
  rpt conj_tac >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  res_tac >> gvs[]
QED

Theorem eown0_early_del:
  eown0 lfd es ⇒ eown0 lfd (es with early := ADELKEY f es.early)
Proof
  simp[eown0_def, cstat_of_def, MEM_FST_ADELKEY, ALL_DISTINCT_MAP_FST_ADELKEY] >>
  strip_tac >> rpt conj_tac >> TRY (metis_tac[] >> NO_TAC) >>
  simp[ADELKEY_def] >> irule EVERY_FILTER_IMP >> simp[]
QED

(* The fd of a connect handle being closed or refused *)
Theorem eown0_ctbl_close:
  eown0 lfd es ∧ ALOOKUP es.ctbl h = SOME f ∧ l1_close f (w, es.p.b) = SOME ((w', b'), evs) ⇒
  eown0 lfd (es with p := es.p with b := b')
Proof
  strip_tac >> drule l1_close_b >> strip_tac >>
  irule eown0_p_sub >> simp[] >>
  ‘pown lfd es.p’ by gvs[eown0_def] >>
  rpt conj_tac >> TRY (irule pown_closing_filter >> simp[] >> metis_tac[] >> NO_TAC) >>
  rw[MEM_FILTER] >> simp[]
QED

Theorem edo_eown0:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧
  eown0 lfd es ∧ l0owne lfd w es ∧ l0_rely w ∧ fds_lt w ⇒
  eown0 lfd es'
Proof
  strip_tac >> Cases_on ‘a’ >| [
    (* EAccept *)
    gvs[edo_def] >> PairCases_on ‘z’ >> gvs[] >> drule_all pdo_accept_eown0 >> simp[],
    (* ERead *)
    qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
    Cases_on ‘ALOOKUP es.ctbl c’ >> simp[]
    >- (IF_CASES_TAC >- (strip_tac >> gvs[]) >>
        simp[pdo_def, AllCaseEqs()] >> strip_tac >> gvs[]
        >- (irule eown0_p_sub >> simp[set_inb_fields] >>
            irule pown_set_inb >> gvs[eown0_def] >> metis_tac[ALOOKUP_SOME_MEM_SND])
        >> gvs[ep_eof_def]) >>
    rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
    rw[] >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
    rename1 ‘l1_close f (w, es.p.b) = SOME ((w', b'), evs)’ >>
    drule_all eown0_ctbl_close >> strip_tac >>
    irule eown0_ec_del >> simp[] >>
    strip_tac >> gvs[eown0_def, cstat_of_def],
    (* EWrite *)
    gvs[edo_def, AllCaseEqs()] >> PairCases_on ‘z’ >> gvs[] >>
    qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
    pairarg_tac >> gvs[] >> drule l1do_write_tbl >> strip_tac >>
    irule eown0_p_sub >> simp[] >>
    ‘pown lfd es.p’ by gvs[eown0_def] >> drule_at (Pos last) (iffRL pown_b) >> simp[],
    (* EConnect *)
    qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
    TRY (PairCases_on ‘z’ >> gvs[] >> NO_TAC) >>
    drule_all sys_connect_l0 >> strip_tac >>
    qmatch_goalsub_abbrev_tac ‘(hn, f) :: es.ctbl’ >>
    qmatch_goalsub_abbrev_tac ‘_ with <| p := _; ctbl := _; cst := _; settling := _; early := ely |>’ >>
    ‘¬MEM f (l0_used w)’ by gvs[Abbr ‘f’] >>
    ‘f ≠ lfd ∧ ¬MEM f (MAP SND es.p.b.tbl) ∧ ¬MEM f es.p.b.closing ∧ ¬MEM f es.p.acq ∧
     ¬MEM f (MAP SND es.ctbl)’ by (gvs[l0owne_def, l0own_def] >> metis_tac[]) >>
    ‘¬MEM f (MAP FST es.early)’ by (gvs[eown0_def] >> metis_tac[]) >>
    ‘∀i. i < es.p.b.nxt ⇒ hdl lfd i ≠ hn’
      by (rw[Abbr ‘hn’] >> irule hdl_fresh >> gvs[l1hdl_hdl]) >>
    ‘¬MEM hn (MAP FST es.p.b.tbl) ∧ ¬MEM hn (MAP FST es.ctbl)’
      by (qpat_x_assum ‘eown0 _ _’ mp_tac >> simp[eown0_def, pown_def, l1hdl_hdl] >> strip_tac >>
          conj_tac >> strip_tac >> gvs[MEM_MAP, EXISTS_PROD] >> rename1 ‘MEM (hn, g) _’
          >- (‘ALOOKUP es.p.b.tbl hn = SOME g’
                by (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[ALL_DISTINCT_APPEND]) >>
              first_x_assum drule >> strip_tac >> metis_tac[])
          >> ‘ALOOKUP es.ctbl hn = SOME g’
               by (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[ALL_DISTINCT_APPEND]) >>
          qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ _’ drule >> strip_tac >> metis_tac[]) >>
    ‘EVERY (λ(f, c). c ≠ CPending) ely ∧ ALL_DISTINCT (MAP FST ely) ∧
     ∀g. MEM g (MAP FST ely) ⇒ MEM g (MAP FST es.early) ∨ g = f’
      by (simp[Abbr ‘ely’] >> rw[] >> gvs[eown0_def] >> every_case_tac >> gvs[]) >>
    qpat_x_assum ‘eown0 _ _’ mp_tac >>
    simp[eown0_def, pown_def, cstat_of_def, l1hdl_hdl, ALOOKUP_ADELKEY, inb_of_def] >>
    strip_tac >> gvs[ALL_DISTINCT_APPEND] >> rpt conj_tac >>
    TRY (metis_tac[] >> NO_TAC) >>
    TRY (rpt strip_tac >> res_tac >> qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
    TRY ((* settling *)
         rpt strip_tac
         >- (qexists_tac ‘es.p.b.nxt’ >> fs[markerTheory.Abbrev_def]) >>
         res_tac >> qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
    TRY ((* early *)
         rpt gen_tac >> strip_tac >>
         qpat_x_assum ‘∀g. MEM g (MAP FST ely) ⇒ _’ drule >> strip_tac
         >- (qpat_x_assum ‘∀f'. MEM f' (MAP FST es.early) ⇒ _’ drule >> strip_tac >>
             ‘f ≠ f'’ by (strip_tac >> gvs[]) >> simp[]) >>
         simp[] >> NO_TAC) >>
    (* the connect table *)
    rpt gen_tac >> IF_CASES_TAC >> strip_tac
    >- (‘f' = f’ by gvs[] >> simp[] >> qexists_tac ‘es.p.b.nxt’ >> fs[markerTheory.Abbrev_def]) >>
    qpat_x_assum ‘∀h f'. ALOOKUP es.ctbl h = SOME f' ⇒ _’ drule >> strip_tac >>
    ‘f ≠ f'’ by (strip_tac >> imp_res_tac ALOOKUP_SOME_MEM_SND >> gvs[]) >>
    simp[] >> qexists_tac ‘i’ >> simp[],
    (* ELevel *)
    gvs[edo_def],
    (* EClose *)
    qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
    Cases_on ‘ALOOKUP es.ctbl c’ >> simp[]
    >- (Cases_on ‘ALOOKUP es.p.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
        rename1 ‘ALOOKUP es.p.b.tbl h = SOME f’ >>
        strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
        qabbrev_tac ‘ps1 = set_inb f [] es.p’ >>
        ‘pown lfd ps1’ by (simp[Abbr ‘ps1’] >> irule pown_set_inb >> gvs[eown0_def] >>
                           metis_tac[ALOOKUP_SOME_MEM_SND]) >>
        ‘ps1.b = es.p.b ∧ ps1.acq = es.p.acq ∧ inb_of ps1 f = []’
          by simp[Abbr ‘ps1’, set_inb_def, inb_of_def, ALOOKUP_ADELKEY] >>
        ‘ALOOKUP ps1.b.tbl h = SOME f’ by simp[] >>
        ‘z1.b.tbl = ADELKEY h ps1.b.tbl ∧ z1.b.nxt = ps1.b.nxt ∧ z1.acq = ps1.acq ∧
         z1.inb = ps1.inb ∧ z1.eof = FILTER ($≠ f) ps1.eof ∧
         (z1.b.closing = FILTER ($≠ f) ps1.b.closing ∨ z1.b.closing = f :: ps1.b.closing)’
          by (qpat_x_assum ‘pf_close _ _ = _’ mp_tac >>
              simp[pf_close_def, pf_release_def] >> IF_CASES_TAC >> simp[] >>
              TRY (strip_tac >> gvs[] >> NO_TAC) >>
              strip_tac >> PairCases_on ‘z’ >> gvs[] >> drule l1_close_b >> simp[]) >>
        ‘pown lfd z1’
          by (qpat_x_assum ‘pown lfd ps1’ assume_tac >> drule read_eof_pown >>
              disch_then drule >> disch_then irule >> simp[]) >>
        qpat_x_assum ‘ps1.b = es.p.b’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        qpat_x_assum ‘ps1.acq = es.p.acq’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        irule eown0_p_sub >> simp[] >> rpt conj_tac >>
        TRY (simp[MEM_FILTER] >> metis_tac[MEM_SND_ADELKEY_sub, MEM_FST_ADELKEY,
                                           ALOOKUP_SOME_MEM_SND] >> NO_TAC) >>
        rpt strip_tac >> gvs[MEM_FILTER, MEM_FST_ADELKEY] >>
        metis_tac[MEM_SND_ADELKEY_sub, ALOOKUP_SOME_MEM_SND]) >>
    rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
    strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
    rename1 ‘l1_close f (w, es.p.b) = SOME ((w', b'), evs)’ >>
    drule_all eown0_ctbl_close >> strip_tac >>
    irule eown0_ec_del >> simp[MEM_FST_ADELKEY] >>
    drule eown0_early_del >> disch_then (qspec_then ‘f’ mp_tac) >> simp[],
    (* EShut *)
    gvs[edo_def, AllCaseEqs()]]
QED

(* ------------------------------------------------------------------------
   The actions: L0's side
   ------------------------------------------------------------------------ *)

Theorem pdo_l0owne0:
  pdo lfd (wl, es.p) a = SOME (r, (wl', ps'), evs) ∧
  l0_rely wl ∧ fds_lt wl ∧ l0owne lfd wl es ∧ eown0 lfd es ⇒
  l0_rely wl' ∧ fds_lt wl' ∧ l0owne lfd wl' (es with p := ps')
Proof
  strip_tac >> ‘pown lfd es.p ∧ l0own lfd wl es.p’ by gvs[eown0_def, l0owne_def] >>
  drule_all pdo_l0 >> strip_tac >> imp_res_tac pdo_keep >>
  simp[l0owne_def] >> rw[] >>
  qpat_x_assum ‘∀g. ¬MEM g (MAP SND es.p.b.tbl) ⇒ _’ irule >>
  gvs[l0owne_def, eown0_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem l1_close_l0owne:
  ∀lfd es w f b w' b' evs es'.
  eown0 lfd es ∧ l0owne lfd w es ∧ l0_rely w ∧ fds_lt w ∧
  (MEM f (MAP SND es.ctbl) ∨ MEM f (MAP SND es.p.b.tbl)) ∧
  l1_close f (w, b) = SOME ((w', b'), evs) ∧
  (∀g. MEM g (MAP SND es'.p.b.tbl) ∨ MEM g es'.p.b.closing ∨ MEM g es'.p.acq ∨
       MEM g (MAP SND es'.ctbl) ⇒
       g ≠ f ∧ (MEM g (MAP SND es.p.b.tbl) ∨ MEM g es.p.b.closing ∨ MEM g es.p.acq ∨
                MEM g (MAP SND es.ctbl))) ⇒
  l0_rely w' ∧ fds_lt w' ∧ l0owne lfd w' es'
Proof
  rpt gen_tac >> strip_tac >> drule_all l1_close_l0 >> strip_tac >>
  ‘f ≠ lfd’ by (gvs[eown0_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  gvs[fds_lt_def, l0owne_def, l0own_def] >> rpt strip_tac >>
  TRY (res_tac >> NO_TAC) >>
  qpat_x_assum ‘∀g. g ≠ f ∧ MEM g (l0_used w) ⇒ _’ irule >> metis_tac[]
QED

Theorem edo_l0owne0:
  edo lfd pol (wl, es) a = SOME (r, (wl', es'), evs) ∧
  l0_rely wl ∧ fds_lt wl ∧ l0owne lfd wl es ∧ eown0 lfd es ⇒
  l0_rely wl' ∧ fds_lt wl' ∧ l0owne lfd wl' es'
Proof
  strip_tac >>
  ‘ALL_DISTINCT (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl) ∧
   ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl)’ by gvs[eown0_def] >>
  Cases_on ‘a’ >| [
    (* EAccept *)
    gvs[edo_def] >> PairCases_on ‘z’ >> gvs[] >> drule_all pdo_l0owne0 >> simp[],
    (* ERead *)
    gvs[edo_def, AllCaseEqs()] >>
      TRY (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_l0owne0 >> simp[] >> NO_TAC) >>
      TRY (gvs[] >> NO_TAC) >>   (* EOF: kept *)
      PairCases_on ‘z’ >> gvs[] >> rename1 ‘l1_close f _ = SOME ((wl', b'), evs)’ >>
      irule l1_close_l0owne >>
      qexistsl_tac [‘es.p.b’, ‘b'’, ‘es’, ‘evs’, ‘f’, ‘wl’] >> simp[] >>
      ‘MEM f (MAP SND es.ctbl) ∧ ALL_DISTINCT (MAP SND es.ctbl) ∧ ALL_DISTINCT (MAP FST es.ctbl)’
        by (imp_res_tac ALOOKUP_SOME_MEM_SND >> gvs[ALL_DISTINCT_APPEND]) >>
      ‘∀g. MEM g (MAP SND (ADELKEY c es.ctbl)) ⇔ MEM g (MAP SND es.ctbl) ∧ g ≠ f’
        by (gen_tac >> irule MEM_SND_ADELKEY >> simp[]) >>
      drule_all l1_close_b >> strip_tac >>
      simp[ec_del_def, MEM_FILTER] >>
    qpat_x_assum ‘ALL_DISTINCT (MAP SND _ ++ _ ++ _ ++ _)’ mp_tac >>
    simp[ALL_DISTINCT_APPEND] >> metis_tac[],
    (* EWrite *)
    gvs[edo_def, AllCaseEqs()] >> PairCases_on ‘z’ >> gvs[] >> drule_all pdo_l0owne0 >> simp[],
    (* EConnect *)
    gvs[edo_def, AllCaseEqs()] >> drule_all sys_connect_l0 >> strip_tac >> simp[] >>
    TRY (PairCases_on ‘z’ >> gvs[] >>
         rename1 ‘sys_close (n2w (res_val out)) wc = SOME (_, wl', _)’ >>
         qpat_x_assum ‘sys_close _ _ = _’ assume_tac >> drule_all sys_close_l0 >> strip_tac >>
         ‘∀g. MEM g (l0_used wl) ⇒ MEM g (l0_used wl')’
           by (rpt strip_tac >> qpat_x_assum ‘∀g. g ≠ _ ∧ MEM g (l0_used wc) ⇒ _’ irule >>
               metis_tac[]) >>
         gvs[fds_lt_def, l0owne_def, l0own_def] >> metis_tac[] >> NO_TAC) >>
    gvs[l0owne_def, l0own_def, l1hdl_hdl] >> metis_tac[],
    (* ELevel *)
    gvs[edo_def],
    (* EClose *)
    qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
    Cases_on ‘ALOOKUP es.ctbl c’ >> simp[]
    >- (Cases_on ‘ALOOKUP es.p.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
        rename1 ‘ALOOKUP es.p.b.tbl h = SOME f’ >>
        strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
        ‘MEM f (MAP SND es.p.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
        ‘ALL_DISTINCT (MAP FST es.p.b.tbl) ∧ ALL_DISTINCT (MAP SND es.p.b.tbl)’
          by gvs[ALL_DISTINCT_APPEND] >>
        ‘∀g. MEM g (MAP SND (ADELKEY h es.p.b.tbl)) ⇔ MEM g (MAP SND es.p.b.tbl) ∧ g ≠ f’
          by (gen_tac >> irule MEM_SND_ADELKEY >> simp[]) >>
        qpat_x_assum ‘pf_close _ _ = _’ mp_tac >>
        simp[pf_close_def, pf_release_def, set_inb_def] >> IF_CASES_TAC >> simp[]
        >- (strip_tac >> PairCases_on ‘z’ >> gvs[] >>
            rename1 ‘l1_close f _ = SOME ((wl', b'), evs)’ >>
            irule l1_close_l0owne >>
            qexistsl_tac [‘es.p.b with tbl := ADELKEY h es.p.b.tbl’, ‘b'’, ‘es’, ‘evs’, ‘f’, ‘wl’] >>
            simp[] >>
            drule l1_close_b >> strip_tac >> simp[MEM_FILTER] >>
            gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
        strip_tac >> gvs[l0owne_def, l0own_def] >> metis_tac[]) >>
    rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
    strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
    rename1 ‘l1_close f _ = SOME ((wl', b'), evs)’ >>
    irule l1_close_l0owne >>
    qexistsl_tac [‘es.p.b’, ‘b'’, ‘es’, ‘evs’, ‘f’, ‘wl’] >> simp[] >>
    ‘MEM f (MAP SND es.ctbl) ∧ ALL_DISTINCT (MAP SND es.ctbl) ∧ ALL_DISTINCT (MAP FST es.ctbl)’
      by (imp_res_tac ALOOKUP_SOME_MEM_SND >> gvs[ALL_DISTINCT_APPEND]) >>
    ‘∀g. MEM g (MAP SND (ADELKEY h es.ctbl)) ⇔ MEM g (MAP SND es.ctbl) ∧ g ≠ f’
      by (gen_tac >> irule MEM_SND_ADELKEY >> simp[]) >>
    drule_all l1_close_b >> strip_tac >>
    simp[ec_del_def, MEM_FILTER] >>
    qpat_x_assum ‘ALL_DISTINCT (MAP SND _ ++ _ ++ _ ++ _)’ mp_tac >>
    simp[ALL_DISTINCT_APPEND] >> metis_tac[],
    (* EShut *)
    gvs[edo_def, AllCaseEqs()]]
QED

Theorem eacts_eown0:
  ∀acts wl es rs evs wl' es'.
    eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ∧
    eown0 lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ⇒
    eown0 lfd es' ∧ l0owne lfd wl' es' ∧ l0_rely wl' ∧ fds_lt wl'
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >> PairCases_on ‘ws1’ >>
  drule_all edo_eown0 >> strip_tac >>
  drule_all edo_l0owne0 >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* ------------------------------------------------------------------------
   The round's tail
   ------------------------------------------------------------------------ *)

Theorem pown_pause[simp]:
  pown lfd (ps with pause := x) = pown lfd ps ∧
  l0own lfd w (ps with pause := x) = l0own lfd w ps
Proof
  simp[pown_def, l0own_def, inb_of_def]
QED

(* The fetch keeps L1's own invariant and its fds open *)
Theorem pf_fetch_own:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    l0_rely w ∧ fds_lt w ∧ pown lfd ps ∧ l0own lfd w ps ∧
    (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND ps.b.tbl)) ⇒
    pown lfd ps' ∧ l0own lfd w' ps' ∧ fds_lt w'
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >> strip_tac >>
  ‘∀g. MEM g fs ⇒ g = lfd ∨ MEM g (MAP SND ps.b.tbl)’ by metis_tac[MEM] >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
      Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
      PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
      ‘l0_rely w1’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule_all l0_do_rely >> simp[]) >>
      ‘fds_lt w1’ by (drule_all sys_accept_fds_lt >> simp[]) >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule l0_do_used >> simp[]) >>
      ‘ps.acq = []’ by gvs[wants_input_def] >>
      ‘pown lfd ps1 ∧ l0own lfd w1 ps1 ∧ ps1.b = ps.b’
        suffices_by (strip_tac >> first_x_assum (qspecl_then [‘w1’, ‘ps1’] mp_tac) >> simp[]) >>
      Cases_on ‘l0_res_of out’ >> gvs[]
      >- (drule_all sys_accept_fresh >> strip_tac >>
          drule_all sys_accept_adds >> strip_tac >>
          ‘∀g. g = lfd ∨ MEM g (MAP SND ps.b.tbl) ∨ MEM g ps.b.closing ⇒ g ≠ n2w n’
            by (qpat_x_assum ‘l0own _ _ _’ mp_tac >> simp[l0own_def] >> metis_tac[]) >>
          conj_tac
          >- (qpat_x_assum ‘pown _ _’ mp_tac >> simp[pown_def, inb_of_def] >>
              simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
          qpat_x_assum ‘l0own _ _ _’ mp_tac >> simp[l0own_def] >> metis_tac[]) >>
      IF_CASES_TAC >> gvs[] >>
      qpat_x_assum ‘l0own _ _ _’ mp_tac >> simp[l0own_def] >> metis_tac[]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
  Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_rely w1’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        drule_all l0_do_rely >> simp[]) >>
  ‘l0_used w1 = l0_used w ∧ w1.fd_limit = w.fd_limit’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        imp_res_tac l0_do_env >> drule l0_do_used >> simp[]) >>
  ‘fds_lt w1’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  ‘MEM f (MAP SND ps.b.tbl)’ by metis_tac[] >>
  ‘pown lfd ps1 ∧ l0own lfd w1 ps1 ∧ ps1.b = ps.b’
    suffices_by (strip_tac >> first_x_assum (qspecl_then [‘w1’, ‘ps1’] mp_tac) >> simp[]) >>
  Cases_on ‘l0_res_of out’ >> gvs[AllCaseEqs()] >>
  TRY (Cases_on ‘0 < n’) >> TRY (Cases_on ‘l1_transient e’) >> gvs[] >>
  TRY (conj_tac >- (irule pown_set_inb >> simp[])) >>
  TRY (conj_tac >- (qpat_x_assum ‘pown _ _’ mp_tac >> simp[pown_def, inb_of_def] >>
                    metis_tac[])) >>
  qpat_x_assum ‘l0own _ _ _’ mp_tac >> simp[l0own_def]
QED

(* The tail up to the settling: the poll, the flush, the fetch, the write
   timeout and the reap *)
Theorem pre_settle_eown0:
  l1_polls fess wl = SOME (rv, w1, pevs) ∧
  l1_flush fls (w1, es.p.b) = SOME ((w2, b2), fevs) ∧
  pf_fetch lfd pol fs (w2, es.p with b := b2) = SOME ((w3, ps3f), log, gevs) ∧
  ps3 = stall_step hfs ob log ps3f ∧
  l1_reap ps3f.b.closing (w3, ps3.b) = SOME ((w4, b4), cevs) ∧
  (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND es.p.b.tbl)) ∧
  eown0 lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ⇒
  eown0 lfd (es with p := ps3 with <| b := b4; pause := ps3.pause − 1 |>) ∧
  l0owne lfd w4 (es with p := ps3 with <| b := b4; pause := ps3.pause − 1 |>) ∧
  l0_rely w4 ∧ fds_lt w4 ∧ b4.nxt = es.p.b.nxt ∧ b4.tbl = es.p.b.tbl
Proof
  strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >>
  drule_all l1_flush_l0 >> strip_tac >>
  ‘pown lfd es.p’ by gvs[eown0_def, pown_def] >>
  ‘l0own lfd wl es.p ∧ ∀f. MEM f (MAP SND es.ctbl) ⇒ MEM f (l0_used wl)’
    by gvs[l0owne_def] >>
  qabbrev_tac ‘ps2 = es.p with b := b2’ >>
  ‘pown lfd ps2’ by (simp[Abbr ‘ps2’] >> simp[pown_b]) >>
  ‘l0own lfd w2 ps2’
    by (qpat_x_assum ‘l0own _ wl _’ mp_tac >> simp[Abbr ‘ps2’, l0own_def]) >>
  ‘l0_rely w2 ∧ fds_lt w2’ by gvs[fds_lt_def] >>
  ‘∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND ps2.b.tbl)’ by simp[Abbr ‘ps2’] >>
  drule_all pf_fetch_own >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule_all pf_fetch_quiet >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule_all fetch_acq >> strip_tac >>
  ‘ps3.b.tbl = es.p.b.tbl ∧ ps3.b.nxt = es.p.b.nxt ∧ ps3.b.closing = es.p.b.closing ∧
   ps3.acq = es.p.acq ++ fconns log ∧ pown lfd ps3 ∧ l0own lfd w3 ps3’
    by (qpat_x_assum ‘ps3 = _’ SUBST1_TAC >> simp[] >> gvs[Abbr ‘ps2’]) >>
  qpat_x_assum ‘ps3 = _’ kall_tac >>
  ‘ps3f.b.closing = ps3.b.closing’ by gvs[Abbr ‘ps2’] >>
  qpat_x_assum ‘l1_reap _ _ = _’ mp_tac >> pop_assum SUBST1_TAC >> strip_tac >>
  drule_all l1_reap_l0 >> strip_tac >>
  qabbrev_tac ‘ps4 = ps3 with <| b := b4; pause := ps3.pause − 1 |>’ >>
  ‘pown lfd (ps3 with b := b4)’
    by (irule pown_closing_filter >> simp[] >> metis_tac[]) >>
  ‘pown lfd ps4’
    by (qpat_x_assum ‘pown _ (ps3 with b := b4)’ mp_tac >>
        simp[Abbr ‘ps4’, pown_def, inb_of_def]) >>
  ‘ps4.b = b4 ∧ ps4.acq = es.p.acq ++ fconns log’ by simp[Abbr ‘ps4’] >>
  (* the fds L1 held, and the new ones, against the connect table *)
  ‘ALL_DISTINCT (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl)’
    by gvs[eown0_def] >>
  ‘∀g. MEM g (MAP SND es.ctbl) ⇒
       g ≠ lfd ∧ ¬MEM g (MAP SND es.p.b.tbl) ∧ ¬MEM g es.p.b.closing ∧ ¬MEM g es.p.acq ∧
       ¬MEM g (fconns log)’
    by (gen_tac >> strip_tac >>
        ‘MEM g (l0_used w2)’ by (qpat_x_assum ‘l0_used w1 = _’ SUBST_ALL_TAC >>
                                 qpat_x_assum ‘l0_used w2 = _’ SUBST_ALL_TAC >> res_tac) >>
        qpat_x_assum ‘ALL_DISTINCT _’ mp_tac >> simp[ALL_DISTINCT_APPEND] >>
        metis_tac[]) >>
  rpt conj_tac
  >- (irule eown0_p >> simp[] >> rpt conj_tac
      >- (‘ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl)’ by gvs[eown0_def] >>
          gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
      >> rpt strip_tac >> gvs[MEM_APPEND] >>
      TRY (qpat_x_assum ‘∀g. MEM g b4.closing ⇒ _’ drule >> strip_tac) >>
      metis_tac[])
  >- (simp[l0owne_def, l0own_def] >>
      ‘∀g. MEM g (l0_used w3) ∧ ¬MEM g es.p.b.closing ⇒ MEM g (l0_used w4)’
        by metis_tac[] >>
      ‘∀g. MEM g (MAP SND es.ctbl) ⇒ MEM g (l0_used w3)’
        by (rpt strip_tac >> first_x_assum irule >> gvs[]) >>
      qpat_x_assum ‘l0own _ w3 ps3’ mp_tac >> simp[l0own_def] >> strip_tac >>
      ‘∀g. (g = lfd ∨ MEM g (MAP SND es.p.b.tbl) ∨ MEM g ps3.acq) ⇒ ¬MEM g es.p.b.closing’
        by (qpat_x_assum ‘pown _ ps3’ mp_tac >> simp[pown_def, ALL_DISTINCT_APPEND] >>
            metis_tac[]) >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >- simp[]
  >- (gvs[fds_lt_def] >> metis_tac[])
  >> gvs[]
QED

(* Promotion keeps L1's invariant (ev_settle's, without the world) *)
Theorem eown_promote:
  eown lfd es ∧
  es5.p = es.p ∧ es5.ctbl = es.ctbl ∧ es5.settling = es.settling ∧ es5.early = [] ∧
  es5.shq = es.shq ∧ es5.shut = es.shut ∧
  (∀f. MEM f (MAP SND es.ctbl) ∧ cstat_of es f ≠ CPending ⇒ cstat_of es5 f = cstat_of es f) ⇒
  eown lfd (promote es5)
Proof
  strip_tac >>
  ‘ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl)’ by gvs[eown_def] >>
  ‘ALL_DISTINCT (MAP FST es5.p.b.tbl ++ MAP FST es5.ctbl)’ by gvs[] >>
  qpat_x_assum ‘eown _ _’ mp_tac >>
      simp[eown_def, pown_def, promote_def, inb_of_def] >> strip_tac >>
      gvs[ALL_DISTINCT_APPEND, MEM_FILTER] >> rpt conj_tac >>
      TRY (irule ALL_DISTINCT_MAP_FILTER_gen >> simp[] >> NO_TAC) >>
      TRY (strip_tac >> imp_res_tac MEM_MAP_FILTER_IMP >> gvs[] >> NO_TAC) >>
      rpt strip_tac >> imp_res_tac MEM_MAP_FILTER_IMP >> gvs[] >>
      TRY (qpat_x_assum ‘ALOOKUP (_ ++ _) _ = _’ mp_tac >> simp[ALOOKUP_APPEND] >>
           CASE_TAC >> strip_tac >> gvs[]
           >- (first_x_assum drule >> simp[]) >>
           imp_res_tac ALOOKUP_FILTER_IMP >> gvs[] >>
           qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ (∃i. _) ∧ _’ drule >> simp[] >> NO_TAC) >>
      TRY (imp_res_tac ALOOKUP_FILTER_IMP >> gvs[] >>
           qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ (∃i. _) ∧ _’ drule >> simp[] >> NO_TAC) >>
      TRY (gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> NO_TAC) >>
      TRY (gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
           ‘ALOOKUP es.ctbl e = SOME p_2 ∧ ALOOKUP es.ctbl e = SOME p_2'’
             by (conj_tac >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >> gvs[] >> NO_TAC) >>
      imp_res_tac ALOOKUP_FILTER_IMP >> gvs[cstat_of_def] >>
      TRY (qpat_x_assum ‘ALOOKUP (_ ++ _) _ = _’
             (strip_assume_tac o SIMP_RULE (srw_ss()) [ALOOKUP_APPEND, AllCaseEqs()]) >>
           imp_res_tac ALOOKUP_FILTER_IMP >> res_tac >> fs[] >> NO_TAC) >>
      Cases_on ‘ALOOKUP es5.cst f’ >> gvs[ALOOKUP_FILTER_NONE] >>
      ‘ALOOKUP (FILTER (λ(f, c). c ≠ CUp) es5.cst) f = SOME x’
        by (irule ALOOKUP_FILTER_SOME >> fs[]) >> gvs[]
QED

Theorem eown0_promote:
  eown0 lfd es ∧
  es5.p = es.p ∧ es5.ctbl = es.ctbl ∧ es5.settling = es.settling ∧ es5.early = [] ∧
  (∀f. MEM f (MAP SND es.ctbl) ∧ cstat_of es f ≠ CPending ⇒ cstat_of es5 f = cstat_of es f) ⇒
  eown0 lfd (promote es5)
Proof
  strip_tac >> simp[eown0_proj] >>
  ‘promote es5 with <| shq := []; shut := [] |> =
   promote (es5 with <| shq := []; shut := [] |>)’ by simp[promote_def, cstat_of_def, honestL1EPModelTheory.l1e_component_equality] >>
  pop_assum SUBST1_TAC >> irule eown_promote >>
  simp[] >> qexists_tac ‘es with <| shq := []; shut := [] |>’ >>
  gvs[eown0_proj, cstat_of_def]
QED

Theorem etail_eown0:
  etail lfd pol ifs (wl, es) = SOME (rdy, (wl', es'), log, tevs) ∧
  eown0 lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ⇒
  eown0 lfd es' ∧ l0owne lfd wl' es' ∧ l0_rely wl' ∧ fds_lt wl'
Proof
  simp[etail_def] >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol es.p ifs ++ MAP (λf. (f, 2n)) (pend_fds es)’ >>
  gvs[AllCaseEqs()] >>
  rename1 ‘l1_polls _ wl = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3f), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  rename1 ‘settle_fds _ _ = SOME ((w5, es5), sevs)’ >>
  ‘∀f. MEM f (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv)) ⇒
       f = lfd ∨ MEM f (MAP SND es.p.b.tbl)’
    by (rw[MEM_FILTER, Abbr ‘fes’, in_fds_pend] >> drule in_fds_poll_set >> simp[]) >>
  ‘stall_step (pf_held ps3f) (outbox_of es.p.b) log ps3f =
   stall_step (pf_held ps3f) (outbox_of es.p.b) log ps3f’ by REWRITE_TAC [] >>
  drule_all pre_settle_eown0 >> strip_tac >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3f) (outbox_of es.p.b) log ps3f’ >>
  ‘ps3.pause = ps3f.pause’ by simp[Abbr ‘ps3’] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qabbrev_tac ‘es4 = es with p := ps3 with <|b := b4; pause := ps3f.pause − 1|>’ >>
  qpat_x_assum ‘settle_fds _ _ = _’ assume_tac >>
  drule_all settle_fds_props >> simp[] >> strip_tac >>
  ‘∀f. MEM f (MAP SND es4.ctbl) ∧ cstat_of es4 f ≠ CPending ⇒ cstat_of es5 f = cstat_of es4 f’
    by (rpt strip_tac >>
        ‘cstat_of es4 f = cstat_of es f’ by simp[Abbr ‘es4’, cstat_of_def] >>
        ‘¬MEM f (pend_fds es)’
          by (simp[pend_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[Abbr ‘es4’]) >>
        ‘ALOOKUP es4.early f = NONE’
          by (simp[ALOOKUP_NONE] >> strip_tac >>
              qpat_assum ‘eown0 _ es4’
                (mp_tac o el 5 o CONJUNCTS o REWRITE_RULE [eown0_def]) >>
              disch_then drule >> simp[]) >>
        qpat_x_assum ‘∀f. cstat_of es5 f = _ ∨ _’ (qspec_then ‘f’ strip_assume_tac) >>
        gvs[MEM_FILTER, cstat_of_apply_early, Abbr ‘es4’]) >>
  ‘eown0 lfd (promote es5)’ by (irule eown0_promote >> simp[] >> qexists_tac ‘es4’ >> simp[]) >>
  rpt conj_tac
  >- (irule eown0_settling_sub >> simp[MEM_FILTER])
  >- (qpat_x_assum ‘l0owne _ w4 _’ assume_tac >>
      drule_at (Pos hd) l0owne_promote >> disch_then irule >> simp[])
  >> gvs[fds_lt_def]
QED

(* ------------------------------------------------------------------------
   The queued shutdowns
   ------------------------------------------------------------------------ *)

Theorem used_chans_hist[local]:
  l0_used (w with chans := c) = l0_used w ∧
  l0_used (w with <| chans := c; hist := h |>) = l0_used w ∧
  (w with <| chans := c; hist := h |>).fd_limit = w.fd_limit ∧
  l0_used (w with hist := h) = l0_used w ∧ (w with hist := h).fd_limit = w.fd_limit
Proof
  simp[l0_used_def]
QED

Theorem sys_shutdown_l0:
  sys_shutdown f w = SOME (out, w', ev) ∧ l0_rely w ⇒
  l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧ l0_rely w'
Proof
  strip_tac >>
  ‘l0_rely w'’ by (gvs[sys_shutdown_def] >> drule_all l0_do_rely >> simp[]) >>
  gvs[sys_shutdown_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, l0_shutdown_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  every_case_tac >> gvs[fail_def, not_chan_def, upd_lchan_def, used_chans_hist]
QED

Theorem pf_shuts_fields:
  ∀fs w ps w' ps' kp sh evs.
    pf_shuts fs (w, ps) = SOME ((w', ps'), kp, sh, evs) ∧ l0_rely w ⇒
    l0_rely w' ∧ l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧
    ps'.b.tbl = ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ∧ ps'.b.closing = ps.b.closing ∧
    ps'.acq = ps.acq ∧ ps'.inb = ps.inb ∧ ps'.eof = ps.eof
Proof
  Induct >- simp[pf_shuts_def] >>
  rpt gen_tac >> rename1 ‘kf :: fs’ >> PairCases_on ‘kf’ >> rename1 ‘(k, f) :: fs’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on ‘sys_shutdown f w’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  rename1 ‘sys_shutdown _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> PairCases_on ‘z’ >> gvs[] >>
  drule_all sys_shutdown_l0 >> strip_tac >>
  ‘ps1.b.tbl = ps.b.tbl ∧ ps1.b.nxt = ps.b.nxt ∧ ps1.b.closing = ps.b.closing ∧
   ps1.acq = ps.acq ∧ ps1.inb = ps.inb ∧ ps1.eof = ps.eof’
    by (Cases_on ‘l0_res_of out’ >> gvs[] >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >>
        simp[drop_out_def, set_outbox_def]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem eshuts_eown0:
  eshuts (wl, es) = SOME ((wl', es'), evs) ∧
  eown0 lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ⇒
  eown0 lfd es' ∧ l0owne lfd wl' es' ∧ l0_rely wl' ∧ fds_lt wl'
Proof
  simp[eshuts_def] >> strip_tac >> pairarg_tac >> gvs[] >>
  rename1 ‘pf_shuts _ _ = SOME ((wl', ps'), kp, sh, evs)’ >>
  drule_all pf_shuts_fields >> strip_tac >>
  ‘pown lfd ps' ⇔ pown lfd es.p’ by simp[pown_def, inb_of_def] >>
  ‘fds_lt wl'’ by gvs[fds_lt_def] >>
  qpat_x_assum ‘eown0 _ _’ mp_tac >> qpat_x_assum ‘l0owne _ _ _’ mp_tac >>
  simp[eown0_def, l0owne_def, l0own_def, cstat_of_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   MAIN: a round, and every run from the initial state, keep L1's
   invariant, its fds open in L0, L0's rely and the fd bound
   ------------------------------------------------------------------------ *)

Theorem eround_eown0:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
  eown0 lfd es ∧ l0owne lfd w es ∧ l0_rely w ∧ fds_lt w ⇒
  eown0 lfd es' ∧ l0owne lfd w' es' ∧ l0_rely w' ∧ fds_lt w'
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  drule_all eacts_eown0 >> strip_tac >>
  drule_all etail_eown0 >> strip_tac >>
  drule_all eshuts_eown0 >> simp[]
QED

Theorem eown0_einit:
  MEM lfd (l0_used w) ⇒ eown0 lfd einit ∧ l0owne lfd w einit
Proof
  simp[einit_def, eown0_def, l0owne_def, l0own_def, pown_def, pinit_def, inb_of_def, l1init_def] >>
  metis_tac[]
QED

Theorem eown_run:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    eown0 lfd (SND ws) ∧ l0owne lfd (FST ws) (SND ws) ∧ l0_rely (FST ws) ∧ fds_lt (FST ws)
Proof
  strip_tac >> Induct >> simp[erounds_def]
  >- (rpt gen_tac >> strip_tac >> gvs[] >> drule eown0_einit >> simp[]) >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘eround _ _ _ ws1 _ = SOME (_, ws2, _, _)’ >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >> gvs[] >>
  drule_all eround_eown0 >> simp[]
QED
