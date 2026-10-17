(*
  E1's round never fails (as honestL1PFInv for the prefetching L1): every fd
  it holds stays below 2^31, and so each round is total, given what a
  computation must not do (eact_ok): Accept only on the listener, connect
  only to a port (< 2^16), well-formed reads, no write on a connect handle
  whose connect is pending, and no handle overflow.  The write condition is
  on the state the write is done in; etail_rdy_ctbl is what lets a
  computation know it: a connect handle reported ready has settled refused
  (one that came up has left the connect table).
*)
Theory honestL1EPTotal
Ancestors
  honestL1EPRefine honestL1EPModel honestL1PFClose honestL1PFInv honestL1PFRefine honestL1Inv
  honestL1PFModel honestL1Model endpointHLModel honestL0Rely honestL0World honestL0
  alist
Libs
  preamble

(* The fds E1 holds are small *)
Definition esmall_def:
  esmall lfd es ⇔ psmall lfd es.p ∧ EVERY small (MAP SND es.ctbl)
End

(* What a computation must not do, in the state es the action is done in *)
Definition eact_ok_def:
  eact_ok lfd es (EAccept l) = (l = lfd) ∧
  eact_ok lfd es (EConnect p) = (p < 65536) ∧
  eact_ok lfd es (ERead h n) = (0 < n ∧ n < 256 ** 8) ∧
  eact_ok lfd es (EWrite h bs) =
    (∀f. ALOOKUP es.ctbl h = SOME f ⇒ cstat_of es f = CRefused) ∧
  eact_ok lfd es (ELevel h) = T ∧
  eact_ok lfd es (EClose h) = (h ≠ lfd) ∧
  eact_ok lfd es (EShut h) = (h ≠ lfd)
End

(* The actions that may take a handle *)
Definition nhdls_def:
  nhdls [] = 0n ∧
  nhdls (EAccept l :: acts) = nhdls acts + 1 ∧
  nhdls (EConnect p :: acts) = nhdls acts + 1 ∧
  nhdls (ERead h n :: acts) = nhdls acts ∧
  nhdls (EWrite h bs :: acts) = nhdls acts ∧
  nhdls (ELevel h :: acts) = nhdls acts ∧
  nhdls (EClose h :: acts) = nhdls acts ∧
  nhdls (EShut h :: acts) = nhdls acts
End

Theorem nhdls_cons:
  nhdls (a :: acts) = nhdls [a] + nhdls acts
Proof
  Cases_on ‘a’ >> simp[nhdls_def]
QED

(* ------------------------------------------------------------------------
   The connect calls
   ------------------------------------------------------------------------ *)

(* connect's value (the new fd, or 0) is below 2^31 *)
Theorem l0_connect_val:
  l0_rely w ∧ l0_connect p w = (r, v, w') ⇒ v < 2147483648 ∧ ∀x. r = Ok x ⇒ x = v
Proof
  rw[l0_connect_def, l0_alloc_def, AllCaseEqs()] >> gvs[fail_def, l0_rely_def]
QED

Theorem sys_connect_ok:
  l0_rely w ⇒
  ∃out w' ev. sys_connect p w = SOME (out, w', ev) ∧ l0_rely w' ∧ res_val out < 2147483648
Proof
  rw[sys_connect_def] >>
  ‘l0_rely (l0_tick «sys_connect» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qabbrev_tac ‘tw = l0_tick «sys_connect» w’ >>
  ‘∃out w1. l0_call «sys_connect» (port_bytes p) (REPLICATE 13 0w) tw = SOME (FFIreturn out w1) ∧
            res_val out < 2147483648’
    by (simp[l0_call_def, l0_hdr_def, port_bytes_def] >>
        qmatch_goalsub_abbrev_tac ‘l0_connect pp tw’ >>
        ‘∃r v w'. l0_connect pp tw = (r, v, w')’ by metis_tac[pairTheory.PAIR] >>
        drule_all l0_connect_val >> strip_tac >>
        Cases_on ‘r’ >> gvs[res_val_enc]) >>
  qunabbrev_tac ‘tw’ >> drule_all l0_do_SOME >> strip_tac >> simp[]
QED

Theorem sys_connerr_ok:
  l0_rely w ∧ small f ⇒ ∃out w' ev. sys_connerr f w = SOME (out, w', ev) ∧ l0_rely w'
Proof
  rw[small_def, sys_connerr_def] >>
  ‘l0_rely (l0_tick «sys_connerr» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘∃out w1. l0_call «sys_connerr» (fd_bytes f) (REPLICATE 13 0w)
              (l0_tick «sys_connerr» w) = SOME (FFIreturn out w1)’
    by (simp[l0_call_def, l0_hdr_def, fd_ok_def] >> every_case_tac >> simp[]) >>
  drule_all l0_do_SOME >> strip_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The actions
   ------------------------------------------------------------------------ *)

Theorem esmall_p:
  esmall lfd es ∧ psmall lfd ps' ⇒ esmall lfd (es with p := ps')
Proof
  simp[esmall_def]
QED

Theorem small_ctbl_lookup:
  EVERY small (MAP SND l) ∧ ALOOKUP l h = SOME f ⇒ small f
Proof
  rw[EVERY_MEM] >> first_x_assum irule >> imp_res_tac ALOOKUP_MEM >>
  simp[MEM_MAP] >> qexists_tac ‘(h, f)’ >> simp[]
QED

Theorem edo_ok:
  l0_rely w ∧ esmall lfd es ∧ eact_ok lfd es a ∧ es.p.b.nxt + nhdls [a] < dimword (:64) ⇒
  ∃r w' es' evs. edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ l0_rely w' ∧
                 esmall lfd es' ∧ es'.p.b.nxt ≤ es.p.b.nxt + nhdls [a]
Proof
  Cases_on ‘a’ >> simp[eact_ok_def, nhdls_def] >> strip_tac >| [
    (* EAccept *)
    ‘psmall lfd es.p’ by gvs[esmall_def] >>
    ‘pact_ok lfd (Accept lfd) ∧ es.p.b.nxt + naccepts [Accept lfd] < dimword (:64)’
      by simp[pact_ok_def, act_ok_def] >>
    drule_all pdo_ok >> strip_tac >> gvs[edo_def, esmall_def],
    (* ERead *)
    rename1 ‘ERead h n’ >> simp[edo_def] >> Cases_on ‘ALOOKUP es.ctbl h’ >> simp[]
    >- (IF_CASES_TAC >- simp[] >>   (* EOF: kept *)
        ‘psmall lfd es.p ∧ pact_ok lfd (Read h n) ∧ es.p.b.nxt + naccepts [Read h n] < dimword (:64)’
          by gvs[esmall_def, pact_ok_def, act_ok_def] >>
        drule_all pdo_ok >> strip_tac >> gvs[esmall_def, naccepts_def]) >>
    rename1 ‘ALOOKUP _ h = SOME f’ >> IF_CASES_TAC >> simp[] >>
    ‘small f’ by (gvs[esmall_def] >> metis_tac[small_ctbl_lookup]) >>
    ‘small_fds lfd es.p.b’ by gvs[esmall_def, psmall_def] >>
    drule_all l1_close_ok >> strip_tac >> simp[] >>
    drule_all l1_close_l0 >> strip_tac >>
    gvs[esmall_def, ec_del_def, psmall_def, EVERY_MEM] >> metis_tac[MEM_SND_ADELKEY_sub],
    (* EWrite *)
    rename1 ‘EWrite h bs’ >> simp[edo_def] >> Cases_on ‘ALOOKUP es.ctbl h’ >> gvs[] >>
    ‘psmall lfd es.p ∧ pact_ok lfd (Write h bs) ∧ es.p.b.nxt + naccepts [Write h bs] < dimword (:64)’
      by gvs[esmall_def, pact_ok_def, act_ok_def] >>
    drule_all pdo_ok >> strip_tac >> IF_CASES_TAC >> gvs[esmall_def],
    (* EConnect *)
    rename1 ‘EConnect p’ >> simp[edo_def] >>
    drule sys_connect_ok >> disch_then (qspec_then ‘p’ strip_assume_tac) >> simp[] >>
    IF_CASES_TAC >> simp[] >>
    ‘small (n2w (res_val out) : word64)’ by simp[small_def] >>
    IF_CASES_TAC
    >- ((* (A): the new socket closed at once *)
        drule_all sys_close_ok >> strip_tac >> simp[]) >>
    simp[] >>
    ‘l1hdln (w2n lfd) es.p.b.nxt < dimword (:64)’ by simp[l1hdln_lt] >> simp[] >>
    ‘small (n2w (res_val out) : word64)’ by simp[small_def] >>
    gvs[esmall_def, psmall_def, small_fds_def],
    (* ELevel *)
    simp[edo_def],
    (* EClose *)
    rename1 ‘EClose h’ >> simp[edo_def] >> Cases_on ‘ALOOKUP es.ctbl h’ >> simp[]
    >- (Cases_on ‘ALOOKUP es.p.b.tbl h’ >> simp[] >>
        rename1 ‘ALOOKUP _ h = SOME f’ >>
        ‘psmall lfd es.p’ by gvs[esmall_def] >>
        ‘small f’ by (gvs[psmall_def] >> metis_tac[small_tbl_lookup]) >>
        qabbrev_tac ‘ps = pf_release h f (set_inb f [] es.p)’ >>
        ‘psmall lfd ps ∧ ps.b.nxt = es.p.b.nxt’
          by simp[Abbr ‘ps’, psmall_release, psmall_set_inb, pf_release_def, set_inb_def] >>
        simp[pf_close_def] >> IF_CASES_TAC >> simp[]
        >- (‘small_fds lfd ps.b’ by gvs[psmall_def] >>
            drule_all l1_close_ok >> strip_tac >> simp[] >>
            ‘st' = forget f ps.b’ by gvs[l1_close_def, AllCaseEqs()] >>
            gvs[esmall_def, psmall_def, forget_def, set_outbox_def]) >>
        gvs[esmall_def, psmall_def, small_fds_def]) >>
    rename1 ‘ALOOKUP _ h = SOME f’ >>
    ‘small f’ by (gvs[esmall_def] >> metis_tac[small_ctbl_lookup]) >>
    ‘small_fds lfd es.p.b’ by gvs[esmall_def, psmall_def] >>
    drule_all l1_close_ok >> strip_tac >> simp[] >>
    drule_all l1_close_l0 >> strip_tac >>
    gvs[esmall_def, ec_del_def, psmall_def, EVERY_MEM] >> metis_tac[MEM_SND_ADELKEY_sub],
    (* EShut *)
    simp[edo_def] >> rw[] >> every_case_tac >> gvs[esmall_def]]
QED

(* The round's actions, given the condition in the state each is done in *)
Theorem eacts_ok:
  ∀acts w es.
    l0_rely w ∧ esmall lfd es ∧ es.p.b.nxt + nhdls acts < dimword (:64) ∧
    (∀i rs0 evs0 wi esi.
       i < LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
       eact_ok lfd esi (EL i acts)) ⇒
    ∃rs evs w' es'. eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧
                    l0_rely w' ∧ esmall lfd es' ∧ es'.p.b.nxt ≤ es.p.b.nxt + nhdls acts
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >> rename1 ‘a :: acts’ >>
  ‘nhdls (a :: acts) = nhdls [a] + nhdls acts’ by simp[Once nhdls_cons] >>
  ‘eact_ok lfd es a’
    by (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[eacts_def]) >>
  ‘es.p.b.nxt + nhdls [a] < dimword (:64)’ by gvs[] >>
  drule_all edo_ok >> disch_then (qspec_then ‘pol’ strip_assume_tac) >> simp[] >>
  first_x_assum (qspecl_then [‘w'’, ‘es'’] mp_tac) >> impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, (gvs[] >> NO_TAC),
             (rpt strip_tac >>
              qpat_x_assum ‘∀i rs0 evs0 wi esi. i < SUC _ ∧ _ ⇒ _’ (qspec_then ‘SUC i’ mp_tac) >>
              qpat_x_assum ‘edo _ _ _ _ = _’ (fn th => simp[eacts_def, th]))]) >>
  strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The round's tail
   ------------------------------------------------------------------------ *)

Theorem settle_fds_ok:
  ∀fs w es. l0_rely w ∧ EVERY small fs ⇒
            ∃w' es' evs. settle_fds fs (w, es) = SOME ((w', es'), evs)
Proof
  Induct >> simp[settle_fds_def] >> rpt strip_tac >>
  drule_all sys_connerr_ok >> strip_tac >> simp[] >>
  ‘∀es. ∃w'' es'' evs. settle_fds fs (w', es) = SOME ((w'', es''), evs)’ by metis_tac[] >>
  qmatch_goalsub_abbrev_tac ‘settle_fds fs (w', es1)’ >>
  first_x_assum (qspec_then ‘es1’ strip_assume_tac) >> simp[]
QED

Theorem pend_fds_small:
  esmall lfd es ⇒ EVERY small (pend_fds es)
Proof
  rw[esmall_def, pend_fds_def, EVERY_MEM, MEM_MAP, MEM_FILTER] >>
  first_x_assum irule >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem esmall_promote:
  esmall lfd es ⇒ esmall lfd (promote es)
Proof
  rw[esmall_def, psmall_def, small_fds_def, promote_def, EVERY_MEM, MEM_MAP, MEM_FILTER] >>
  gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem etail_ok:
  l0_rely w ∧ esmall lfd es ⇒
  ∃rdy w' es' log evs. etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ∧
                       l0_rely w' ∧ esmall lfd es' ∧ es'.p.b.nxt = es.p.b.nxt
Proof
  strip_tac >> simp[etail_def] >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol es.p hs ++ MAP (λf. (f, 2n)) (pend_fds es)’ >>
  ‘psmall lfd es.p’ by gvs[esmall_def] >>
  ‘EVERY (EVERY (λ(f, e). small f ∧ e < 4)) [fes]’
    by (simp[Abbr ‘fes’] >> conj_tac >- (irule pf_poll_set_small >> simp[]) >>
        drule pend_fds_small >> simp[EVERY_MAP, EVERY_MEM]) >>
  drule_all l1_polls_ok >> strip_tac >> simp[] >>
  rename1 ‘l1_polls _ _ = SOME (rv, w1, pevs)’ >>
  drule readable_small >> strip_tac >>
  ‘small_fds lfd es.p.b’ by gvs[psmall_def] >>
  qspecl_then [‘writable_fds rv’, ‘w1’, ‘es.p.b’] mp_tac l1_flush_ok >> simp[] >> strip_tac >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >> simp[] >>
  ‘psmall lfd (es.p with b := b2)’ by gvs[psmall_def] >>
  ‘EVERY small (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))’
    by gvs[EVERY_MEM, MEM_FILTER] >>
  drule_all pf_fetch_ok >> disch_then (qspec_then ‘pol’ strip_assume_tac) >> simp[] >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log, gevs)’ >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3'’ >>
  ‘psmall lfd ps3 ∧ ps3.b.nxt = ps3'.b.nxt’ by simp[Abbr ‘ps3’, psmall_stall] >>
  ‘small_fds lfd ps3.b ∧ EVERY small ps3'.b.closing’ by gvs[psmall_def, small_fds_def] >>
  qspecl_then [‘ps3'.b.closing’, ‘w3’, ‘ps3.b’] mp_tac l1_reap_ok >> simp[] >> strip_tac >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘settle_fds rp (w4, apply_early es4)’ >>
  ‘EVERY small rp’
    by (drule pend_fds_small >> simp[Abbr ‘rp’, EVERY_MEM, MEM_FILTER]) >>
  drule_all settle_fds_ok >> disch_then (qspec_then ‘apply_early es4’ strip_assume_tac) >>
  simp[] >>
  drule_all settle_fds_props >> strip_tac >>
  ‘esmall lfd es4’ by gvs[Abbr ‘es4’, esmall_def, psmall_def] >>
  ‘esmall lfd es'’ by gvs[esmall_def] >>
  drule esmall_promote >> strip_tac >>
  ‘(promote es').p.b.nxt = b4.nxt’
    by (qpat_x_assum ‘es'.p = _’ mp_tac >> simp[promote_def, apply_early_def, Abbr ‘es4’]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qpat_x_assum ‘esmall lfd (promote es')’ mp_tac >> simp[esmall_def])
  >> qpat_x_assum ‘(promote es').p.b.nxt = _’ SUBST1_TAC >> first_assum ACCEPT_TAC
QED

(* A connect handle reported ready has settled refused *)
Theorem etail_rdy_ctbl:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ∧
  MEM h rdy ∧ ALOOKUP es'.ctbl h = SOME f ⇒ cstat_of es' f = CRefused
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> gvs[MEM_FILTER] >>
  qmatch_asmsub_abbrev_tac ‘ALOOKUP (promote es5).ctbl h = SOME f’ >>
  ‘cstat_of (promote es5) f ≠ CUp’
    by (simp[cstat_of_def, promote_def] >> CASE_TAC >> simp[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_FILTER]) >>
  gvs[] >> Cases_on ‘cstat_of (promote es5) f’ >> gvs[] >> gvs[cstat_of_def]
QED

(* ------------------------------------------------------------------------
   The round
   ------------------------------------------------------------------------ *)

Theorem eround_ok:
  l0_rely w ∧ esmall lfd es ∧ es.p.b.nxt + nhdls acts < dimword (:64) ∧
  (∀i rs0 evs0 wi esi.
     i < LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
     eact_ok lfd esi (EL i acts)) ⇒
  ∃snap w' es' log evs. eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
                        l0_rely w' ∧ esmall lfd es' ∧ es'.p.b.nxt ≤ es.p.b.nxt + nhdls acts
Proof
  strip_tac >> simp[eround_def] >>
  drule_all eacts_ok >> strip_tac >> simp[] >>
  drule_all etail_ok >> disch_then (qspecl_then [‘pol’, ‘hs’] strip_assume_tac) >> simp[] >>
  simp[eshuts_def] >>
  ‘psmall lfd es''.p’ by gvs[esmall_def] >>
  qmatch_goalsub_abbrev_tac ‘pf_shuts qs (w'', es''.p)’ >>
  qspecl_then [‘qs’, ‘w''’, ‘es''.p’] mp_tac pf_shuts_ok >> simp[] >> strip_tac >> simp[] >>
  gvs[esmall_def]
QED

Theorem esmall_einit:
  small lfd ⇒ esmall lfd einit
Proof
  simp[esmall_def, einit_def, psmall_def, small_fds_def, pinit_def, l1init_def]
QED
