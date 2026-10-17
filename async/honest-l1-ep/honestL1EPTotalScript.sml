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
  honestL1EPRefine honestL1EPModel honestL1PFInv honestL1PFRefine honestL1Inv
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
  eact_ok lfd es (ELevel h) = T
End

(* The actions that may take a handle *)
Definition nhdls_def:
  nhdls [] = 0n ∧
  nhdls (EAccept l :: acts) = nhdls acts + 1 ∧
  nhdls (EConnect p :: acts) = nhdls acts + 1 ∧
  nhdls (ERead h n :: acts) = nhdls acts ∧
  nhdls (EWrite h bs :: acts) = nhdls acts ∧
  nhdls (ELevel h :: acts) = nhdls acts
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
    >- (‘psmall lfd es.p ∧ pact_ok lfd (Read h n) ∧ es.p.b.nxt + naccepts [Read h n] < dimword (:64)’
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
    drule_all pdo_ok >> strip_tac >> gvs[esmall_def],
    (* EConnect *)
    rename1 ‘EConnect p’ >> simp[edo_def] >>
    drule sys_connect_ok >> disch_then (qspec_then ‘p’ strip_assume_tac) >> simp[] >>
    IF_CASES_TAC >> simp[] >>
    ‘l1hdln (w2n lfd) es.p.b.nxt < dimword (:64)’ by simp[l1hdln_lt] >> simp[] >>
    ‘small (n2w (res_val out) : word64)’ by simp[small_def] >>
    gvs[esmall_def, psmall_def, small_fds_def],
    (* ELevel *)
    simp[edo_def]]
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
  drule_all etail_ok >> disch_then (qspecl_then [‘pol’, ‘hs’] strip_assume_tac) >> simp[]
QED

Theorem esmall_einit:
  small lfd ⇒ esmall lfd einit
Proof
  simp[esmall_def, einit_def, psmall_def, small_fds_def, pinit_def, l1init_def]
QED

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
