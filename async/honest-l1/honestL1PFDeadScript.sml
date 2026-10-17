(*
  After L1 closes an fd f (with channel c), what the kernel took on c no
  longer changes: c is unused (the close went through) or still f's (an
  interrupted close kept it, POSIX close EINTR), and L1 never sends on an
  fd it no longer holds.  With this, the round lemma of honestL1PFOut is
  sharpened (tkx): an fd L1 closes in a round with nothing left to send
  had everything it was given taken by the kernel, unless L1 dropped its
  output (a send on it failed hard, or the write timeout dropped it, D23).
*)
Theory honestL1PFDead
Ancestors
  honestL1PFFlushLive honestL1PFFlush honestL1PFOut honestL0WorldProps honestL1PFRound
  honestL1PFRefine honestL1PFInv honestL1PFModel honestL1Steps honestL1Inv honestL1Props
  honestL1Model honestL0WorldInv honestL0Rely honestL0World honestL0 socketV2FFI
  asyncHLModel asyncCore Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   A closed fd's channel
   ------------------------------------------------------------------------ *)

(* f's channel c, with sent sb: unused, or still f's *)
Definition dinv_def:
  dinv f c sb w ⇔ uchan c sb w ∨ (l0_chan_of w f = SOME c ∧ csent w c = sb)
End

Theorem close_fd_uchan:
  l0wf w ∧ l0_chan_of w f = SOME c ⇒ uchan c (csent w c) (close_fd f w)
Proof
  rw[close_fd_def, uchan_def] >> gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘MEM (f, c) w.open_fds’ by metis_tac[ALOOKUP_MEM] >>
  ‘ALL_DISTINCT (MAP SND w.open_fds) ∧
   ∀x. MEM x (MAP SND w.open_fds) ⇒ ¬MEM x (FLAT (MAP (SND o SND) w.listeners))’
    by gvs[l0wf_def, used_chans_def, ALL_DISTINCT_APPEND] >>
  simp[upd_lchan_def, used_chans_def, csent_def, EL_LUPDATE, MEM_MAP, MEM_FLAT,
       FORALL_PROD] >>
  rw[]
  >- (CCONTR_TAC >> gvs[] >> metis_tac[distinct_snd])
  >> CCONTR_TAC >> gvs[MEM_MAP, MEM_FLAT] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> simp[MEM_MAP, MEM_FLAT] >>
  conj_tac >- (qexists_tac ‘(f, c)’ >> simp[]) >>
  qexists_tac ‘l’ >> simp[] >> qexists_tac ‘(p_1, p_1', l)’ >> simp[]
QED

Theorem sys_close_dinv:
  winv w ∧ l0_chan_of w f = SOME c ∧ sys_close f w = SOME (out, w', ev) ⇒
  dinv f c (csent w c) w'
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0_chan_of (l0_tick «sys_close» w) f = SOME c ∧
   csent (l0_tick «sys_close» w) c = csent w c ∧ l0wf (l0_tick «sys_close» w)’
    by (‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
        ‘c < LENGTH (l0_tick «sys_close» w).chans ∧
         csent (l0_tick «sys_close» w) c = csent w c’ by metis_tac[csent_tick] >>
        gvs[l0_chan_of_def, winv_def, l0wf_tick, AllCaseEqs()]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def, fd_bytes_lfd] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  gvs[l0_close_def, AllCaseEqs(), fail_def, dinv_def] >>
  TRY (disj1_tac >> drule_all close_fd_uchan >>
       simp[uchan_def, used_chans_def, csent_def] >> NO_TAC) >>
  disj2_tac >> gvs[l0_chan_of_def, csent_def]
QED

Theorem sys_dinv:
  winv w ∧ dinv f c sb w ⇒
  (sys_recv g k w = SOME (out, w', ev) ⇒ dinv f c sb w') ∧
  (sys_accept g w = SOME (out, w', ev) ⇒ dinv f c sb w') ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ dinv f c sb w') ∧
  (sys_send g bs w = SOME (out, w', ev) ∧ g ≠ f ⇒ dinv f c sb w') ∧
  (sys_close g w = SOME (out, w', ev) ⇒ dinv f c sb w')
Proof
  strip_tac >> qpat_x_assum ‘dinv _ _ _ _’ mp_tac >> simp[dinv_def] >> strip_tac
  >- (‘wpres (uchan c sb)’ by simp[wpres_uchan] >>
      drule_all sys_wpres >> strip_tac >> rpt conj_tac >> rpt strip_tac >>
      disj1_tac >> metis_tac[]) >>
  rpt conj_tac >> rpt strip_tac
  >- (disj2_tac >> drule_all (cj 2 sys_csents) >> simp[])
  >- (disj2_tac >> drule_all (cj 3 sys_csents) >> simp[])
  >- (disj2_tac >> drule_all (cj 1 sys_csents) >> simp[])
  >- (disj2_tac >> drule_all sys_send_csent >> simp[])
  >> Cases_on ‘g = f’ >> gvs[]
  >- (drule_all sys_close_dinv >> simp[dinv_def])
  >> disj2_tac >> drule_all (cj 4 sys_csents) >> simp[]
QED

Theorem l1_close_dinv:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ dinv f c sb w ⇒ dinv f c sb w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> metis_tac[sys_dinv]
QED

Theorem l1_polls_dinv:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ dinv f c sb w ⇒
    dinv f c sb w'
Proof
  Induct >> simp[l1_polls_def] >> rw[AllCaseEqs()] >> metis_tac[sys_dinv, sys_winv]
QED

(* The flush leaves an fd with nothing to send (or gone) alone *)
Theorem l1_flush_dinv:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧
    dinv f c sb w ∧ (outbox_of b f = [] ∨ MEM f b.gone) ⇒
    dinv f c sb w' ∧ evs_sent f evs = []
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac >>
  TRY (first_x_assum (qspecl_then [‘w’, ‘b’] mp_tac) >> simp[] >> metis_tac[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >>
  ‘h ≠ f’ by (strip_tac >> gvs[]) >>
  ‘dinv f c sb w''’ by metis_tac[sys_dinv] >>
  ‘winv w''’ by metis_tac[sys_winv] >>
  drule_all sys_send_other >> strip_tac >>
  first_x_assum (qspecl_then [‘w''’, ‘after_send h (l0_res_of out) b’] mp_tac) >>
  simp[outbox_of_after_send_other] >> disch_then irule >>
  gvs[after_send_def] >> every_case_tac >> gvs[MEM_FILTER]
QED

Theorem pf_fetch_dinv:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ dinv f c sb w ⇒
    dinv f c sb w'
Proof
  Induct >> simp[pf_fetch_def] >> rw[AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[AllCaseEqs()]) >> metis_tac[sys_dinv, sys_winv]
QED

Theorem l1_reap_dinv:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ dinv f c sb w ⇒ dinv f c sb w'
Proof
  Induct >> simp[l1_reap_def] >> rw[AllCaseEqs()] >>
  TRY (Cases_on ‘ws’) >> metis_tac[l1_close_dinv, l1_close_winv]
QED

(* An action on others leaves f's channel alone *)
Theorem pdo_dinv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧
  dinv f c sb w ∧ ¬MEM f (MAP SND ps.b.tbl) ⇒
  dinv f c sb w'
Proof
  strip_tac >> qpat_x_assum ‘dinv _ _ _ _’ mp_tac >> simp[dinv_def] >> strip_tac
  >- (disj1_tac >> irule pdo_wpres >> simp[wpres_uchan] >> metis_tac[])
  >> disj2_tac >> drule_all pdo_chan >> simp[]
QED

(* ------------------------------------------------------------------------
   Where gone comes from: a send that failed hard
   ------------------------------------------------------------------------ *)

(* The event's call failed *)
Definition ev_failed_def:
  ev_failed (IO_event n conf bs) ⇔ ∃e x. l0_res_of (MAP SND bs) = Fail e x
End

(* A send on f in evs failed with an error L1 does not retry (D19 (a), D16) *)
Definition hard_send_def:
  hard_send f evs ⇔ ∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev ∧ ev_failed ev
End

Theorem hard_send_simps[simp]:
  (hard_send f [] ⇔ F) ∧
  (hard_send f (evs1 ++ evs2) ⇔ hard_send f evs1 ∨ hard_send f evs2)
Proof
  simp[hard_send_def] >> metis_tac[]
QED

(* Not a simp rule: [ev] is itself a cons *)
Theorem hard_send_cons:
  hard_send f (ev :: evs) ⇔ hard_send f [ev] ∨ hard_send f evs
Proof
  simp[hard_send_def] >> metis_tac[]
QED

Theorem sys_send_hard:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ∧ l0_res_of out = Fail e x ∧
  ¬l1_transient e ⇒ hard_send g [ev]
Proof
  strip_tac >> simp[hard_send_def] >> rpt conj_tac
  >- (drule ev_on_send >> simp[])
  >- (drule_all retried_send >> simp[])
  >> qpat_x_assum ‘sys_send _ _ _ = _’ mp_tac >> simp[sys_send_def] >> strip_tac >>
  ‘LENGTH out = 13’
    by (qpat_x_assum ‘l0_do _ _ _ _ = _’ mp_tac >> simp[l0_do_def, AllCaseEqs()] >>
        strip_tac >> ‘l0_rely w’ by fs[winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[ev_failed_def, MAP_SND_ZIP_REPLICATE]
QED

Theorem after_send_gone:
  MEM f (after_send g r b).gone ⇒
  MEM f b.gone ∨ (f = g ∧ ∃e x. r = Fail e x ∧ ¬l1_transient e)
Proof
  rw[after_send_def] >> every_case_tac >> gvs[set_outbox_def, MEM_FILTER]
QED

Theorem pdo_gone:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ MEM f ps'.b.gone ⇒
  MEM f ps.b.gone ∨ hard_send f evs
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[set_inb_def] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >>
  gvs[forget_def, set_outbox_def, MEM_FILTER] >>
  drule after_send_gone >> strip_tac >> gvs[set_outbox_def] >>
  drule_all sys_send_hard >> simp[]
QED

Theorem l1_flush_gone:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ MEM f b'.gone ⇒
    MEM f b.gone ∨ hard_send f evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘winv w''’ by metis_tac[sys_winv] >>
  first_x_assum drule_all >> strip_tac >> ONCE_REWRITE_TAC [hard_send_cons] >> simp[] >>
  drule after_send_gone >> strip_tac >> gvs[] >>
  drule_all sys_send_hard >> simp[]
QED

(* An action, from an fd with channel c: c's sent grows by what the
   action's sends took on f, and c stays f's or (f closed) unused *)
Theorem pdo_dinv_live:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧
  pown lfd ps ∧ l0_chan_of w f = SOME c ⇒
  dinv f c (csent w c ++ evs_sent f evs) w'
Proof
  strip_tac >> drule_all pdo_acct >> disch_then (qspec_then ‘[]’ strip_assume_tac) >>
  qpat_x_assum ‘csent w' c = _’ (SUBST1_TAC o SYM) >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (simp[dinv_def] >> NO_TAC) >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  TRY (simp[dinv_def] >> NO_TAC) >>
  TRY (drule_all sys_send_csent >> simp[dinv_def] >> NO_TAC) >>
  TRY (drule_all (cj 4 sys_csents) >> simp[dinv_def] >> NO_TAC) >>
  imp_res_tac chan_lt >> rename1 ‘sys_close g w = _’ >> Cases_on ‘g = f’ >> gvs[] >>
  TRY (drule_all (cj 4 sys_csents) >> simp[dinv_def] >> NO_TAC) >>
  drule_all sys_close_dinv >> drule_all sys_close_csent >> simp[]
QED

(* ------------------------------------------------------------------------
   The sharpened round relation
   ------------------------------------------------------------------------ *)

(* tk, plus: while live, gone only with dx (a recorded drop); once closed,
   c keeps its sent (ts), which is everything f was given unless dx *)
Definition tkx_def:
  tkx live dx w ps f c ts out ⇔
    tk live w ps f c ts out ∧
    (live ⇒ MEM f ps.b.gone ⇒ dx) ∧
    (¬live ⇒ dinv f c ts w ∧ (ts = out ∨ dx))
End

Theorem pdo_tkx:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ pown lfd ps ∧
  tkx live dx w ps f c ts out ∧ (¬live ⇒ ¬MEM f ps.acq) ⇒
  ∃live'. tkx live' (dx ∨ hard_send f evs) w' ps' f c (ts ++ evs_sent f evs)
            (out ++ wbytes f ps.b a) ∧ (¬live' ⇒ ¬MEM f ps'.acq)
Proof
  strip_tac >> qpat_x_assum ‘tkx _ _ _ _ _ _ _ _’ mp_tac >> simp[tkx_def] >> strip_tac >>
  drule_all pdo_tk >> strip_tac >> qexists_tac ‘live'’ >> simp[] >>
  ‘MEM f ps'.b.gone ⇒ MEM f ps.b.gone ∨ hard_send f evs’ by metis_tac[pdo_gone] >>
  Cases_on ‘live’ >> Cases_on ‘live'’ >> gvs[]
  >- metis_tac[]
  >- ((* f closed by this action *)
      qpat_x_assum ‘tk T _ _ _ _ _ _’ mp_tac >> qpat_x_assum ‘tk F _ _ _ _ _ _’ mp_tac >>
      simp[tk_def] >> rpt strip_tac >>
      ‘l0_chan_of w f = SOME c’ by fs[acct_def] >>
      drule_all pdo_dinv_live >> strip_tac >>
      ‘¬(¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing ∧ ¬MEM f ps.acq)’ by fs[] >>
      drule_all pdo_closed >> strip_tac >> gvs[] >>
      Cases_on ‘MEM f ps.b.gone’ >> gvs[acct_def])
  >- (qpat_x_assum ‘tk F _ _ _ _ _ _’ mp_tac >> simp[tk_def] >> strip_tac >> gvs[])
  >> (* closed before: nothing changes for f *)
  qpat_x_assum ‘tk F w _ _ _ _ _’ mp_tac >> simp[tk_def] >> strip_tac >>
  drule_all pdo_quiet >> strip_tac >>
  ‘wbytes f ps.b a = []’ by simp[wbytes_nil] >>
  drule_all pdo_dinv >> simp[]
QED

Theorem pacts_tkx:
  ∀acts w ps s rs evs w' ps' s' hs' hrs hevs live dx ts.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
    hacts lfd (s, hs_of ps) acts = SOME (hrs, hevs, (s', hs')) ∧
    pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧
    MEM f (MAP FST cm) ∧
    tkx live dx w ps f c ts (EL (cl cm f) s.clients).outgoing ∧ (¬live ⇒ ¬MEM f ps.acq) ⇒
    ∃live'. tkx live' (dx ∨ hard_send f evs) w' ps' f c (ts ++ evs_sent f evs)
              (EL (cl cm f) s'.clients).outgoing ∧
            (¬live' ⇒ ¬MEM f ps'.acq)
Proof
  Induct >> simp[pacts_def, hacts_def]
  >- (rpt strip_tac >> gvs[] >> qexists_tac ‘live’ >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘hdo _ _ _ = SOME (r2, st1, hevs1)’ >> PairCases_on ‘st1’ >>
  drule_all pdo_hdo >> strip_tac >> gvs[] >>
  drule_all pdo_tkx >> strip_tac >>
  drule_all pdo_winv >> strip_tac >>
  drule hdo_out >> strip_tac >>
  first_x_assum (qspec_then ‘cl cm f’ assume_tac) >>
  ‘hwrote s (hs_of ps) h (cl cm f) = wbytes f ps.b h’ by metis_tac[hwrote_wbytes] >>
  qpat_x_assum ‘hwrote _ _ _ _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum ‘tkx live' _ _ _ _ _ _ _’ mp_tac >>
  qpat_x_assum ‘(EL (cl cm f) _.clients).outgoing = _’ (SUBST1_TAC o SYM) >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac ‘live''’ >> fs[DISJ_ASSOC]
QED

(* ------------------------------------------------------------------------
   The tail: the write timeout's drops (D23)
   ------------------------------------------------------------------------ *)

(* The fds the round's stall step drops (stall_step's drop list) *)
Definition stall_drops_def:
  stall_drops (hfs : word64 list) (ob : word64 -> word8 list) log (ps : l1p) =
    let held = (λf. MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing);
        hs0 = FILTER (λ(f, n). held f) ps.stalls ++
              MAP (λf. (f, 0n)) (nub (FILTER (λf. held f ∧ ¬MEM f (MAP FST ps.stalls)) hfs));
        hs1 = MAP (λ(f, n). if MEM (FReset f) log then (f, pf_sendwait)
                            else if outbox_of ps.b f = [] ∨
                                    LENGTH (outbox_of ps.b f) < LENGTH (ob f) then (f, 0)
                            else (f, n + 1)) hs0
    in MAP FST (FILTER (λ(f, n). pf_sendwait ≤ n) hs1)
End

Theorem stall_step_drops:
  (stall_step hfs ob log ps).b = FOLDL drop_out ps.b (stall_drops hfs ob log ps)
Proof
  simp[stall_step_def, stall_drops_def]
QED

Theorem stall_gone:
  MEM f (stall_step hfs ob log ps).b.gone ⇔ MEM f ps.b.gone ∨ MEM f (stall_drops hfs ob log ps)
Proof
  simp[stall_step_drops, FOLDL_drop_out]
QED

(* The round tail's stall drops (as pf_tail computes them) *)
Definition tail_drops_def:
  tail_drops lfd pol hs (w, ps) =
    let fes = pf_poll_set lfd pol ps hs in
    case l1_polls [fes] w of
    | NONE => []
    | SOME (rv, w1, pevs) =>
        case l1_flush (writable_fds rv) (w1, ps.b) of
        | NONE => []
        | SOME ((w2, b2), fevs) =>
            case pf_fetch lfd pol (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))
                   (w2, ps with b := b2) of
            | NONE => []
            | SOME ((w3, ps3'), log, gevs) =>
                stall_drops (pf_held ps3') (outbox_of ps.b) log ps3'
End

Theorem l1_reap_gone:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ MEM f b'.gone ⇒ MEM f b.gone
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> gvs[l1_close_def, AllCaseEqs()] >>
      first_x_assum drule_all >> simp[forget_def, set_outbox_def, MEM_FILTER])
  >> first_x_assum drule_all >> simp[]
QED

Theorem tail_gone:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ winv w ∧
  MEM f ps'.b.gone ⇒
  MEM f ps.b.gone ∨ hard_send f evs ∨ MEM f (tail_drops lfd pol hs (w, ps))
Proof
  simp[pf_tail_def, tail_drops_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l1_reap_gone >> simp[] >> disch_then drule >>
  simp[stall_step_drops, FOLDL_drop_out] >> strip_tac >> simp[] >>
  drule pf_fetch_b >> strip_tac >> gvs[] >>
  ‘winv w1’ by metis_tac[l1_polls_winv] >>
  drule_all l1_flush_gone >> rw[] >> simp[]
QED

Theorem dinv_lt:
  dinv f c sb w ⇒ c < LENGTH w.chans
Proof
  rw[dinv_def, uchan_def] >> metis_tac[chan_lt]
QED

(* The tail of a round, from a closed fd: nothing changes for it *)
Theorem tail_dinv_dead:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ winv w ∧ qfresh w ∧
  dinv f c ts w ∧ outbox_of ps.b f = [] ⇒
  dinv f c ts w' ∧ evs_sent f evs = []
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘winv w1 ∧ qfresh w1’ by metis_tac[l1_polls_winv, l1_polls_qfresh] >>
  ‘dinv f c ts w1’ by metis_tac[l1_polls_dinv] >>
  ‘evs_sent f pevs = []’ by metis_tac[l1_polls_quiet] >>
  ‘dinv f c ts w2 ∧ evs_sent f fevs = []’
    by (irule l1_flush_dinv >> fs[] >> metis_tac[]) >>
  ‘winv w2 ∧ qfresh w2’ by metis_tac[l1_flush_winv, l1_flush_qfresh] >>
  drule_all pf_fetch_out >> strip_tac >>
  ‘dinv f c ts w3’ by metis_tac[pf_fetch_dinv] >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  drule_all l1_reap_dinv >> strip_tac >> simp[] >>
  ‘c < LENGTH w3.chans’ by metis_tac[dinv_lt] >>
  drule_all l1_reap_csent >> simp[]
QED

(* The tail of a round closing a live fd (the reap of a closing fd): its
   channel keeps what the kernel took, which is all f was given unless f
   was gone at the start, a send on it failed hard, or the write timeout
   dropped it in this tail *)
Theorem tail_live_close:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ winv w ∧ qfresh w ∧
  acct w ps.b f c out ∧
  ¬MEM f ps'.b.closing ∧ outbox_of ps'.b f = [] ∧ ¬MEM f ps'.b.gone ⇒
  dinv f c (csent w c ++ evs_sent f evs) w' ∧
  (csent w c ++ evs_sent f evs = out ∨ MEM f ps.b.gone ∨ hard_send f evs ∨
   MEM f (tail_drops lfd pol hs (w, ps)))
Proof
  strip_tac >>
  ‘∃rv w1 pevs w2 b2 fevs w3 ps3' gevs w4 b4 cevs.
     l1_polls [pf_poll_set lfd pol ps hs] w = SOME (rv, w1, pevs) ∧
     l1_flush (writable_fds rv) (w1, ps.b) = SOME ((w2, b2), fevs) ∧
     pf_fetch lfd pol (FILTER (λf. MEM f (in_fds (pf_poll_set lfd pol ps hs))) (readable_fds rv))
       (w2, ps with b := b2) = SOME ((w3, ps3'), log, gevs) ∧
     l1_reap ps3'.b.closing
       (w3, (stall_step (pf_held ps3') (outbox_of ps.b) log ps3').b) = SOME ((w4, b4), cevs) ∧
     w' = w4 ∧ ps'.b = b4 ∧ evs = pevs ++ fevs ++ gevs ++ cevs’
    by (qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
        simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  ‘tail_drops lfd pol hs (w, ps) = stall_drops (pf_held ps3') (outbox_of ps.b) log ps3'’
    by simp[tail_drops_def] >>
  gvs[] >>
  ‘l0_chan_of w f = SOME c’ by fs[acct_def] >>
  ‘winv w1 ∧ qfresh w1’ by metis_tac[l1_polls_winv, l1_polls_qfresh] >>
  drule_all l1_polls_csent >> strip_tac >>
  ‘acct w1 ps.b f c out’ by metis_tac[acct_keep] >>
  drule_all l1_flush_acct >> strip_tac >>
  ‘winv w2 ∧ qfresh w2’ by metis_tac[l1_flush_winv, l1_flush_qfresh] >>
  drule_all pf_fetch_out >> strip_tac >> gvs[] >>
  ‘l0_chan_of w3 f = SOME c ∧ csent w3 c = csent w2 c’
    by (first_x_assum irule >> fs[acct_def]) >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  ‘acct w3 ps3.b f c out’
    by (simp[Abbr ‘ps3’] >> irule (cj 4 stall_out) >> irule acct_keep >>
        conj_tac >- simp[] >> qexists_tac ‘w2’ >> simp[]) >>
  ‘ps3.b.closing = ps3'.b.closing’ by simp[Abbr ‘ps3’, stall_out] >>
  ‘dinv f c (csent w3 c) w3’ by simp[dinv_def] >>
  drule_all l1_reap_dinv >> strip_tac >>
  ‘c < LENGTH w3.chans’ by metis_tac[chan_lt] >>
  drule_all l1_reap_csent >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  ‘evs_sent f gevs = []’ by fs[] >>
  gvs[] >>
  ‘outbox_of ps3.b f = [] ∨ MEM f ps3.b.gone’
    by (Cases_on ‘MEM f ps3.b.closing’
        >- (drule_all l1_reap_dead >> simp[])
        >> ‘¬MEM f ps3'.b.closing’ by metis_tac[] >>
        drule_all l1_reap_other >> strip_tac >> gvs[]) >>
  ‘MEM f ps3.b.gone ⇒ MEM f ps.b.gone ∨ hard_send f fevs ∨
                      MEM f (stall_drops (pf_held ps3') (outbox_of ps.b) log ps3')’
    by (qpat_assum ‘Abbrev (ps3 = _)’
          (fn th => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
        REWRITE_TAC [stall_gone] >> strip_tac >> simp[] >>
        drule_all l1_flush_gone >> metis_tac[]) >>
  Cases_on ‘MEM f ps3.b.gone’ >> gvs[] >>
  qpat_x_assum ‘acct w3 ps3.b f c out’ mp_tac >> simp[acct_def]
QED

Theorem tail_tkx:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  winv w ∧ qfresh w ∧ pown lfd ps ∧ tkx live dx w ps f c ts out ⇒
  ∃live'. tkx live' (dx ∨ hard_send f evs ∨ MEM f (tail_drops lfd pol hs (w, ps)))
            w' ps' f c (ts ++ evs_sent f evs) out
Proof
  strip_tac >> qpat_x_assum ‘tkx _ _ _ _ _ _ _ _’ mp_tac >> simp[tkx_def] >> strip_tac >>
  drule_all tail_tk >> strip_tac >> qexists_tac ‘live'’ >> simp[] >>
  Cases_on ‘live'’ >> simp[]
  >- (strip_tac >> drule_all tail_gone >> strip_tac >> simp[] >>
      Cases_on ‘live’ >> gvs[tk_def]) >>
  qpat_x_assum ‘tk F _ _ _ _ _ _’ mp_tac >> simp[tk_def] >> strip_tac >>
  Cases_on ‘live’ >> gvs[]
  >- (qpat_x_assum ‘tk T _ _ _ _ _ _’ mp_tac >> simp[tk_def] >> strip_tac >>
      drule_all tail_live_close >> strip_tac >> gvs[] >> metis_tac[])
  >> qpat_x_assum ‘tk F _ _ _ _ _ _’ mp_tac >> simp[tk_def] >> strip_tac >>
  drule_all tail_dinv_dead >> simp[]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

(* The round's write-timeout drops (its tail's, after the actions) *)
Definition round_drops_def:
  round_drops lfd pol hs ws acts =
    case pacts lfd ws acts of
    | NONE => []
    | SOME (rs, evs, ws1) => tail_drops lfd pol hs ws1
End

(* round_tk sharpened: if L1 closes f in the round, f's channel keeps
   what the kernel took, and that is everything the server wrote to f's
   client unless f was gone at the start, a send on f failed hard in the
   round, or the write timeout dropped f in the round *)
Theorem round_tkx:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧ out_rel cm w ps s ∧
  (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq) ∧ l0_chan_of w f = SOME c ⇒
  MEM f (MAP FST cm) ∧
  ∃rs hevs s1 hs1.
    hacts lfd (s, hs_of ps) acts = SOME (rs, hevs, (s1, hs1)) ∧
    ∃live. tkx live (MEM f ps.b.gone ∨ hard_send f evs ∨
                     MEM f (round_drops lfd pol hs (w, ps) acts))
             w' ps' f c (csent w c ++ evs_sent f evs) (EL (cl cm f) s1.clients).outgoing
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule_all held_acct >> strip_tac >> simp[] >>
  ‘c' = c’ by gvs[acct_def] >> gvs[] >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[pround_def, AllCaseEqs()] >>
  strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  rename1 ‘pacts _ _ _ = SOME (rs1, aevs, (w1, ps1))’ >>
  ‘round_drops lfd pol hs (w, ps) acts = tail_drops lfd pol hs (w1, ps1)’
    by simp[round_drops_def] >>
  drule_all pacts_hacts >> strip_tac >> gvs[] >>
  ‘tkx T (MEM f ps.b.gone) w ps f c (csent w c) (EL (cl cm f) s.clients).outgoing’
    by simp[tkx_def, tk_def] >>
  ‘¬T ⇒ ¬MEM f ps.acq’ by simp[] >>
  drule_all pacts_tkx >> strip_tac >>
  ‘qfresh w’ by fs[out_rel_def] >>
  drule_all pacts_winv >> strip_tac >>
  drule_all pacts_qfresh >> strip_tac >>
  drule_all tail_tkx >> strip_tac >>
  qexists_tac ‘live''’ >> fs[DISJ_ASSOC]
QED

(* ------------------------------------------------------------------------
   The run, round by round (as l1pf_round_sent_upto, sharpened)
   ------------------------------------------------------------------------ *)

Theorem l1pf_round_sent_x:
  winv w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ N ⇒ SND (pcm lfd pol ifds m w0 n') + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs h' ws' evs' logs'.
    SUC n ≤ N ∧
    prounds lfd pol ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ∧
    prounds lfd pol ifds m (w0, pinit) (SUC n) = SOME (h', ws', evs', logs') ∧
        (MEM f (MAP SND (SND ws).b.tbl) ∨ MEM f (SND ws).b.closing ∨ MEM f (SND ws).acq) ∧
    l0_chan_of (FST ws) f = SOME c ⇒
    ∃live. tkx live (MEM f (SND ws).b.gone ∨ hard_send f (DROP (LENGTH evs) evs') ∨
                     MEM f (round_drops lfd pol (ifds h) ws (new_actions (log_of m) h)))
             (FST ws') (SND ws') f c
             (csent (FST ws) c ++ evs_sent f (DROP (LENGTH evs) evs'))
             (EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
                 (FST (hst lfd ifds m (psk lfd pol ifds m w0) (SUC n))).clients).outgoing
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[winv_def] >>
  drule_all prounds_SUC_step >> strip_tac >>
  qpat_x_assum ‘evs' = _’ SUBST_ALL_TAC >>
  REWRITE_TAC [DROP_LENGTH_APPEND] >>
  ‘n ≤ N’ by simp[] >>
  mp_tac (Q.INST [‘N’ |-> ‘N’] l1pf_refines_hl_out_upto) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  mp_tac (Q.INST [‘N’ |-> ‘N’] l1pf_refines_hl_upto) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  PairCases_on ‘ws’ >> PairCases_on ‘ws'’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [FST, SND]) >> REWRITE_TAC [FST, SND] >>
  Cases_on ‘hst lfd ifds m (psk lfd pol ifds m w0) n’ >> rename1 ‘_ = (s, hs)’ >> gvs[] >>
  ‘hacts_of lfd ifds m (psk lfd pol ifds m w0) n =
   new_actions (log_of m) (hhist lfd ifds m (psk lfd pol ifds m w0) n)’
    by simp[hacts_of_def] >>
  Q.SUBGOAL_THEN ‘MEM f (MAP SND ws1.b.tbl) ∨ MEM f ws1.b.closing ∨ MEM f ws1.acq’
    ASSUME_TAC >> TRY (fs[] >> NO_TAC) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ assume_tac >>
  drule round_tkx >>
  disch_then (qspecl_then [‘s’, ‘f’, ‘FST (pcm lfd pol ifds m w0 n)’, ‘c’] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  ‘hacts_tot lfd (hst lfd ifds m (psk lfd pol ifds m w0) n)
     (hacts_of lfd ifds m (psk lfd pol ifds m w0) n) = (rs, hevs, (s1, hs1))’
    by fs[hacts_tot_def] >>
  drule hround_step >> strip_tac >> simp[] >>
  ‘cl (FST (pcm lfd pol ifds m w0 n)) f < LENGTH s1.clients’
    by (drule hacts_world >> strip_tac >>
        qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> simp[pv_rel_def] >> strip_tac >>
        drule cl_mem >> gvs[EVERY_MEM]) >>
  ‘∀hf. (EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
           (SND (hpoll lfd hs1 hf s1)).clients).outgoing =
        (EL (cl (FST (pcm lfd pol ifds m w0 n)) f) s1.clients).outgoing’
    by (gen_tac >> qspecl_then [‘s1’, ‘lfd’, ‘hs1’, ‘hf’] mp_tac
          (Q.GENL [‘s’, ‘lfd’, ‘hs’, ‘hfds’] cext_hpoll) >>
        simp[cext_def]) >>
  simp[] >> qexists_tac ‘live’ >> simp[]
QED

(* ------------------------------------------------------------------------
   A connection that is still f's (channel c) after a round was not
   re-accepted in it: its client stays the same
   ------------------------------------------------------------------------ *)

Theorem tail_noconn:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ winv w ∧ qfresh w ∧
  tkx live dx w ps f c ts out ∧ l0_chan_of w' f = SOME c ⇒
  ¬MEM (FConn f) log
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >> strip_tac >>
  ‘winv w1 ∧ qfresh w1’ by metis_tac[l1_polls_winv, l1_polls_qfresh] >>
  ‘winv w2 ∧ qfresh w2’ by metis_tac[l1_flush_winv, l1_flush_qfresh] >>
  drule_all pf_fetch_out >> strip_tac >>
  ‘∀c. l0_chan_of w2 f ≠ SOME c’ by metis_tac[] >>
  Cases_on ‘live’
  >- ((* live: f keeps channel c up to the fetch *)
      ‘acct w ps.b f c out’ by fs[tkx_def, tk_def] >>
      ‘l0_chan_of w f = SOME c’ by fs[acct_def] >>
      drule_all l1_polls_csent >> strip_tac >>
      ‘acct w1 ps.b f c out’ by metis_tac[acct_keep] >>
      drule_all l1_flush_acct >> strip_tac >> gvs[acct_def]) >>
  (* closed: c is unused once f has no channel, and stays unused *)
  ‘dinv f c ts w ∧ outbox_of ps.b f = []’ by fs[tkx_def, tk_def] >>
  ‘dinv f c ts w1’ by (drule_all l1_polls_dinv >> simp[]) >>
  ‘dinv f c ts w2 ∧ evs_sent f fevs = []’ by (irule l1_flush_dinv >> fs[] >> metis_tac[]) >>
  ‘uchan c ts w2’ by gvs[dinv_def] >>
  ‘wpres (uchan c ts)’ by simp[wpres_uchan] >>
  drule_all pf_fetch_wpres >> strip_tac >>
  ‘winv w3’ by (drule_all pf_fetch_winv >> simp[]) >>
  drule_all l1_reap_wpres >> strip_tac >>
  gvs[uchan_def] >> drule chan_of_used >> simp[]
QED

(* ------------------------------------------------------------------------
   Send progress: a send on f that L1 does not retry either took bytes or
   failed hard, when L1 sends f's (non-empty) outbox
   ------------------------------------------------------------------------ *)

(* sys_send_res without the length hypothesis: D24 (the kernel's counts
   are below 2^64) makes the recorded count exact for any payload *)
Theorem sys_send_res_rely:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ∧ bs ≠ [] ⇒
  (∃k. l0_res_of out = Ok k ∧ 0 < k ∧ k ≤ LENGTH bs) ∨ (∃e x. l0_res_of out = Fail e x)
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  ‘TAKE 8 (fd_bytes g ++ bs) = fd_bytes g ∧ DROP 8 (fd_bytes g ++ bs) = bs’
    by metis_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  gvs[] >>
  ‘l0_rely (l0_tick «sys_send» w)’
    by (gvs[winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘l0_res_ok r’
    by (qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
        simp[l0_send_def, not_chan_def] >> rw[AllCaseEqs()] >>
        TRY (irule fail_ok >> first_assum ACCEPT_TAC >> NO_TAC) >>
        simp[l0_res_ok_def, MIN_DEF] >> rw[] >> fs[l0_rely_def] >>
        irule LESS_EQ_LESS_TRANS >> goal_assum (first_assum o mp_then Any mp_tac) >>
        simp[]) >>
  simp[l0_res_of_enc] >>
  qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
  simp[l0_send_def, not_chan_def] >> rw[AllCaseEqs()] >> gvs[fail_def] >>
  simp[MIN_DEF] >> rw[] >> fs[] >> Cases_on ‘bs’ >> fs[]
QED

Theorem l1_flush_progress:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧
    l0_chan_of w f = SOME c ∧ (∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ⇒
    evs_sent f evs ≠ [] ∨ hard_send f evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum (qspecl_then [‘w’, ‘b’] mp_tac) >> fs[] >> metis_tac[]) >>
  gvs[AllCaseEqs()] >>
  rename1 ‘sys_send h _ w = SOME (out, w1, ev1)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  drule_all sys_send_csent >> strip_tac >>
  ONCE_REWRITE_TAC [hard_send_cons] >> simp[] >>
  TRY (first_x_assum (qspecl_then [‘w1’, ‘after_send h (l0_res_of out) b’] mp_tac) >>
       fs[] >> metis_tac[] >> NO_TAC) >>
  ‘h = f’ by (imp_res_tac ev_on_send >> fs[]) >> gvs[] >>
  drule_all retried_send >> strip_tac >>
  drule sys_send_res_rely >> simp[] >> strip_tac >> gvs[] >>
  TRY (Cases_on ‘outbox_of b f’ >> gvs[] >> NO_TAC) >>
  rpt strip_tac >> disj1_tac >> drule_all sys_send_hard >> simp[]
QED

Theorem l1_polls_names:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒
    EVERY (λev. ev_name ev = ExtCall «sys_poll») evs
Proof
  Induct >> simp[l1_polls_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> gvs[sys_poll_def] >>
  drule l0_do_buf_cases >> rw[] >> simp[ev_name_def]
QED

(* A round from an fd with something to send: a send on it that L1 does
   not retry took bytes or failed hard (only the flush sends on it) *)
Theorem pround_progress:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ olive lfd f ps ∧ l0_chan_of w f = SOME c ∧
  MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev ⇒
  evs_sent f evs ≠ [] ∨ hard_send f evs
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule_all pacts_live >> strip_tac >>
  rename1 ‘l1_polls _ wa = SOME (rv, w1, pevs)’ >>
  drule_all l1_polls_csent >> strip_tac >>
  ‘winv w1’ by metis_tac[l1_polls_winv] >>
  imp_res_tac ev_on_name >>
  imp_res_tac l1_polls_names >> imp_res_tac pf_fetch_names >> imp_res_tac l1_reap_names >>
  gvs[] >>
  TRY (gvs[EXISTS_MEM] >> metis_tac[] >> NO_TAC) >>
  TRY (gvs[EVERY_MEM] >> res_tac >> gvs[] >> NO_TAC) >>
  rename1 ‘l1_flush _ (w1, pa.b) = SOME ((w2, b2), fevs)’ >>
  ‘evs_sent f fevs ≠ [] ∨ hard_send f fevs’
    by (irule l1_flush_progress >> simp[] >> metis_tac[]) >>
  gvs[]
QED

(* An fd held (or pre-accepted) at a round's start that still has its
   channel at the end was not re-accepted in the round *)
Theorem round_noconn:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧ out_rel cm w ps s ∧
  (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq) ∧ l0_chan_of w f = SOME c ∧
  l0_chan_of w' f = SOME c ⇒
  ¬MEM (FConn f) log
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule_all held_acct >> strip_tac >>
  ‘c' = c’ by gvs[acct_def] >> gvs[] >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[pround_def, AllCaseEqs()] >>
  strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  rename1 ‘pacts _ _ _ = SOME (rs1, aevs, (w1, ps1))’ >>
  drule_all pacts_hacts >> strip_tac >> gvs[] >>
  ‘tkx T (MEM f ps.b.gone) w ps f c (csent w c) (EL (cl cm f) s.clients).outgoing’
    by simp[tkx_def, tk_def] >>
  ‘¬T ⇒ ¬MEM f ps.acq’ by simp[] >>
  drule_all pacts_tkx >> strip_tac >>
  ‘qfresh w’ by fs[out_rel_def] >>
  drule_all pacts_winv >> strip_tac >>
  drule_all pacts_qfresh >> strip_tac >>
  drule_all tail_noconn >> simp[]
QED

Theorem l1pf_round_noconn:
  winv w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ N ⇒ SND (pcm lfd pol ifds m w0 n') + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs h' ws' evs' logs'.
    SUC n ≤ N ∧
    prounds lfd pol ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ∧
    prounds lfd pol ifds m (w0, pinit) (SUC n) = SOME (h', ws', evs', logs') ∧
        (MEM f (MAP SND (SND ws).b.tbl) ∨ MEM f (SND ws).b.closing ∨ MEM f (SND ws).acq) ∧
    l0_chan_of (FST ws) f = SOME c ∧ l0_chan_of (FST ws') f = SOME c ⇒
    ¬MEM (FConn f) (plog lfd pol ifds m w0 n)
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[winv_def] >>
  qpat_assum ‘prounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [prounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >> gvs[] >>
  ‘plog lfd pol ifds m w0 n = log’
    by (drule prounds_logs >> strip_tac >>
        qpat_x_assum ‘prounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule plog_EL >> disch_then (qspec_then ‘n’ mp_tac) >>
        simp[EL_APPEND2]) >>
  ‘n ≤ N’ by simp[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [EVERY_APPEND]) >>
  mp_tac (Q.INST [‘N’ |-> ‘N’] l1pf_refines_hl_out_upto) >>
  (impl_tac >- fs[]) >>
  disch_then drule_all >> strip_tac >>
  mp_tac (Q.INST [‘N’ |-> ‘N’] l1pf_refines_hl_upto) >>
  (impl_tac >- fs[]) >>
  disch_then drule_all >> strip_tac >>
  PairCases_on ‘ws’ >> PairCases_on ‘ws'’ >> gvs[] >>
  irule round_noconn >> simp[] >> metis_tac[]
QED
