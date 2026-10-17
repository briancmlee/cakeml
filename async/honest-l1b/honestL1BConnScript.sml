(*
  L3-09 (S3): how a connection leaves a listener's accept queue, along a
  faithful trace.  Steps of time only append to a queue; an L1 call
  other than an accept or a close on the listener only appends too.  So a
  queued channel leaves the queue only at an event that resolves it: an
  accept that opens it under the fd the event reports, or a failed accept
  or a close of the listener after which it is broken.

  MAIN: qexit_trace.
*)
Theory honestL1BConn
Ancestors
  honestL1BFaith honestL1BStmts honestL1PFConn honestL0WorldInv honestL0Part
  honestEchoL0Spec honestL0World honestL0
Libs
  preamble

Theorem FOLDL_break_broken:
  ∀q w. j0 < LENGTH w.chans ∧ (MEM j0 q ∨ (EL j0 w.chans).broken) ⇒
        j0 < LENGTH (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q).chans ∧
        (EL j0 (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q).chans).broken
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  first_x_assum (qspec_then ‘upd_lchan h (break_lchan e F) w’ mp_tac) >>
  impl_tac
  >- (fs[upd_lchan_def, EL_LUPDATE] >> Cases_on ‘j0 = h’ >> gvs[] >>
      rw[break_lchan_def] >> gvs[]) >>
  simp[]
QED

(* A close of the listener breaks what was queued on it *)
Theorem close_queue:
  l0_close l t = (r, u) ∧ l0wf t ∧ MEM j0 (qof t l) ∧ ¬MEM j0 (qof u l) ⇒
  j0 < LENGTH u.chans ∧ (EL j0 u.chans).broken
Proof
  strip_tac >> ‘j0 < LENGTH t.chans’ by metis_tac[qof_lt] >>
  ‘u = t ∨ u = close_fd l t’ by gvs[l0_close_def, AllCaseEqs()] >> gvs[] >>
  qpat_x_assum ‘¬MEM _ _’ mp_tac >> simp[close_fd_def] >>
  Cases_on ‘l0_chan_of t l’ >> simp[]
  >- (Cases_on ‘FILTER (λ(l', p, q). l' = l) t.listeners’ >> simp[] >>
      PairCases_on ‘h’ >> simp[] >> strip_tac >>
      ‘h2 = qof t l’ by simp[qof_def] >> gvs[] >>
      qspecl_then [‘qof t l’, ‘t with listeners := FILTER (λ(l',p,q). l' ≠ l) t.listeners’]
        mp_tac (Q.INST [‘e’ |-> ‘E_CONNRESET’] FOLDL_break_broken) >> simp[])
QED

Theorem call_accept_conf:
  l0_call «sys_accept» conf b w = SOME r ⇒ LENGTH conf = 8
Proof
  rw[l0_call_def, AllCaseEqs()]
QED

Theorem qof_call_close:
  l0_call «sys_close» conf bytes w = SOME (FFIreturn bytes' w') ∧ bytes_fd conf = l ⇒
  ∃r. l0_close l w = (r, w')
Proof
  rw[l0_call_def] >> pairarg_tac >> gvs[]
QED

(* One call: a queued channel that leaves the queue is resolved *)
Theorem qexit_ffi:
  l0wf u ∧ l0_ffi_fn n conf inp u = SOME (FFIreturn out u') ∧ MEM n l1_names ∧
  MEM j0 (qof u l) ∧ ¬MEM j0 (qof u' l) ⇒
  (n = «sys_accept» ∧ LENGTH conf = 8 ∧ bytes_fd conf = l ∧
   ∃k. out = enc_res (Ok (w2n k)) ∧ ALOOKUP u'.open_fds k = SOME j0) ∨
  (j0 < LENGTH u'.chans ∧ (EL j0 u'.chans).broken)
Proof
  strip_tac >> gvs[l0_ffi_fn_def, AllCaseEqs()] >>
  qabbrev_tac ‘t = l0_tick n u’ >>
  ‘MEM j0 (qof t l)’
    by (qspecl_then [‘u’, ‘n’, ‘l’] strip_assume_tac
          (Q.GENL [‘w’, ‘nm’, ‘l’] qof_tick) >> gvs[Abbr ‘t’]) >>
  ‘l0wf t’ by simp[Abbr ‘t’, l0wf_tick] >>
  ‘j0 < LENGTH t.chans’ by metis_tac[qof_lt] >>
  rename1 ‘l0_call n conf inp t = SOME (FFIreturn out u1)’ >>
  Cases_on ‘n = «sys_accept» ∧ bytes_fd conf = l’
  >- (gvs[] >> drule qof_call_accept >> disch_then (qspec_then ‘bytes_fd conf’ mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      drule call_accept_conf >> strip_tac >>
      drule accept_chans_len >> strip_tac >>
      drule accept_queue >> strip_tac >> gvs[] >> metis_tac[])
  >> Cases_on ‘n = «sys_close» ∧ bytes_fd conf = l’
  >- (gvs[] >> drule qof_call_close >> disch_then (qspec_then ‘bytes_fd conf’ mp_tac) >>
      simp[] >> strip_tac >>
      drule_all close_queue >> simp[])
  >> ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
  drule qof_call >> simp[] >> disch_then (qspec_then ‘l’ mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >> gvs[]
QED

(* MAIN: along a faithful trace, a queued channel that leaves the queue is
   resolved at some event: accepted under the fd the event reports, or
   broken *)
Theorem qexit_trace:
  ∀evs u u'. faithful u evs ∧ l0wf u ∧
             FOLDL l0_step (SOME u) (MAP ev_lcall evs) = SOME u' ∧
             MEM j0 (qof u l) ∧ ¬MEM j0 (qof u' l) ⇒
             ∃a ev b x. evs = a ++ [ev] ++ b ∧
                        FOLDL l0_step (SOME u) (MAP ev_lcall (a ++ [ev])) = SOME x ∧
                        ((∃k. l0_event_accepted ev = SOME k ∧ ALOOKUP x.open_fds k = SOME j0) ∨
                         (j0 < LENGTH x.chans ∧ (EL j0 x.chans).broken))
Proof
  Induct >- (rw[] >> gvs[]) >>
  rpt gen_tac >> strip_tac >> qpat_x_assum ‘faithful _ _’ mp_tac >>
  simp[faithful_def] >> strip_tac >>
  ‘l0_step (SOME u) (ev_lcall h) = SOME u''’ by gvs[ev_lcall_def, l0_step_def] >>
  ‘l0wf u''’ by metis_tac[l0wf_ffi_fn] >>
  ‘FOLDL l0_step (SOME u'') (MAP ev_lcall evs) = SOME u'’
    by (qpat_x_assum ‘FOLDL _ _ (MAP _ (h::evs)) = _’ mp_tac >> REWRITE_TAC[MAP, FOLDL] >>
        qpat_assum ‘l0_step _ _ = _’ (fn th => REWRITE_TAC[th])) >>
  Cases_on ‘MEM j0 (qof u'' l)’
  >- (first_x_assum (qspecl_then [‘u''’, ‘u'’] mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      qexistsl_tac [‘h :: a’, ‘ev’, ‘b’, ‘x’] >> conj_tac >- simp[] >>
      REWRITE_TAC[APPEND, MAP, FOLDL] >> asm_rewrite_tac[] >> fs[])
  >> drule_all qexit_ffi >> strip_tac >>
  qexistsl_tac [‘[]’, ‘h’, ‘evs’, ‘u''’] >> simp[] >> gvs[] >>
  disj1_tac >> qexists_tac ‘k’ >>
  simp[l0_event_accepted_def, l0_ev_res_def] >>
  ‘dec_res (enc_res (Ok (w2n k)) ++ []) = SOME (Ok (w2n k))’
    by (irule dec_enc_res >> simp[l0_res_ok_def] >>
        assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
  fs[]
QED

(* ------------------------------------------------------------------------
   Invariants along a faithful trace
   ------------------------------------------------------------------------ *)

Theorem faithful_inv:
  (∀n conf b out u u'. P u ∧ l0_ffi_fn n conf b u = SOME (FFIreturn out u') ∧
                       MEM n l1_names ⇒ P u') ⇒
  ∀evs u u'. faithful u evs ∧ P u ∧ FOLDL l0_step (SOME u) (MAP ev_lcall evs) = SOME u' ⇒
             P u'
Proof
  strip_tac >> Induct >> rw[faithful_def] >> gvs[ev_lcall_def, l0_step_def] >>
  metis_tac[]
QED

Theorem faithful_prefix:
  ∀a b w. faithful w (a ++ b) ⇒ faithful w a
Proof
  Induct >> rw[faithful_def] >> metis_tac[]
QED

(* lfd is the only listener (or there is none) *)
Definition lone_def:
  lone lfd w ⇔ MAP FST w.listeners = [lfd] ∨ MAP FST w.listeners = []
End

Theorem lone_simple[simp]:
  (lone l (upd_lchan j g w) ⇔ lone l w) ∧ (lone l (w with chans := cs) ⇔ lone l w) ∧
  (lone l (w with hist := h) ⇔ lone l w) ∧ (lone l (w with clock := c) ⇔ lone l w) ∧
  (lone l (w with open_fds := ofs) ⇔ lone l w) ∧ (lone l (w with reserved := rs) ⇔ lone l w)
Proof
  simp[lone_def, upd_lchan_def]
QED

(* lone reads only the listeners' fds (simp's MAP_EQ_NIL / MAP_EQ_SING would
   otherwise unfold lone_def before MAP_FST_AFUPDKEY applies) *)
Theorem lone_MAP:
  MAP FST w'.listeners = MAP FST w.listeners ∧ lone l w ⇒ lone l w'
Proof
  REWRITE_TAC[lone_def] >> rpt strip_tac >> asm_rewrite_tac[]
QED

Theorem lone_AFUPDKEY[simp]:
  lone l (w with listeners := AFUPDKEY k g w.listeners) ⇔ lone l w
Proof
  eq_tac >> strip_tac >> irule lone_MAP
  >- (qexists_tac ‘w with listeners := AFUPDKEY k g w.listeners’ >>
      conj_tac >- simp[honestL1PFConnTheory.MAP_FST_AFUPDKEY] >> first_assum ACCEPT_TAC)
  >> qexists_tac ‘w’ >>
  conj_tac >- simp[honestL1PFConnTheory.MAP_FST_AFUPDKEY] >> first_assum ACCEPT_TAC
QED

Theorem lone_FOLDL_upd[simp]:
  ∀q w. lone l (FOLDL (λw j. upd_lchan j g w) w q) ⇔ lone l w
Proof
  Induct >> simp[]
QED

Theorem lone_deliver:
  lone l w ⇒ lone l (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  irule lone_MAP >> qexists_tac ‘w’ >>
  conj_tac >- simp[honestL1PFConnTheory.MAP_FST_AFUPDKEY] >> first_assum ACCEPT_TAC
QED

Theorem lone_tick:
  lone l w ⇒ lone l (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. lone l w ⇒ lone l (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[lone_deliver]) >>
  rw[] >> first_x_assum irule >> gvs[lone_def]
QED

Theorem lone_ticks:
  ∀k w. lone l w ⇒ lone l (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[lone_tick]
QED

Theorem lone_FILTER[local]:
  lone l w ⇒ lone l (w with listeners := FILTER P w.listeners)
Proof
  rw[lone_def] >> gvs[] >> Cases_on ‘w.listeners’ >> gvs[] >> rw[]
QED

Theorem lone_ops:
  (lone l w ∧ l0_send g bs w = (r, w') ⇒ lone l w') ∧
  (lone l w ∧ l0_recv g n w = (r, d, w') ⇒ lone l w') ∧
  (lone l w ∧ l0_shutdown g w = (r, w') ⇒ lone l w') ∧
  (lone l w ∧ l0_connerr g w = (y, w') ⇒ lone l w') ∧
  (lone l w ∧ l0_close g w = (r, w') ⇒ lone l w') ∧
  (lone l w ∧ l0_accept g w = (r, w') ⇒ lone l w')
Proof
  rpt conj_tac >> strip_tac
  >- gvs[l0_send_def, AllCaseEqs()]
  >- gvs[l0_recv_def, AllCaseEqs()]
  >- gvs[l0_shutdown_def, AllCaseEqs()]
  >- gvs[l0_connerr_def, AllCaseEqs()]
  >- (gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >>
      simp[] >> irule lone_FILTER >> simp[])
  >> gvs[l0_accept_def, AllCaseEqs(), fail_def, l0_alloc_def] >>
  irule lone_MAP >> qexists_tac ‘w’ >>
  asm_simp_tac (srw_ss()) [honestL1PFConnTheory.MAP_FST_AFUPDKEY]
QED

Theorem lone_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_connect» ∧
  n ≠ «sys_listen» ∧ lone l w ⇒ lone l w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac lone_ops >> gvs[] >>
  metis_tac[lone_ticks, lone_ops]
QED

Theorem lone_ffi:
  lone l u ∧ l0_ffi_fn n conf b u = SOME (FFIreturn out u') ∧ MEM n l1_names ⇒ lone l u'
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >>
  ‘lone l (l0_tick n u)’ by simp[lone_tick] >>
  ‘n ≠ «sys_connect» ∧ n ≠ «sys_listen»’ by (gvs[l1_names_def] >> EVAL_TAC) >>
  drule_all lone_call >> simp[lone_def]
QED
