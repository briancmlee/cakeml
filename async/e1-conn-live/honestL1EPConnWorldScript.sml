(*
  E1's events replay in L0 (task D, r3-close): honestL1BFaith's faithful /
  fplays with E1's calls (sys_connect, sys_connerr, sys_shutdown) added, for
  eround and erounds; and honestL1BConn's qexit_trace and lone_ffi for those
  calls.  (e1-trace's eplays is not on the R3 line.)
*)
Theory honestL1EPConnWorld
Ancestors
  honestL1BConn honestL1BFaith honestL1BRuns honestL1BStmts
  honestL1EPConnRound honestL1EPModel honestL1PFConn honestL1PFClose honestL1PFRound honestL1PFModel
  honestL1Model honestEchoL0Spec honestL0Part honestL0WorldProps
  honestL0WorldInv honestL0World honestL0
Libs
  preamble

Definition e1_names_def:
  e1_names = l1_names ++ [«sys_connect»; «sys_connerr»; «sys_shutdown»]
End

(* honestL1BFaith.faithful, over E1's calls *)
Definition efaithful_def:
  efaithful w [] = T ∧
  efaithful w (ev :: evs) =
    ∃n conf bs u. ev = IO_event (ExtCall n) conf bs ∧ MEM n e1_names ∧
                  l0_ffi_fn n conf (MAP FST bs) w = SOME (FFIreturn (MAP SND bs) u) ∧
                  efaithful u evs
End

Definition efplays_def:
  efplays w w' (evs : io_event list) ⇔
    l0_rely w ⇒ FOLDL l0_step (SOME w) (MAP ev_lcall evs) = SOME w' ∧ l0_rely w' ∧
                efaithful w evs
End

Theorem FOLDL_step_NONE[local,simp]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem faithful_efaithful:
  ∀evs w. faithful w evs ⇒ efaithful w evs
Proof
  Induct >> rw[faithful_def, efaithful_def] >> simp[e1_names_def] >> metis_tac[]
QED

Theorem fplays_efplays:
  fplays w w' evs ⇒ efplays w w' evs
Proof
  rw[fplays_def, efplays_def] >> metis_tac[faithful_efaithful]
QED

Theorem efaithful_append:
  ∀a w w2. efaithful w a ∧ FOLDL l0_step (SOME w) (MAP ev_lcall a) = SOME w2 ∧
           efaithful w2 b ⇒ efaithful w (a ++ b)
Proof
  Induct >> rw[efaithful_def] >> gvs[ev_lcall_def, l0_step_def] >> metis_tac[]
QED

Theorem efaithful_prefix:
  ∀a b w. efaithful w (a ++ b) ⇒ efaithful w a
Proof
  Induct >> rw[efaithful_def] >> metis_tac[]
QED

Theorem efaithful_drop:
  ∀a b w w'. efaithful w (a ++ b) ∧ FOLDL l0_step (SOME w) (MAP ev_lcall a) = SOME w' ⇒
             efaithful w' b
Proof
  Induct >> rw[efaithful_def] >> gvs[ev_lcall_def, l0_step_def] >> metis_tac[]
QED

Theorem efplays_nil[simp]:
  efplays w w []
Proof
  simp[efplays_def, efaithful_def]
QED

Theorem efplays_trans:
  efplays w1 w2 a ∧ efplays w2 w3 b ⇒ efplays w1 w3 (a ++ b)
Proof
  rw[efplays_def] >> fs[FOLDL_APPEND] >> metis_tac[efaithful_append]
QED

Theorem efplays_cons:
  efplays w1 w2 [e] ∧ efplays w2 w3 b ⇒ efplays w1 w3 (e :: b)
Proof
  metis_tac[efplays_trans, APPEND]
QED

Theorem efplays_do:
  l0_do n conf alen w = SOME (out, w', ev) ∧ MEM n e1_names ⇒ efplays w w' [ev]
Proof
  rw[efplays_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0_ffi_fn n conf (REPLICATE alen 0w) w =
     SOME (FFIreturn out (w1 with hist := w.hist ++ [(n, conf, REPLICATE alen 0w)]))’
    by simp[l0_ffi_fn_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP, efaithful_def]
QED

Theorem efplays_sys_e:
  (sys_connect p w = SOME (out, w', ev) ⇒ efplays w w' [ev]) ∧
  (sys_connerr g w = SOME (out, w', ev) ⇒ efplays w w' [ev]) ∧
  (sys_shutdown g w = SOME (out, w', ev) ⇒ efplays w w' [ev])
Proof
  rw[sys_connect_def, sys_connerr_def, sys_shutdown_def] >>
  irule efplays_do >> simp[e1_names_def] >> metis_tac[]
QED

Theorem efplays_sys:
  (sys_close f w = SOME (out, w', ev) ⇒ efplays w w' [ev])
Proof
  metis_tac[fplays_sys, fplays_efplays]
QED

Theorem efplays_edo:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒ efplays w w' evs
Proof
  Cases_on ‘a’ >> simp[edo_def] >> rw[AllCaseEqs()] >> gvs[pf_close_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >> TRY (PairCases_on ‘z'’) >> gvs[] >>
  FIRST [
    drule fplays_pdo >> simp[fplays_efplays] >> NO_TAC,
    drule fplays_close >> simp[fplays_efplays] >> NO_TAC,
    drule (cj 1 efplays_sys_e) >> simp[] >> NO_TAC,
    irule efplays_cons >> qexists_tac ‘w''’ >>
    conj_tac >- (drule (cj 1 efplays_sys_e) >> simp[]) >>
    drule efplays_sys >> simp[]]
QED

Theorem efplays_eacts:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ⇒ efplays w w' evs
Proof
  Induct >> rw[eacts_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  res_tac >> imp_res_tac efplays_edo >> irule efplays_trans >> metis_tac[]
QED

Theorem efplays_settle:
  ∀fs w es w' es' evs. settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ efplays w w' evs
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> drule (cj 2 efplays_sys_e) >> strip_tac >>
  irule efplays_cons >> metis_tac[]
QED

Theorem efplays_etail:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ⇒ efplays w w' evs
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac fplays_polls >> imp_res_tac fplays_flush >> imp_res_tac fplays_fetch >>
  imp_res_tac fplays_reap >> imp_res_tac efplays_settle >>
  imp_res_tac fplays_efplays >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  rpt (irule efplays_trans >> goal_assum (first_assum o mp_then Any mp_tac)) >>
  first_assum ACCEPT_TAC
QED

Theorem efplays_pf_shuts:
  ∀fs w ps w' ps' kp sh evs.
    pf_shuts fs (w, ps) = SOME ((w', ps'), kp, sh, evs) ⇒ efplays w w' evs
Proof
  Induct >- simp[pf_shuts_def] >>
  rpt gen_tac >> rename1 ‘kf :: fs’ >> PairCases_on ‘kf’ >> rename1 ‘(k, f) :: fs’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule >> simp[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule >> simp[]) >>
  Cases_on ‘sys_shutdown f w’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  rename1 ‘sys_shutdown _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> PairCases_on ‘z’ >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule (cj 3 efplays_sys_e) >> strip_tac >>
  irule efplays_cons >> metis_tac[]
QED

Theorem efplays_eshuts:
  eshuts (w, es) = SOME ((w', es'), evs) ⇒ efplays w w' evs
Proof
  simp[eshuts_def] >> strip_tac >> pairarg_tac >> gvs[] >>
  drule efplays_pf_shuts >> simp[]
QED

(* MAIN: an E1 round replays *)
Theorem efplays_eround:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ⇒ efplays w w' evs
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  imp_res_tac efplays_eacts >> imp_res_tac efplays_etail >> imp_res_tac efplays_eshuts >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  irule efplays_trans >> goal_assum (first_assum o mp_then Any mp_tac) >>
  irule efplays_trans >> goal_assum (first_assum o mp_then Any mp_tac) >>
  first_assum ACCEPT_TAC
QED

Theorem efplays_erounds:
  ∀n h w es evs logs.
    erounds lfd pol ifds m (w0, es0) n = SOME (h, (w, es), evs, logs) ⇒ efplays w0 w evs
Proof
  Induct >- rw[erounds_def] >>
  rw[erounds_def, AllCaseEqs()] >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >> imp_res_tac efplays_eround >>
  irule efplays_trans >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   honestL1BConn's qexit_trace and lone_ffi, with E1's calls
   ------------------------------------------------------------------------ *)

Theorem qof_call_e:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧
  ¬((n = «sys_accept» ∨ n = «sys_close») ∧ bytes_fd conf = l) ⇒
  ∃t. qof w' l = qof w l ++ t
Proof
  Cases_on ‘n = «sys_connect»’
  >- (simp[l0_call_def] >> rw[AllCaseEqs()] >> gvs[] >>
      qexists_tac ‘[]’ >> simp[] >> irule qof_connect >> metis_tac[]) >>
  strip_tac >> drule qof_call >> metis_tac[]
QED

Theorem qexit_ffi_e:
  l0wf u ∧ l0_ffi_fn n conf inp u = SOME (FFIreturn out u') ∧
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
  >> drule qof_call_e >> disch_then (qspec_then ‘l’ mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >> gvs[]
QED

(* MAIN: along an E1-faithful trace, a queued channel that leaves the queue
   is resolved at some event *)
Theorem qexit_trace_e:
  ∀evs u u'. efaithful u evs ∧ l0wf u ∧
             FOLDL l0_step (SOME u) (MAP ev_lcall evs) = SOME u' ∧
             MEM j0 (qof u l) ∧ ¬MEM j0 (qof u' l) ⇒
             ∃a ev b x. evs = a ++ [ev] ++ b ∧
                        FOLDL l0_step (SOME u) (MAP ev_lcall (a ++ [ev])) = SOME x ∧
                        ((∃k. l0_event_accepted ev = SOME k ∧ ALOOKUP x.open_fds k = SOME j0) ∨
                         (j0 < LENGTH x.chans ∧ (EL j0 x.chans).broken))
Proof
  Induct >- (rw[] >> gvs[]) >>
  rpt gen_tac >> strip_tac >> qpat_x_assum ‘efaithful _ _’ mp_tac >>
  simp[efaithful_def] >> strip_tac >>
  ‘l0_step (SOME u) (ev_lcall h) = SOME u''’ by gvs[ev_lcall_def, l0_step_def] >>
  ‘l0wf u''’ by metis_tac[l0wf_ffi_fn] >>
  ‘FOLDL l0_step (SOME u'') (MAP ev_lcall evs) = SOME u'’
    by (qpat_x_assum ‘FOLDL _ _ (MAP _ (h::evs)) = _’ mp_tac >> REWRITE_TAC[MAP, FOLDL] >>
        qpat_assum ‘l0_step _ _ = _’ (fn th => REWRITE_TAC[th])) >>
  Cases_on ‘MEM j0 (qof u'' l)’
  >- (first_x_assum (qspecl_then [‘u''’, ‘u'’] mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      qexistsl_tac [‘h :: a’, ‘ev’, ‘b’, ‘x’] >> conj_tac >- simp[] >>
      REWRITE_TAC[APPEND, MAP, FOLDL] >> asm_rewrite_tac[] >> fs[])
  >> drule_all qexit_ffi_e >> strip_tac >>
  qexistsl_tac [‘[]’, ‘h’, ‘evs’, ‘u''’] >> simp[] >> gvs[] >>
  disj1_tac >> qexists_tac ‘k’ >>
  simp[l0_event_accepted_def, l0_ev_res_def] >>
  ‘dec_res (enc_res (Ok (w2n k)) ++ []) = SOME (Ok (w2n k))’
    by (irule dec_enc_res >> simp[l0_res_ok_def] >>
        assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
  fs[]
QED

Theorem efaithful_inv:
  (∀n conf b out u u'. P u ∧ l0_ffi_fn n conf b u = SOME (FFIreturn out u') ∧
                       MEM n e1_names ⇒ P u') ⇒
  ∀evs u u'. efaithful u evs ∧ P u ∧ FOLDL l0_step (SOME u) (MAP ev_lcall evs) = SOME u' ⇒
             P u'
Proof
  strip_tac >> Induct >> rw[efaithful_def] >> gvs[ev_lcall_def, l0_step_def] >>
  metis_tac[]
QED

Theorem efaithful_world_inv:
  (∀n conf b out u u'. P u ∧ l0_ffi_fn n conf b u = SOME (FFIreturn out u') ∧
                       MEM n e1_names ⇒ P u') ∧
  efaithful w0 (a ++ b) ∧ P w0 ∧ world_at w0 a = SOME w ⇒ P w
Proof
  rw[world_at_def, l0_replay_def] >> drule efaithful_inv >>
  disch_then irule >> metis_tac[efaithful_prefix]
QED

Theorem lone_connect:
  lone l w ∧ l0_connect p w = (r, v, w') ⇒ lone l w'
Proof
  rw[l0_connect_def, AllCaseEqs()] >> gvs[]
QED

Theorem lone_ffi_e:
  lone l u ∧ l0_ffi_fn n conf b u = SOME (FFIreturn out u') ∧ MEM n e1_names ⇒ lone l u'
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >>
  ‘lone l (l0_tick n u)’ by simp[lone_tick] >>
  Cases_on ‘n = «sys_connect»’
  >- (gvs[l0_call_def, AllCaseEqs()] >>
      drule_all lone_connect >> simp[lone_def]) >>
  ‘n ≠ «sys_listen»’ by (gvs[e1_names_def, l1_names_def] >> EVAL_TAC) >>
  drule_all lone_call >> simp[lone_def]
QED

(* The world before an E1-faithful trace's i-th event keeps the rely, and
   the event is that world's answer to its call *)
Theorem efaithful_EL_call:
  ∀l w0 i. efaithful w0 l ∧ l0_rely w0 ∧ i < LENGTH l ⇒
           ∃x n' conf bs u.
             EL i l = IO_event (ExtCall n') conf bs ∧ l0_rely x ∧
             l0_ffi_fn n' conf (MAP FST bs) x = SOME (FFIreturn (MAP SND bs) u)
Proof
  Induct >> simp[efaithful_def] >> rpt gen_tac >> strip_tac >> Cases_on ‘i’ >> gvs[]
  >- metis_tac[]
  >> drule_all l0_ffi_fn_length >> strip_tac >> first_x_assum drule_all >> simp[]
QED
