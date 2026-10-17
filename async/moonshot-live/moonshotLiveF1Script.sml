(*
  PROVISIONAL Q-16(b).  Moonshot liveness: the F1 TRANSFER (README §6):
  the run's per-process fairness F1_sys / F1_connect_sys / F1_poll_sys
  gives F1_io on the process's L0 trace tr (the form the programs' live
  claims take: clientLiveCopy's verbatim copy of honestL1BStmts.F1_io).

  F1_sys keys a call by bytes_fd (TAKE 8 conf) with 8 ≤ LENGTH conf, so it
  says nothing about polls (LENGTH conf = 1): F1_io keys a poll by the fds
  in its buffer (call_fds).  Q-16 option (b): a separate hypothesis
  F1_poll_sys keyed by the polled fds (precedent F1_connect_sys, D41 (2)).
  It is NOT in moonshot_live_hyps until the user rules on Q-16; if Q-16
  goes (a) (F1_sys re-keyed by call_fds), only F1_io_of_sys's plug-in of
  F1_poll_sys changes.

  The other names:
   - a connect's conf has 2 bytes, so its F1_io key bytes_fd (TAKE 8 conf)
     is w82n of a 2-byte list: one unspecified value for every connect
     (w82n_short).  F1_connect_sys is keyed by port (w22n conf < 65536), so
     some port is connected to infinitely often (io_pigeon) and
     F1_connect_sys at that port gives the unretried connects;
   - a listen is never retried unless one failed (listen_failed, in
     sys_excuse);
   - an fdok's answer is one byte, never a result dec_res decodes, so it
     is never retried;
   - every other call has 8 ≤ LENGTH conf: F1_sys.
  The decode lemma poll_dec (a poll's answer always decodes) is needed
  because retried reads an undecodable answer as a failure (l0_res_of)
  and retried_lab does not.

  MAIN: F1_io_of_sys.
*)
Theory moonshotLiveF1
Ancestors
  moonshotLiveExcuse moonshotLiveWorldDrains moonshotLiveStmts l0sysFair l0sys l0sysProj
  clientLiveCopy honestL1PFRound honestL1Model honestL0World honestL0Rely honestL0 Marshalling llist
Libs
  preamble

(* PROVISIONAL Q-16(b): F1 for polls, keyed by the polled fds *)
Definition F1_poll_sys_def:
  F1_poll_sys (S : dec list list) (rs : num -> syslabel) ⇔
    ∀k f. k < LENGTH S ∧
          io (λn. ∃conf b out. rs n = Call k «sys_poll» conf b out ∧
                               MEM f (MAP pe_fd (pollfd_entries (DROP 16 b)))) ⇒
          io (λn. ∃conf b out. rs n = Call k «sys_poll» conf b out ∧
                               MEM f (MAP pe_fd (pollfd_entries (DROP 16 b))) ∧ ¬retried_lab (rs n))
End

(*---------------------------------------------------------------------------*)
(* Positions of tr are k's calls *)

(* As moonshotLiveClaims.lprefix_lnth *)
Theorem lnth_prefix_el:
  LPREFIX (fromList evs) tr ∧ n < LENGTH evs ⇒ LNTH n tr = SOME (EL n evs)
Proof
  rw[LPREFIX_fromList] >> every_case_tac >> gvs[]
  >- (irule LTAKE_LNTH_EL >> metis_tac[]) >>
  ‘LFINITE tr’ by (CCONTR_TAC >> gvs[toList]) >>
  ‘tr = fromList x’ by metis_tac[to_fromList, THE_DEF] >>
  gvs[LNTH_fromList] >> imp_res_tac IS_PREFIX_LENGTH >>
  ‘n < LENGTH x’ by simp[] >> simp[] >> metis_tac[is_prefix_el]
QED

Theorem ptr_el_call:
  ∀t i. i < LENGTH (ptr rs k t) ⇒
        ∃n nm conf bts out. n < t ∧ rs n = Call k nm conf bts out ∧ LENGTH (ptr rs k n) = i ∧
                            EL i (ptr rs k t) = IO_event (ExtCall nm) conf (ZIP (bts, out))
Proof
  Induct >- simp[ptr_def, proc_events_def] >>
  rpt strip_tac >> Cases_on ‘i < LENGTH (ptr rs k t)’
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [‘n’, ‘nm’, ‘conf’, ‘bts’, ‘out’] >> simp[ptr_SUC, EL_APPEND1]) >>
  qpat_x_assum ‘i < LENGTH (ptr rs k (SUC t))’ mp_tac >> simp[ptr_len_SUC] >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  ‘i = LENGTH (ptr rs k t)’ by simp[] >> fs[is_kcall_def] >>
  qexists_tac ‘t’ >> simp[ptr_SUC, EL_APPEND2]
QED

Theorem call_lnth:
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ rs n = Call k nm conf bts out ⇒
  LNTH (LENGTH (ptr rs k n)) tr = SOME (IO_event (ExtCall nm) conf (ZIP (bts, out)))
Proof
  strip_tac >>
  ‘LNTH (LENGTH (ptr rs k n)) tr = SOME (EL (LENGTH (ptr rs k n)) (ptr rs k (SUC n)))’
    by (irule lnth_prefix_el >> conj_tac >>
        FIRST [first_assum (qspec_then ‘SUC n’ ACCEPT_TAC), fs[ptr_len_SUC, is_kcall_def]]) >>
  pop_assum SUBST1_TAC >> fs[ptr_SUC, EL_APPEND2]
QED

(* "Infinitely often on tr" is "infinitely often on k's calls" *)
Theorem io_tr_lab:
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ⇒
  ((∀i. ∃i' ev. i ≤ i' ∧ LNTH i' tr = SOME ev ∧ P ev) ⇔
   io (λn. ∃nm conf bts out. rs n = Call k nm conf bts out ∧
                             P (IO_event (ExtCall nm) conf (ZIP (bts, out)))))
Proof
  strip_tac >>
  ‘∀t t'. t ≤ t' ⇒ LENGTH (ptr rs k t) ≤ LENGTH (ptr rs k t')’
    by (rpt strip_tac >> drule ptr_mono >> disch_then (qspecl_then [‘rs’, ‘k’] strip_assume_tac) >>
        simp[]) >>
  ‘∀m. ∃t. LENGTH (ptr rs k t) = m’ by (irule ptr_len_hits >> first_assum ACCEPT_TAC) >>
  eq_tac >> rw[io_def]
  >- (qpat_x_assum ‘∀i. ∃i' ev. _’ (qspec_then ‘LENGTH (ptr rs k n0)’ strip_assume_tac) >>
      qpat_x_assum ‘∀m. ∃t. LENGTH _ = m’ (qspec_then ‘SUC i'’ strip_assume_tac) >>
      ‘i' < LENGTH (ptr rs k t)’ by simp[] >>
      ‘LNTH i' tr = SOME (EL i' (ptr rs k t))’
        by (irule lnth_prefix_el >> conj_tac >>
            FIRST [first_assum ACCEPT_TAC, first_assum (qspec_then ‘t’ ACCEPT_TAC)]) >>
      drule ptr_el_call >> strip_tac >>
      qexists_tac ‘n’ >> conj_tac
      >- (CCONTR_TAC >>
          ‘SUC n ≤ n0’ by simp[] >>
          ‘LENGTH (ptr rs k (SUC n)) ≤ LENGTH (ptr rs k n0)’ by (first_x_assum irule >> simp[]) >>
          ‘is_kcall k (rs n)’ by simp[is_kcall_def] >>
          fs[ptr_len_SUC]) >>
      qexistsl_tac [‘nm’, ‘conf’, ‘bts’, ‘out’] >> gvs[]) >>
  qmatch_goalsub_rename_tac ‘jj ≤ _’ >>
  qpat_x_assum ‘∀m. ∃t. LENGTH _ = m’ (qspec_then ‘jj’ (qx_choose_then ‘t0’ assume_tac)) >>
  qpat_x_assum ‘∀n0. ∃n. n0 ≤ n ∧ _’ (qspec_then ‘t0’ (qx_choose_then ‘n1’ strip_assume_tac)) >>
  qexistsl_tac [‘LENGTH (ptr rs k n1)’, ‘IO_event (ExtCall nm) conf (ZIP (bts, out))’] >>
  rpt conj_tac
  >- (‘LENGTH (ptr rs k t0) ≤ LENGTH (ptr rs k n1)’ by (first_x_assum irule >> simp[]) >> gvs[])
  >- (irule call_lnth >> conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Theorem io_mono:
  io P ∧ (∀n. P n ⇒ Q n) ⇒ io Q
Proof
  rw[io_def] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* The calls *)

Theorem call_shape:
  l0_call nm conf bts w = SOME (FFIreturn out w1) ⇒
  nm = «sys_poll» ∨ nm = «sys_connect» ∨ nm = «sys_listen» ∨ (nm = «sys_fdok» ∧ LENGTH out = 1) ∨
  (nm ≠ «sys_fdok» ∧ 8 ≤ LENGTH conf)
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs(), LET_THM, UNCURRY]
QED

(* The decode lemma: a poll's answer is a result *)
Theorem poll_dec:
  l0_rely w ∧ l0_call «sys_poll» conf bts w = SOME (FFIreturn out w1) ⇒ dec_res out ≠ NONE
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs(), LET_THM] >> every_case_tac >> gvs[] >>
  FIRST [simp[poll_out_def, enc_res_def, dec_res_def, LENGTH_n2w8] >> NO_TAC,
         ‘l0_res_ok (fail w e)’ by fs[fail_def, l0_res_ok_def, l0_rely_def] >>
         ‘∀rest. dec_res (enc_res (fail w e) ++ rest) = SOME (fail w e)’
           by (gen_tac >> irule dec_enc_res >> first_assum ACCEPT_TAC) >>
         simp[poll_failed_def, LET_THM] >> ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
         asm_rewrite_tac[] >> simp[]]
QED

Theorem fdok_dec:
  LENGTH out = 1 ⇒ dec_res out = NONE
Proof
  simp[dec_res_def]
QED

Theorem retried_lab_ev:
  LENGTH out = LENGTH bts ⇒
  (retried (IO_event (ExtCall nm) conf (ZIP (bts, out))) ⇔
   retried_lab (Call k nm conf bts out) ∨ (nm = «sys_poll» ∧ dec_res out = NONE))
Proof
  simp[retried_def, retried_lab_def, MAP_ZIP, l0_res_of_def] >> strip_tac >>
  Cases_on ‘dec_res out’ >> simp[l1_transient_def] >>
  rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[]
QED

Theorem ev_on_lab:
  LENGTH out = LENGTH bts ⇒
  (ev_on nm f (IO_event (ExtCall nm') conf (ZIP (bts, out))) ⇔ nm' = nm ∧ MEM f (call_fds nm conf bts))
Proof
  rw[ev_on_def, MAP_ZIP] >> eq_tac >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* F1 on k's calls, per name *)

Theorem listen_not_retried:
  ¬listen_failed rs k ∧ rs n = Call k «sys_listen» conf bts out ⇒ ¬retried_lab (rs n)
Proof
  rw[listen_failed_def, retried_lab_def] >> every_case_tac >> metis_tac[]
QED

Theorem fdok_not_retried:
  l0sys_irun ps ss rs ∧ rs n = Call k «sys_fdok» conf bts out ⇒ ¬retried_lab (rs n)
Proof
  strip_tac >> drule_all irun_call >> strip_tac >> drule call_shape >> simp[] >> strip_tac >>
  simp[retried_lab_def, fdok_dec]
QED

Theorem other_conf8:
  l0sys_irun ps ss rs ∧ rs n = Call k nm conf bts out ∧
  nm ≠ «sys_poll» ∧ nm ≠ «sys_connect» ∧ nm ≠ «sys_listen» ∧ nm ≠ «sys_fdok» ⇒
  8 ≤ LENGTH conf
Proof
  strip_tac >> drule_all irun_call >> strip_tac >> drule call_shape >> simp[unblock_def]
QED

Theorem poll_out_dec:
  l0sys_irun ps ss rs ∧ rs n = Call k «sys_poll» conf bts out ⇒ dec_res out ≠ NONE
Proof
  strip_tac >> drule_all irun_call >> strip_tac >> drule_all poll_dec >> simp[]
QED

Theorem F1_lab_poll:
  F1_poll_sys ps rs ∧ k < LENGTH ps ∧
  (∀n conf bts out. rs n = Call k «sys_poll» conf bts out ⇒ dec_res out ≠ NONE) ∧
  io (λn. ∃conf bts out. rs n = Call k «sys_poll» conf bts out ∧ MEM f (call_fds «sys_poll» conf bts)) ⇒
  io (λn. ∃conf bts out. rs n = Call k «sys_poll» conf bts out ∧ MEM f (call_fds «sys_poll» conf bts) ∧
                         ¬retried_lab (rs n) ∧ ¬(«sys_poll» = «sys_poll» ∧ dec_res out = NONE))
Proof
  rw[F1_poll_sys_def, call_fds_def] >>
  first_x_assum (qspecl_then [‘k’, ‘f’] mp_tac) >> simp[] >> strip_tac >>
  fs[io_def] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘n0’ strip_assume_tac) >>
  qexists_tac ‘n’ >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [‘conf’, ‘b’, ‘out’] >> asm_rewrite_tac[] >>
  qpat_x_assum ‘∀n conf bts out. _ ⇒ dec_res _ ≠ NONE’ irule >> metis_tac[]
QED

(* w82n is unspecified (one ARB) off 8-byte lists, so every connect has
   the same F1_io key.  REVIEW NOTE: F1_io keys a connect by
   bytes_fd (TAKE 8 conf), and a connect's conf has 2 bytes, so the key is
   this one unspecified value for every connect.  That is harmless: it
   collapses all of a process's connects into one key, so F1_io for
   connects reads "connects infinitely often ⇒ unretried connects
   infinitely often", which F1_connect_sys (keyed by port) gives through
   io_pigeon.  F1_io's definition is not changed here (orchestrator's
   reviewability item for F1_io's owner) *)
Theorem w82n_short:
  w82n [x1; x2] = w82n [y1; y2]
Proof
  ONCE_REWRITE_TAC [w82n_def_primitive] >>
  ‘WF (@R. WF (R : word8 list -> word8 list -> bool))’ by (SELECT_ELIM_TAC >> metis_tac[relationTheory.WF_EMPTY_REL]) >>
  pop_assum (fn th => ONCE_REWRITE_TAC [MATCH_MP relationTheory.WFREC_THM th]) >> simp[]
QED

Theorem w22n_lt:
  w22n [x1; x2] < 65536
Proof
  simp[w22n_def] >>
  ‘w2n x1 < 256 ∧ w2n x2 < 256’ by (conj_tac >> irule (INST_TYPE [alpha |-> “:8”] w2n_lt_256)) >>
  simp[]
QED

Theorem connect_conf2:
  l0sys_irun ps ss rs ∧ rs n = Call k «sys_connect» conf bts out ⇒ ∃x1 x2. conf = [x1; x2]
Proof
  strip_tac >> drule_all irun_call >> strip_tac >>
  fs[l0_call_def, unblock_def] >> gvs[AllCaseEqs(), LET_THM, UNCURRY] >>
  rename1 ‘LENGTH conf = 2’ >> Cases_on ‘conf’ >> fs[] >> Cases_on ‘t’ >> fs[]
QED

(* Pigeonhole: infinitely often with a value below M ⇒ one value infinitely often *)
Theorem io_pigeon:
  ∀M P. io P ∧ (∀n. P n ⇒ (g : num -> num) n < M) ⇒ ∃p. io (λn. P n ∧ g n = p)
Proof
  Induct
  >- (rpt strip_tac >> fs[io_def] >> first_x_assum (qspec_then ‘0’ strip_assume_tac) >> res_tac >> fs[]) >>
  rpt strip_tac >>
  Cases_on ‘io (λn. P n ∧ g n = M)’ >- (qexists_tac ‘M’ >> first_assum ACCEPT_TAC) >>
  pop_assum (strip_assume_tac o SIMP_RULE bool_ss [io_def, NOT_FORALL_THM, NOT_EXISTS_THM, DE_MORGAN_THM]) >>
  first_x_assum (qspec_then ‘λn. P n ∧ n0 ≤ n’ mp_tac) >> impl_tac
  >- (conj_tac
      >- (fs[io_def] >> gen_tac >> qpat_x_assum ‘∀n0. ∃n. n0 ≤ n ∧ P n’ (qspec_then ‘MAX n0 n0'’ strip_assume_tac) >>
          qexists_tac ‘n’ >> fs[MAX_LE]) >>
      rpt strip_tac >> fs[] >> res_tac >>
      ‘g n ≠ M’ by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]) >> simp[]) >>
  strip_tac >> qexists_tac ‘p’ >> irule io_mono >> qexists_tac ‘λn. (P n ∧ n0 ≤ n) ∧ g n = p’ >>
  fs[]
QED

Theorem F1_lab_connect:
  F1_connect_sys ps rs ∧ k < LENGTH ps ∧
  (∀n conf bts out. rs n = Call k «sys_connect» conf bts out ⇒ ∃x1 x2. conf = [x1; x2]) ∧
  io (λn. ∃conf bts out. rs n = Call k «sys_connect» conf bts out ∧
                         MEM f (call_fds «sys_connect» conf bts)) ⇒
  io (λn. ∃conf bts out. rs n = Call k «sys_connect» conf bts out ∧
                         MEM f (call_fds «sys_connect» conf bts) ∧
                         ¬retried_lab (rs n) ∧ ¬(«sys_connect» = «sys_poll» ∧ dec_res out = NONE))
Proof
  simp[F1_connect_sys_def, call_fds_def] >> strip_tac >>
  ‘∀n conf bts out. rs n = Call k «sys_connect» conf bts out ⇒
                    bytes_fd (TAKE 8 conf) = bytes_fd [0w; 0w] ∧ w22n conf < 65536’
    by (rpt gen_tac >> strip_tac >>
        qpat_x_assum ‘∀n conf bts out. _ ⇒ ∃x1 x2. _’ drule >> strip_tac >>
        simp[ffiSpikeSocketFFITheory.bytes_fd_def, w22n_lt] >> AP_THM_TAC >> AP_TERM_TAC >> MATCH_ACCEPT_TAC w82n_short) >>
  qabbrev_tac ‘g = λn. case rs n of Call _ _ conf _ _ => w22n conf | _ => 0’ >>
  qspecl_then [‘65536’, ‘λn. ∃conf bts out. rs n = Call k «sys_connect» conf bts out ∧
                                 f = bytes_fd (TAKE 8 conf)’]
    mp_tac (Q.GEN ‘g’ io_pigeon |> Q.SPEC ‘g’) >>
  impl_tac
  >- (conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
      simp[Abbr ‘g’] >> rpt strip_tac >> simp[] >> res_tac) >>
  disch_then (qx_choose_then ‘p’ (assume_tac o BETA_RULE)) >>
  qpat_x_assum ‘∀k p. _’ (qspecl_then [‘k’, ‘p’] mp_tac) >> impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      irule io_mono >> qexists_tac ‘λn. (∃conf bts out. rs n = Call k «sys_connect» conf bts out ∧
                                         f = bytes_fd (TAKE 8 conf)) ∧ g n = p’ >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      simp[Abbr ‘g’] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >> irule io_mono >>
  qexists_tac ‘λn. ∃conf b out. rs n = Call k «sys_connect» conf b out ∧ w22n conf = p ∧ ¬retried_lab (rs n)’ >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> rpt strip_tac >> qexistsl_tac [‘conf’, ‘b’, ‘out’] >> simp[] >>
  ‘∃n'. ∃conf' bts' out'. rs n' = Call k «sys_connect» conf' bts' out' ∧ f = bytes_fd (TAKE 8 conf')’
    by (qpat_x_assum ‘io (λn. (∃conf bts out. _) ∧ _)’ (strip_assume_tac o SIMP_RULE bool_ss [io_def]) >>
        pop_assum (qspec_then ‘0’ strip_assume_tac) >> metis_tac[]) >>
  metis_tac[]
QED

Theorem F1_lab_noretry:
  nm ≠ «sys_poll» ∧ (∀n conf bts out. rs n = Call k nm conf bts out ⇒ ¬retried_lab (rs n)) ∧
  io (λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts)) ⇒
  io (λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts) ∧
                         ¬retried_lab (rs n) ∧ ¬(nm = «sys_poll» ∧ dec_res out = NONE))
Proof
  rw[io_def] >> first_x_assum (qspec_then ‘n0’ strip_assume_tac) >>
  qexists_tac ‘n’ >> simp[] >> res_tac >> gvs[]
QED

Theorem F1_lab_sys:
  F1_sys ps rs ∧ k < LENGTH ps ∧ nm ≠ «sys_poll» ∧
  (∀n conf bts out. rs n = Call k nm conf bts out ⇒ 8 ≤ LENGTH conf) ∧
  io (λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts)) ⇒
  io (λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts) ∧
                         ¬retried_lab (rs n) ∧ ¬(nm = «sys_poll» ∧ dec_res out = NONE))
Proof
  rw[F1_sys_def, call_fds_def] >>
  first_x_assum (qspecl_then [‘k’, ‘nm’, ‘f’] mp_tac) >> simp[] >> impl_tac
  >- (fs[io_def] >> rpt strip_tac >> first_x_assum (qspec_then ‘n0’ strip_assume_tac) >>
      qexists_tac ‘n’ >> simp[] >> res_tac >> gvs[]) >>
  rw[io_def] >> first_x_assum (qspec_then ‘n0’ strip_assume_tac) >>
  qexists_tac ‘n’ >> simp[] >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* MAIN (PROVISIONAL Q-16(b)).  Connects: see the REVIEW NOTE at w82n_short (F1_io's
   connect key is one unspecified value, so it means "connects i.o. ⇒ unretried connects i.o.") *)

Theorem F1_io_of_sys:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧
  F1_sys ps rs ∧ F1_connect_sys ps rs ∧ F1_poll_sys ps rs ∧ ¬listen_failed rs k ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ⇒
  F1_io tr
Proof
  strip_tac >> rewrite_tac[F1_io_def] >> rpt gen_tac >>
  qspecl_then [‘k’, ‘rs’, ‘tr’, ‘ev_on nm f’] mp_tac (Q.GENL [‘k’, ‘rs’, ‘tr’, ‘P’] io_tr_lab) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then SUBST1_TAC >>
  qspecl_then [‘k’, ‘rs’, ‘tr’, ‘λev. ev_on nm f ev ∧ ¬retried ev’] mp_tac
    (Q.GENL [‘k’, ‘rs’, ‘tr’, ‘P’] io_tr_lab) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then (SUBST1_TAC o BETA_RULE) >>
  ‘∀n nm' conf bts out. rs n = Call k nm' conf bts out ⇒ LENGTH out = LENGTH bts’
    by (rpt strip_tac >> drule_all irun_call_len >> simp[]) >>
  ‘io (λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts)) ⇒
   io (λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts) ∧
                          ¬retried_lab (rs n) ∧ ¬(nm = «sys_poll» ∧ dec_res out = NONE))’
    suffices_by
      (strip_tac >> strip_tac >>
       ‘io (λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts))’
         by (irule io_mono >>
             qexists_tac ‘λn. ∃nm' conf bts out. rs n = Call k nm' conf bts out ∧
                                ev_on nm f (IO_event (ExtCall nm') conf (ZIP (bts, out)))’ >>
             reverse conj_tac >- first_assum ACCEPT_TAC >>
             simp[] >> rpt strip_tac >>
             qpat_assum ‘∀n nm' conf bts out. _ ⇒ LENGTH _ = _’ drule >> strip_tac >>
             gvs[ev_on_lab] >> metis_tac[]) >>
       qpat_x_assum ‘io (λn. ∃conf bts out. _ ∧ MEM _ _) ⇒ _’
         (fn th => first_assum (assume_tac o MATCH_MP th)) >>
       irule io_mono >>
       qexists_tac ‘λn. ∃conf bts out. rs n = Call k nm conf bts out ∧ MEM f (call_fds nm conf bts) ∧
                          ¬retried_lab (rs n) ∧ ¬(nm = «sys_poll» ∧ dec_res out = NONE)’ >>
       reverse conj_tac >- first_assum ACCEPT_TAC >>
       simp[] >> rpt strip_tac >>
       qpat_assum ‘∀n nm' conf bts out. _ ⇒ LENGTH _ = _’ drule >> strip_tac >>
       qexistsl_tac [‘nm’, ‘conf’, ‘bts’, ‘out’] >> simp[ev_on_lab] >>
       qpat_x_assum ‘LENGTH out = LENGTH bts’ (fn th => rewrite_tac[MATCH_MP retried_lab_ev th]) >>
       rpt strip_tac >- (qpat_x_assum ‘¬retried_lab _’ mp_tac >> asm_rewrite_tac[]) >>
       qpat_x_assum ‘nm = «sys_poll» ⇒ _’ drule >> asm_rewrite_tac[]) >>
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’
  >- (pop_assum SUBST_ALL_TAC >> irule F1_lab_poll >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, qexists_tac ‘ps’ >> rpt conj_tac >> first_assum ACCEPT_TAC,
             rpt strip_tac >> drule_all poll_out_dec >> asm_rewrite_tac[]]) >>
  Cases_on ‘nm = «sys_connect»’
  >- (pop_assum SUBST_ALL_TAC >> irule F1_lab_connect >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, qexists_tac ‘ps’ >> rpt conj_tac >> first_assum ACCEPT_TAC,
             rpt gen_tac >> strip_tac >> qpat_x_assum ‘l0sys_irun _ _ _’ mp_tac >> qpat_x_assum ‘rs n = _’ mp_tac >>
             rpt (pop_assum kall_tac) >> metis_tac[connect_conf2]]) >>
  Cases_on ‘nm = «sys_listen»’
  >- (pop_assum SUBST_ALL_TAC >> irule F1_lab_noretry >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
             rpt gen_tac >> strip_tac >> qpat_x_assum ‘¬listen_failed _ _’ mp_tac >> qpat_x_assum ‘rs n = _’ mp_tac >>
             rpt (pop_assum kall_tac) >> metis_tac[listen_not_retried]]) >>
  Cases_on ‘nm = «sys_fdok»’
  >- (pop_assum SUBST_ALL_TAC >> irule F1_lab_noretry >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
             rpt gen_tac >> strip_tac >> qpat_x_assum ‘l0sys_irun _ _ _’ mp_tac >> qpat_x_assum ‘rs n = _’ mp_tac >>
             rpt (pop_assum kall_tac) >> metis_tac[fdok_not_retried]]) >>
  irule F1_lab_sys >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, qexists_tac ‘ps’ >> rpt conj_tac >> first_assum ACCEPT_TAC,
         rpt strip_tac >> qpat_x_assum ‘l0sys_irun _ _ _’ mp_tac >> qpat_x_assum ‘rs n = _’ mp_tac >>
         qpat_x_assum ‘nm ≠ «sys_poll»’ mp_tac >> qpat_x_assum ‘nm ≠ «sys_connect»’ mp_tac >>
         qpat_x_assum ‘nm ≠ «sys_listen»’ mp_tac >> qpat_x_assum ‘nm ≠ «sys_fdok»’ mp_tac >>
         rpt (pop_assum kall_tac) >> metis_tac[other_conf8]]
QED
