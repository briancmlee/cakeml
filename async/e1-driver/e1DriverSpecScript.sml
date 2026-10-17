(*
  The CF specs of the E1 driver's code (e1DriverProg) against E1's model
  (honestL1EPModel), stated as honestL1PFSpec's are: if the model's step
  returns SOME (results, (w', es'), events), the code, from L0_EV w0 w evs,
  returns the same results and state and ends in L0_EV w0 w' (evs ++
  events).
*)
Theory e1DriverSpec
Ancestors
  ml_translator cfHeapsBase mlstring endpointHLModel
  honestL0 honestL0World honestL1Model honestL1PFModel honestL1EPModel honestL0Part
  honestL0Prog honestL0Proof honestL0WorldProps honestL1PFProg honestL1PFSpec e1TypesProg e1DriverProg
  ffiSpikeSocketFFI cfDiv
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "e1DriverProg";
val st = get_ml_prog_state ();

Overload L1P = “HONESTL1PFMODEL_L1P_TYPE”
Overload L1E = “HONESTL1EPMODEL_L1E_TYPE”
Overload EACT = “ENDPOINTHLMODEL_EACT_TYPE”
Overload ERESP = “ENDPOINTHLMODEL_ERESP_TYPE”

(* ------------------------------------------------------------------------
   The calls
   ------------------------------------------------------------------------ *)

Theorem c_connect_spec:
  NUM a av ∧ sys_connect a w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_connect_v [av] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "c_connect_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec L0_connect_spec >> xsimpl >>
      gvs[sys_connect_def, bytes_str_bytes_to_str] >> metis_tac[]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

Theorem c_connerr_spec:
  WORD f fv ∧ sys_connerr f w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_connerr_v [fv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "c_connerr_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec L0_connerr_spec >> xsimpl >>
      gvs[sys_connerr_def, bytes_str_bytes_to_str] >> metis_tac[]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* The precondition's world is reachable: assume it *)
Theorem app_L0_EV_reach:
  args ≠ [] ∧ (l0_reach w0 w ⇒ app (p:'ffi ffi_proj) f args (L0_EV w0 w evs) Q) ⇒
  app p f args (L0_EV w0 w evs) Q
Proof
  Cases_on ‘l0_reach w0 w’ >> simp[L0_EV_def] >> rpt strip_tac >> xpull >>
  irule cfAppTheory.app_local >> simp[]
QED

(* A call's answer has the buffer's length *)
Theorem l0_do_length:
  l0_reach w0 w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒ LENGTH out = alen
Proof
  rw[l0_do_def, AllCaseEqs(), l0_reach_def] >> drule_all l0_ffi_fn_length >> simp[]
QED

(* res_val reads 8 bytes of a full header *)
Theorem res_val_side_13[local]:
  LENGTH out = 13 ⇒ res_val_side out
Proof
  rw[listTheory.LENGTH_EQ_NUM_compute] >>
  simp[fetch "e1DriverProg" "res_val_side_def", fetch "honestL1PFProg" "w82n_side_def",
       mllistTheory.take_def, mllistTheory.drop_def]
QED

Theorem conn_upd_side_13[local]:
  LENGTH out = 13 ⇒ conn_upd_side lfd out es
Proof
  simp[fetch "e1DriverProg" "conn_upd_side_def", res_val_side_13]
QED

(* ------------------------------------------------------------------------
   The model's edo, as the code splits it
   ------------------------------------------------------------------------ *)

Theorem l1e_p_id[local,simp]:
  (es : l1e) with p := es.p = es
Proof
  simp[honestL1EPModelTheory.l1e_component_equality]
QED

Theorem edo_EAccept_split:
  edo lfd pol (w, es) (EAccept l) = SOME (r, (w', es'), evs1) ⇒
  w' = w ∧ evs1 = [] ∧
  (pacc lfd es.p = NONE ∧ r = EAccepted NONE ∧ es' = es ∨
   ∃h ps1. pacc lfd es.p = SOME (h, ps1) ∧ r = EAccepted (SOME h) ∧ es' = set_p es ps1)
Proof
  simp[edo_def] >> strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
  drule pdo_Accept_split >> rw[] >> gvs[set_p_def]
QED

Theorem edo_EConnect_split:
  edo lfd pol (w, es) (EConnect a) = SOME (r, (w', es'), evs1) ⇒
  a < 65536 ∧
  ∃out ev. sys_connect a w = SOME (out, w', ev) ∧ conn_upd lfd out es = (es', r) ∧
           evs1 = [ev]
Proof
  rw[edo_def, AllCaseEqs()] >> gvs[conn_upd_def, conn_stat_def] >>
  rpt (pop_assum mp_tac) >> rw[] >> gvs[] >>
  Cases_on ‘l0_res_of out’ >> gvs[] >> rename1 ‘Fail e _’ >> Cases_on ‘e’ >> gvs[]
QED

Theorem edo_ERead_split:
  edo lfd pol (w, es) (ERead h n) = SOME (r, (w', es'), evs1) ⇒
  (∃f. ec_lookup es h = SOME f ∧
       (ec_refused es f ∧
        (∃out ev. sys_close f w = SOME (out, w', ev) ∧ es' = ec_close_upd h f es ∧
                  r = ERefused ∧ evs1 = [ev]) ∨
        ¬ec_refused es f ∧ es' = es ∧ r = EGot NONE ∧ w' = w ∧ evs1 = [])) ∨
  (ec_lookup es h = NONE ∧
   ((∃ro ps1. pread_step es.p h n = RkGot ro ps1 ∧ r = EGot ro ∧ es' = set_p es ps1 ∧
              w' = w ∧ evs1 = []) ∨
    (∃f ps0 out ev. pread_step es.p h n = RkClose f ps0 ∧
       sys_close f w = SOME (out, w', ev) ∧ es' = set_p es (pclose_upd f ps0) ∧
       r = EGot (SOME []) ∧ evs1 = [ev])))
Proof
  simp[edo_def, AllCaseEqs(), ec_lookup_def, ec_refused_def] >> strip_tac >>
  gvs[l1_close_def, AllCaseEqs(), ec_close_upd_def] >>
  PairCases_on ‘z’ >> gvs[] >>
  drule pdo_Read_split >> rw[] >> gvs[set_p_def]
QED

Theorem edo_EWrite_split:
  edo lfd pol (w, es) (EWrite h bs) = SOME (r, (w', es'), evs1) ⇒
  (∃f. ec_lookup es h = SOME f ∧ es' = es ∧ r = EWrote 0 ∧ w' = w ∧ evs1 = []) ∨
  (ec_lookup es h = NONE ∧ r = ewrite_resp es h bs ∧
   ((∃ps1. pwrite_step es.p h bs = WkDone ps1 ∧ es' = set_p es ps1 ∧ w' = w ∧ evs1 = []) ∨
    (∃f out ev. pwrite_step es.p h bs = WkSend f ∧ sys_send f bs w = SOME (out, w', ev) ∧
       es' = set_p es (psend_upd f bs out es.p) ∧ evs1 = [ev])))
Proof
  simp[edo_def, AllCaseEqs(), ec_lookup_def] >> strip_tac >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  drule pdo_Write_split >> rw[] >> gvs[set_p_def, ewrite_resp_def]
QED

(* ------------------------------------------------------------------------
   One action, the round's actions
   ------------------------------------------------------------------------ *)

(* Match, bind, and build the answer: the pure parts of a branch *)
val drive_tac =
  rpt (xmatch ORELSE (xlet_auto >- (TRY xcon >> xsimpl))) >>
  xcon >> xsimpl >>
  gvs[ENDPOINTHLMODEL_ERESP_TYPE_def, std_preludeTheory.OPTION_TYPE_def, PAIR_TYPE_def, e_p_def,
      LIST_TYPE_def];

Theorem edo_EAccept_spec[local]:
  edo lfd pol (w, es) (EAccept l) = SOME (r, (w', es'), evs1) ∧
  WORD lfd lfdv ∧ L1E es esv ∧ EACT (EAccept l) av ⇒
  app (p:'ffi ffi_proj) edo_v [lfdv; esv; av] (L0_EV w0 w evs)
    (POSTv v. &(∃esv' rv. v = Conv NONE [esv'; rv] ∧ L1E es' esv' ∧ ERESP r rv) *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "edo_v_def") >>
  gvs[ENDPOINTHLMODEL_EACT_TYPE_def] >> xmatch >>
  drule edo_EAccept_split >> strip_tac >> gvs[] >>
  rpt (xlet_auto >- xsimpl) >>
  gvs[e_p_def, std_preludeTheory.OPTION_TYPE_def, PAIR_TYPE_def] >> drive_tac
QED

Theorem edo_ERead_spec[local]:
  edo lfd pol (w, es) (ERead h n) = SOME (r, (w', es'), evs1) ∧
  WORD lfd lfdv ∧ L1E es esv ∧ EACT (ERead h n) av ⇒
  app (p:'ffi ffi_proj) edo_v [lfdv; esv; av] (L0_EV w0 w evs)
    (POSTv v. &(∃esv' rv. v = Conv NONE [esv'; rv] ∧ L1E es' esv' ∧ ERESP r rv) *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "edo_v_def") >>
  gvs[ENDPOINTHLMODEL_EACT_TYPE_def] >> xmatch >>
  drule edo_ERead_split >> strip_tac >> gvs[] >>
  (xlet_auto >- xsimpl) >> gvs[e_p_def, std_preludeTheory.OPTION_TYPE_def] >> xmatch
  >- (xlet_auto >- xsimpl >> xif >> qexists_tac ‘T’ >> simp[] >>
      xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev])’
      >- (xapp_spec c_close_spec >> xsimpl >> metis_tac[]) >>
      drive_tac)
  >- (xlet_auto >- xsimpl >> xif >> qexists_tac ‘F’ >> simp[] >> drive_tac)
  >> (xlet_auto >- xsimpl) >> (xlet_auto >- xsimpl)
  >- (gvs[e_p_def, fetch "honestL1PFProg" "HONESTL1PFPROG_RSTEP_TYPE_def"] >> xmatch >> drive_tac) >>
  gvs[e_p_def, fetch "honestL1PFProg" "HONESTL1PFPROG_RSTEP_TYPE_def"] >> xmatch >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec c_close_spec >> xsimpl >> metis_tac[]) >>
  drive_tac
QED

Theorem edo_EWrite_spec[local]:
  edo lfd pol (w, es) (EWrite h bs) = SOME (r, (w', es'), evs1) ∧
  WORD lfd lfdv ∧ L1E es esv ∧ EACT (EWrite h bs) av ⇒
  app (p:'ffi ffi_proj) edo_v [lfdv; esv; av] (L0_EV w0 w evs)
    (POSTv v. &(∃esv' rv. v = Conv NONE [esv'; rv] ∧ L1E es' esv' ∧ ERESP r rv) *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "edo_v_def") >>
  gvs[ENDPOINTHLMODEL_EACT_TYPE_def] >> xmatch >>
  drule edo_EWrite_split >> strip_tac >> gvs[] >>
  (xlet_auto >- xsimpl) >> gvs[e_p_def, std_preludeTheory.OPTION_TYPE_def] >> xmatch
  >- drive_tac >>
  (xlet_auto >- xsimpl) >> (xlet_auto >- xsimpl)
  >- (gvs[e_p_def, fetch "honestL1PFProg" "HONESTL1PFPROG_WSTEP_TYPE_def"] >> xmatch >> drive_tac) >>
  gvs[e_p_def, fetch "honestL1PFProg" "HONESTL1PFPROG_WSTEP_TYPE_def"] >> xmatch >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec c_send_spec >> xsimpl >> metis_tac[]) >>
  drive_tac
QED

Theorem edo_EConnect_spec[local]:
  edo lfd pol (w, es) (EConnect a) = SOME (r, (w', es'), evs1) ∧
  WORD lfd lfdv ∧ L1E es esv ∧ EACT (EConnect a) av ⇒
  app (p:'ffi ffi_proj) edo_v [lfdv; esv; av] (L0_EV w0 w evs)
    (POSTv v. &(∃esv' rv. v = Conv NONE [esv'; rv] ∧ L1E es' esv' ∧ ERESP r rv) *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >> irule app_L0_EV_reach >> simp[] >> strip_tac >>
  xcf_with_def (fetch "e1DriverProg" "edo_v_def") >>
  gvs[ENDPOINTHLMODEL_EACT_TYPE_def] >> xmatch >>
  drule edo_EConnect_split >> strip_tac >> gvs[] >>
  ‘LENGTH out = 13’ by (gvs[sys_connect_def] >> drule_all l0_do_length >> simp[]) >>
  (xlet_auto >- xsimpl) >> xif >> qexists_tac ‘F’ >> simp[] >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec c_connect_spec >> xsimpl >> metis_tac[]) >>
  xapp >> xsimpl >> qexistsl [‘out’, ‘lfd’, ‘es’] >> simp[conn_upd_side_13] >>
  rpt strip_tac >> gvs[PAIR_TYPE_def]
QED

Theorem edo_ELevel_spec[local]:
  edo lfd pol (w, es) (ELevel h) = SOME (r, (w', es'), evs1) ∧
  WORD lfd lfdv ∧ L1E es esv ∧ EACT (ELevel h) av ⇒
  app (p:'ffi ffi_proj) edo_v [lfdv; esv; av] (L0_EV w0 w evs)
    (POSTv v. &(∃esv' rv. v = Conv NONE [esv'; rv] ∧ L1E es' esv' ∧ ERESP r rv) *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "edo_v_def") >>
  gvs[ENDPOINTHLMODEL_EACT_TYPE_def] >> xmatch >>
  gvs[edo_def] >> drive_tac
QED

Theorem edo_spec:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs1) ∧
  WORD lfd lfdv ∧ L1E es esv ∧ EACT a av ⇒
  app (p:'ffi ffi_proj) edo_v [lfdv; esv; av] (L0_EV w0 w evs)
    (POSTv v. &(∃esv' rv. v = Conv NONE [esv'; rv] ∧ L1E es' esv' ∧ ERESP r rv) *
              L0_EV w0 w' (evs ++ evs1))
Proof
  Cases_on ‘a’ >>
  metis_tac[edo_EAccept_spec, edo_ERead_spec, edo_EWrite_spec, edo_EConnect_spec,
            edo_ELevel_spec]
QED

Theorem eacts_spec:
  ∀acts es w rs evs1 w' es' esv actsv evs.
    eacts lfd pol (w, es) acts = SOME (rs, evs1, (w', es')) ∧
    WORD lfd lfdv ∧ L1E es esv ∧ LIST_TYPE EACT acts actsv ⇒
    app (p:'ffi ffi_proj) eacts_v [lfdv; esv; actsv] (L0_EV w0 w evs)
      (POSTv v. &(∃esv' rsv. v = Conv NONE [esv'; rsv] ∧ L1E es' esv' ∧
                             LIST_TYPE ERESP rs rsv) *
                L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >>
  xcf_with_def (fetch "e1DriverProg" "eacts_v_def") >>
  gvs[LIST_TYPE_def, eacts_def] >> xmatch
  >- (xlet_auto >- (xcon >> xsimpl) >> xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  xlet ‘POSTv v. &(∃esv' rv. v = Conv NONE [esv'; rv] ∧ L1E ws11 esv' ∧ ERESP r rv) *
                 L0_EV w0 ws10 (evs ++ evs1')’
  >- (xapp_spec edo_spec >> xsimpl >> metis_tac[]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &(∃esv' rsv. v = Conv NONE [esv'; rsv] ∧ L1E es' esv' ∧
                              LIST_TYPE ERESP rs' rsv) *
                 L0_EV w0 w' (evs ++ evs1' ++ evs')’
  >- (first_x_assum drule >> disch_then drule >> strip_tac >> xapp >> xsimpl >>
      metis_tac[]) >>
  gvs[] >> xmatch >>
  xlet_auto >- (xcon >> xsimpl) >> xcon >> xsimpl >> simp[LIST_TYPE_def]
QED

(* ------------------------------------------------------------------------
   The round's tail
   ------------------------------------------------------------------------ *)

Overload FLOG = “HONESTL1PFMODEL_FETCHED_TYPE”
Overload L1ST = “HONESTL1MODEL_L1ST_TYPE”
Overload REV = “HONESTL0_REVENTS_TYPE”

(* The tail of a fetch: the recursive call, then this fd's log entry in
   front of the call's log (honestL1PFSpec's) *)
fun fetch_tail_tac log_def =
  qmatch_asmsub_rename_tac ‘pf_fetch _ _ _ (w1, _) = SOME ((_, _), lg, ee)’ >>
  first_x_assum drule >> strip_tac >>
  (xlet ‘POSTv v. &(∃psv' lv. v = Conv NONE [psv'; lv] ∧ L1P ps' psv' ∧
                              LIST_TYPE FLOG lg lv) *
                  L0_EV w0 w' (evs ++ [ev] ++ ee)’
   >- (xapp >> simp[])) >>
  gvs[] >> xmatch >> rpt (xlet_auto >- xsimpl) >>
  xcon >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> xsimpl >> gvs[log_def];

(* The fetch, for a general pause policy pol *)
Theorem pf_fetch_p_spec:
  ∀fs w ps w' ps' log evs1 fsv psv evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs1) ∧
    WORD lfd lfdv ∧ (L1P --> WORD --> BOOL) pol polv ∧
    LIST_TYPE WORD fs fsv ∧ L1P ps psv ⇒
    app (p:'ffi ffi_proj) pf_fetch_p_v [lfdv; polv; fsv; psv] (L0_EV w0 w evs)
      (POSTv v. &(∃psv' lv. v = Conv NONE [psv'; lv] ∧ L1P ps' psv' ∧ LIST_TYPE FLOG log lv) *
                L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >>
  xcf_with_def (fetch "e1DriverProg" "pf_fetch_p_v_def") >>
  gvs[LIST_TYPE_def, pf_fetch_def] >> xmatch
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  rpt (xlet_auto >- xsimpl) >> xif
  >- (gvs[] >> first_x_assum drule >> strip_tac >> xapp >> fs[]) >>
  gvs[] >> xlet_auto >- xsimpl >> xif
  >- (gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
      (xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w1 (evs ++ [ev])’
       >- (xapp_spec c_accept_spec >> xsimpl >> metis_tac[])) >>
      (xlet_auto >- xsimpl) >> gvs[fetch_acc_upd_def] >>
      fetch_tail_tac fetch_acc_log_def) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt (xlet_auto >- xsimpl) >>
  (xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w1 (evs ++ [ev])’
   >- (xapp_spec c_recv_spec >> xsimpl >> qexistsl [‘h’, ‘pf_chunk’] >>
       simp[fetch "honestL1PFProg" "pf_chunk_v_thm"])) >>
  (xlet_auto >- xsimpl) >> gvs[fetch_recv_upd_def] >>
  fetch_tail_tac fetch_recv_log_def
QED

Theorem settle_upd_side_13[local]:
  LENGTH out = 13 ⇒ settle_upd_side f out es
Proof
  simp[fetch "e1DriverProg" "settle_upd_side_def", res_val_side_13]
QED

Theorem settle_fds_c_spec:
  ∀fs w es w' es' evs1 fsv esv evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs1) ∧
    LIST_TYPE WORD fs fsv ∧ L1E es esv ⇒
    app (p:'ffi ffi_proj) settle_fds_c_v [fsv; esv] (L0_EV w0 w evs)
      (POSTv v. &L1E es' v * L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >> irule app_L0_EV_reach >> simp[] >> strip_tac >>
  xcf_with_def (fetch "e1DriverProg" "settle_fds_c_v_def") >>
  gvs[LIST_TYPE_def, settle_fds_def] >> xmatch
  >- (xvar >> xsimpl) >>
  gvs[AllCaseEqs()] >>
  ‘LENGTH out = 13’ by (gvs[sys_connerr_def] >> drule_all l0_do_length >> simp[]) >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w1 (evs ++ [ev])’
  >- (xapp_spec c_connerr_spec >> xsimpl >> metis_tac[]) >>
  xlet ‘POSTv v. &L1E (settle_upd h out es) v * L0_EV w0 w1 (evs ++ [ev])’
  >- (xapp >> xsimpl >> qexistsl [‘out’, ‘h’, ‘es’] >> simp[settle_upd_side_13]) >>
  gvs[GSYM settle_upd_def] >> first_x_assum drule >> strip_tac >> xapp >>
  qexistsl [‘emp’, ‘evs ++ [ev]’] >> xsimpl >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> xsimpl
QED

Theorem etail_spec:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs1) ∧
  WORD lfd lfdv ∧ (L1P --> WORD --> BOOL) pol polv ∧
  LIST_TYPE WORD hs hsv ∧ L1E es esv ⇒
  app (p:'ffi ffi_proj) etail_v [lfdv; polv; hsv; esv] (L0_EV w0 w evs)
    (POSTv v. &(∃rdyv esv'. v = Conv NONE [rdyv; esv'] ∧
                            LIST_TYPE WORD rdy rdyv ∧ L1E es' esv') *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "e1DriverProg" "etail_v_def") >>
  gvs[etail_def, AllCaseEqs(), GSYM etail_fes_def] >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE (LIST_TYPE (PAIR_TYPE WORD NUM))
                   ([] : (word64 # num) list list) v * L0_EV w0 w evs’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xlet ‘POSTv v. &LIST_TYPE (LIST_TYPE (PAIR_TYPE WORD NUM))
                   [etail_fes lfd pol es hs] v * L0_EV w0 w evs’
  >- (xcon >> xsimpl >> fs[LIST_TYPE_def]) >>
  xlet ‘POSTv v. &LIST_TYPE (PAIR_TYPE WORD REV) rv v * L0_EV w0 w1 (evs ++ pevs)’
  >- (xapp_spec l1_polls_spec >> xsimpl >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &L1ST b2 v * L0_EV w0 w2 (evs ++ pevs ++ fevs)’
  >- (xapp_spec l1_flush_spec >> xsimpl >> gvs[l1p_b_def, e_p_def] >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &(∃psv' lv. v = Conv NONE [psv'; lv] ∧ L1P ps3' psv' ∧ LIST_TYPE FLOG log lv) *
                 L0_EV w0 w3 (evs ++ pevs ++ fevs ++ gevs)’
  >- (xapp_spec pf_fetch_p_spec >> xsimpl >>
      gvs[filter_in_def, set_b_def, e_p_def] >> metis_tac[]) >>
  gvs[] >> xmatch >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &L1ST b4 v * L0_EV w0 w4 (evs ++ pevs ++ fevs ++ gevs ++ cevs)’
  >- (xapp_spec l1_reap_spec >> xsimpl >>
      gvs[l1p_b_def, closing_of_def, stall_step_ob_def, e_p_def] >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &L1E es5 v * L0_EV w0 w' (evs ++ pevs ++ fevs ++ gevs ++ cevs ++ sevs)’
  >- (xapp_spec settle_fds_c_spec >> xsimpl >>
      gvs[es_end_def, end_round_def, stall_step_ob_def, l1p_b_def, e_p_def,
          ready_pend_def] >> metis_tac[]) >>
  xapp >> xsimpl >> gvs[etail_fin_def, PAIR_TYPE_def] >> metis_tac[]
QED
