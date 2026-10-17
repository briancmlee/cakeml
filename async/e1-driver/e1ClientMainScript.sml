(*
  The moonshot client's CakeML run (e1ClientProg's client_main) on the E1
  driver: client_main c a N (lits_enc bss), with bss connection i's request
  bytes brequests (rqs i) for i < N, runs e1_start c on the client's fold
  (cinit a N, cstep a rqs, clast, cifdsl, call_done; pol_never).

   - The reachable invariant: the client's state has N connections
     (CSTN N); the CakeML step, which reads the request bytes from bss
     (rqf: [] past the end), agrees with cstep a rqs on such states
     (cstepl_rqf).
   - mk_emk: client_main's mk meets the driver's EMK with these.
   - client_main_closed/nolisten/term/div_spec: e1_start's four outcomes,
     for client_main.
*)
Theory e1ClientMain
Ancestors
  ml_translator cfHeapsBase cfApp cfDiv endpointHLModel asyncCore asyncLevel1 asyncM3World
  honestL0 honestL0World honestL1Model honestL1PFModel honestL1EPModel honestL0Part
  honestL0Prog honestL0Proof honestL0Fdok honestL1PFProg honestL1PFSpec e1TypesProg
  e1DriverProg e1DriverSpec e1Fold e1DriverLoop e1DriverMain moonshotClient e1Lits e1ClientProg
Libs
  preamble ml_translatorLib ml_progLib cfLib cfDivLib basisFunctionsLib

val _ = translation_extends "e1ClientProg";
val st = get_ml_prog_state ();

Overload CST = “MOONSHOTCLIENT_CST_TYPE”
Overload EACT = “ENDPOINTHLMODEL_EACT_TYPE”
Overload ERESP = “ENDPOINTHLMODEL_ERESP_TYPE”
Overload L1P = “HONESTL1PFMODEL_L1P_TYPE”

(* ------------------------------------------------------------------------
   The invariant: N connections
   ------------------------------------------------------------------------ *)

(* A client state with N connections, as a CakeML value *)
Definition CSTN_def:
  CSTN N st v ⇔ CST st v ∧ LENGTH st.cs = N
End

(* The request bytes of connections 0..N-1 *)
Overload RQB = “λN rqs. GENLIST (λi. brequests (rqs i)) N”

Theorem lmod_LENGTH:
  ∀f i cs. LENGTH (lmod f i cs) = LENGTH cs
Proof
  Induct_on ‘cs’ >> rw[lmod_def]
QED

Theorem lmod_cong:
  ∀f g i cs. (i < LENGTH cs ⇒ f (EL i cs) = g (EL i cs)) ⇒ lmod f i cs = lmod g i cs
Proof
  Induct_on ‘cs’ >> rw[lmod_def] >> Cases_on ‘i’ >> gvs[]
QED

Theorem cupdf_LENGTH:
  ∀rq st xs rs. LENGTH (cupdf rq st xs rs).cs = LENGTH st.cs
Proof
  ho_match_mp_tac cupdf_ind >> rw[cupdf_def, lmod_LENGTH]
QED

Theorem cupdf_cong:
  ∀rq st xs rs. (∀i. i < LENGTH st.cs ⇒ rq i = rq' i) ⇒
                cupdf rq st xs rs = cupdf rq' st xs rs
Proof
  ho_match_mp_tac cupdf_ind >> rpt strip_tac >> REWRITE_TAC [cupdf_def] >>
  ‘lmod (λc. cres (rq i) c x r) i st.cs = lmod (λc. cres (rq' i) c x r) i st.cs’
    by (irule lmod_cong >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [GSYM th]) >>
  first_x_assum irule >> simp[lmod_LENGTH]
QED

Theorem cstepl_LENGTH:
  LENGTH (cstepl a rq st rdy rs).cs = LENGTH st.cs
Proof
  simp[cstepl_def, cupdf_LENGTH]
QED

Theorem cinitl_LENGTH:
  LENGTH (cinitl a N).cs = N
Proof
  simp[cinitl_def, cidles_eq]
QED

(* On a state with N connections, the CakeML step is cstep a rqs *)
Theorem cstepl_rqf:
  LENGTH st.cs = N ⇒
  cstepl a (rqf (RQB N rqs)) st rdy rs = cstep a rqs st (ssnap rdy rs)
Proof
  strip_tac >> simp[cstep_eq, cstepl_def] >>
  ‘cupdf (rqf (RQB N rqs)) st st.last rs = cupdf (λi. brequests (rqs i)) st st.last rs’
    by (irule cupdf_cong >> simp[rqf_eq]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Refining a translator certificate
   ------------------------------------------------------------------------ *)

Theorem Arrow_refine:
  (a --> b) f fv ∧ (∀x xv u. a' x xv ⇒ a x xv ∧ (b (f x) u ⇒ b' (g x) u)) ⇒
  (a' --> b') g fv
Proof
  rw[Arrow_def, AppReturns_def] >> metis_tac[]
QED

Theorem Arrow_refine_imp =
  Arrow_refine |> REWRITE_RULE [GSYM AND_IMP_INTRO];

Theorem Arrow_same:
  (a --> b) f fv ∧ (∀x xv. a' x xv ⇒ a x xv) ⇒ (a' --> b) f fv
Proof
  rw[] >> irule Arrow_refine >> metis_tac[]
QED

(* The step's certificate, on states with N connections *)
Theorem cstep_cert:
  (CST --> LIST_TYPE WORD --> LIST_TYPE ERESP --> CST) (cstepl a (rqf (RQB N rqs))) stepv ⇒
  (CSTN N --> LIST_TYPE WORD --> LIST_TYPE ERESP --> CSTN N)
    (λs rdy rs. cstep a rqs s (ssnap rdy rs)) stepv
Proof
  strip_tac >> pop_assum (irule o MATCH_MP Arrow_refine_imp) >>
  rw[CSTN_def] >> pop_assum (irule o MATCH_MP Arrow_refine_imp) >>
  rw[] >> pop_assum (irule o MATCH_MP Arrow_refine_imp) >>
  rw[CSTN_def, cstepl_rqf, cstepl_LENGTH] >> gvs[cstepl_rqf, cstep_eq, cstepl_LENGTH]
QED

(* Partial applications of translated functions *)
Theorem Arrow_app1:
  (a --> b) f fv ∧ a x xv ⇒
  app (p:'ffi ffi_proj) fv [xv] emp (POSTv v. &b (f x) v)
Proof
  rw[app_def] >> metis_tac[Arrow_IMP_app_basic]
QED

Theorem Arrow_app2:
  (a --> b --> c) f fv ∧ a x xv ∧ b y yv ⇒
  app (p:'ffi ffi_proj) fv [xv; yv] emp (POSTv v. &c (f x y) v)
Proof
  rw[app_def] >> drule_all Arrow_IMP_app_basic >>
  disch_then (qspec_then ‘p’ assume_tac) >>
  irule app_basic_weaken >> first_assum (irule_at Any) >>
  Cases >> simp[POSTv_def, cond_def, SEP_EXISTS_THM, STAR_def] >>
  strip_tac >> qexistsl [‘emp’, ‘∅’] >> simp[emp_def, SPLIT_def] >>
  drule_all Arrow_IMP_app_basic >> disch_then (qspec_then ‘p’ mp_tac) >>
  simp[POSTv_def, cond_def, emp_def]
QED

(* ------------------------------------------------------------------------
   mk_client's values
   ------------------------------------------------------------------------ *)

Theorem mk_client_spec:
  NUM a av ∧ NUM N nv ∧ LIST_TYPE (LIST_TYPE WORD) (RQB N rqs) bssv ∧ WORD lfd lfdv ⇒
  app (p:'ffi ffi_proj) mk_client_v [av; nv; bssv; lfdv] emp
    (POSTv v. &(∃polv ifdsv actsv stepv finv initv.
                  v = Conv NONE [polv; ifdsv; actsv; stepv; finv; initv] ∧
                  ECODE (CSTN N) lfd pol_never cifdsl clast (cstep a rqs) call_done
                    (Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]) ∧
                  CSTN N (cinit a N) initv))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1ClientProg" "mk_client_v_def") >>
  xlet ‘POSTv v. &CST (cinitl a N) v’ >- (xapp >> simp[]) >>
  xlet ‘POSTv v. &(NUM --> LIST_TYPE WORD8) (rqf (RQB N rqs)) v’
  >- (xapp_spec (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Arrow_app1) (fetch "e1ClientProg" "rqf_v_thm")) >> simp[]) >>
  xlet ‘POSTv v. &(CST --> LIST_TYPE (WORD : word64 -> v -> bool) --> LIST_TYPE ERESP --> CST)
                    (cstepl a (rqf (RQB N rqs))) v’
  >- (xapp_spec (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Arrow_app2) (fetch "e1ClientProg" "cstepl_v_thm")) >> simp[]) >>
  xcon >> xsimpl >>
  simp[ECODE_def, CSTN_def, cinit_eq, cinitl_LENGTH, cstep_cert,
       fetch "e1TypesProg" "pol_never_v_thm"] >>
  rpt conj_tac >> irule Arrow_same >> simp[CSTN_def] >>
  FIRST (map (fn th => qexists_tac ‘CST’ >> simp[th] >> NO_TAC)
             [fetch "e1ClientProg" "cifdsl_v_thm", fetch "e1ClientProg" "clast_v_thm",
              fetch "e1ClientProg" "call_done_v_thm"])
QED

(* ------------------------------------------------------------------------
   The client's fold is cprog (moonshotClient)
   ------------------------------------------------------------------------ *)

Theorem client_fold_state:
  FOLDL (cstep a rqs) (cinit a N) h = cstate a N rqs h
Proof
  simp[cstate_def]
QED

Theorem client_fold_ifds:
  fold_ifds (cinit a N) (cstep a rqs) cifdsl = cifds a N rqs
Proof
  simp[FUN_EQ_THM, fold_ifds_def, cifds_eq, cstate_def]
QED

Theorem client_fold_prog:
  fold_prog (cinit a N) (cstep a rqs) clast call_done = cprog a N rqs
Proof
  simp[FUN_EQ_THM, fold_prog_def, cprog_def, cstate_def, clast_def]
QED

(* ------------------------------------------------------------------------
   client_main
   ------------------------------------------------------------------------ *)

(* A driver spec with its state invariant ST := CSTN N (a type instance) *)
fun inst_cstn th =
  let val stv = find_term (fn t => is_var t andalso fst (dest_var t) = "ST") (concl th)
  in INST_TY_TERM (match_term stv “CSTN N”) th end;

Overload CLITS = “λN rqs. bytes_to_str (lits_enc (RQB N rqs))”

(* The driver specs with the client's fold substituted (λ_. constant in lfd),
   the fold rewritten to cifds / cprog / cstate *)
fun inst_client th =
  Q.INST [‘pol’ |-> ‘λ_. pol_never’, ‘ifds’ |-> ‘λ_. cifdsl’, ‘acts’ |-> ‘λ_. clast’,
          ‘step’ |-> ‘λ_. cstep a rqs’, ‘fin’ |-> ‘λ_. call_done’,
          ‘init’ |-> ‘λ_. cinit a N’] (inst_cstn th)
  |> BETA_RULE |> REWRITE_RULE [client_fold_ifds, client_fold_prog, client_fold_state];

val client_div_spec = inst_client e1_start_div_spec;

(* The startup: the request bytes decoded, mk defined, EMK for mk *)
val main_prefix_tac =
  rpt strip_tac >>
  xcf_with_def (fetch "e1ClientProg" "client_main_v_def") >>
  xlet ‘POSTv v. &LIST_TYPE WORD8 (lits_enc (RQB N rqs)) v * L0_EV w0 w []’
  >- (xapp >> qexistsl [‘L0_EV w0 w []’, ‘CLITS N rqs’] >>
      simp[str_to_bytes_bytes_to_str] >> xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE (LIST_TYPE WORD8) (RQB N rqs) v * L0_EV w0 w []’
  >- (xapp >> qexistsl [‘L0_EV w0 w []’, ‘lits_enc (RQB N rqs)’] >>
      simp[lits_dec_enc] >> xsimpl) >>
  xfun_spec ‘mk’
    ‘∀(lfd : word64) lfdv. WORD lfd lfdv ⇒
       app (p:'ffi ffi_proj) mk [lfdv] emp
         (POSTv v. &(∃polv ifdsv actsv stepv finv initv.
                       v = Conv NONE [polv; ifdsv; actsv; stepv; finv; initv] ∧
                       ECODE (CSTN N) lfd pol_never cifdsl clast (cstep a rqs) call_done
                         (Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]) ∧
                       CSTN N (cinit a N) initv))’
  >- (rpt strip_tac >> first_x_assum irule >> xapp_spec mk_client_spec >> simp[]) >>
  ‘EMK p (CSTN N) (λ_. pol_never) (λ_. cifdsl) (λ_. clast) (λ_. cstep a rqs) (λ_. call_done)
       (λ_. cinit a N) mk’
    by (simp[EMK_def] >> first_x_assum ACCEPT_TAC);

(* stdin, stdout or stderr closed: client_main returns after the fdok calls *)
Theorem client_main_closed_spec:
  NUM c cv ∧ NUM a av ∧ NUM N nv ∧ STRING_TYPE (CLITS N rqs) sv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ ¬fdok_all o0 o1 o2 ⇒
  app (p:'ffi ffi_proj) client_main_v [cv; av; nv; sv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w3 [e0; e1; e2])
Proof
  main_prefix_tac >>
  ‘app p e1_start_v [cv; mk] (L0_EV w0 w [])
     (POSTv v. &UNIT_TYPE () v * L0_EV w0 w3 [e0; e1; e2])’
    by (irule e1_start_closed_spec >> qexistsl [‘o0’, ‘o1’, ‘o2’, ‘w1’, ‘w2’] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  xapp >> xsimpl
QED

(* The listen fails: client_main returns after it *)
Theorem client_main_nolisten_spec:
  NUM c cv ∧ NUM a av ∧ NUM N nv ∧ STRING_TYPE (CLITS N rqs) sv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port c w3 = SOME (out, w4, ev) ∧ listen_fd out = NONE ⇒
  app (p:'ffi ffi_proj) client_main_v [cv; av; nv; sv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w4 [e0; e1; e2; ev])
Proof
  main_prefix_tac >>
  ‘app p e1_start_v [cv; mk] (L0_EV w0 w [])
     (POSTv v. &UNIT_TYPE () v * L0_EV w0 w4 [e0; e1; e2; ev])’
    by (irule e1_start_nolisten_spec >>
        qexistsl [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘c’, ‘w1’, ‘w2’, ‘w3’] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  xapp >> xsimpl
QED

Theorem client_main_term_spec:
  NUM c cv ∧ NUM a av ∧ NUM N nv ∧ STRING_TYPE (CLITS N rqs) sv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port c w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  erounds (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n =
    SOME (h, (w', es'), evs, logs) ∧
  call_done (cstate a N rqs h) ∧
  (∀j. j < n ⇒ ¬call_done (cstate a N rqs
                  (FST (erun (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) j)))) ⇒
  app (p:'ffi ffi_proj) client_main_v [cv; av; nv; sv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' ([e0; e1; e2; ev] ++ evs))
Proof
  main_prefix_tac >>
  ‘app p e1_start_v [cv; mk] (L0_EV w0 w [])
     (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' ([e0; e1; e2; ev] ++ evs))’
    by (irule (inst_cstn e1_start_term_spec) >>
        qexistsl [‘N’, ‘λ_. clast’, ‘es'’, ‘λ_. call_done’, ‘h’, ‘λ_. cifdsl’,
                  ‘λ_. cinit a N’, ‘k’, ‘logs’, ‘n’, ‘o0’, ‘o1’, ‘o2’, ‘out’,
                  ‘λ_. pol_never’, ‘c’, ‘λ_. cstep a rqs’, ‘w1’, ‘w2’, ‘w3’, ‘w4’] >>
        simp[client_fold_ifds, client_fold_prog, client_fold_state] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  xapp >> xsimpl
QED

(* The client never finishes: client_main diverges, the trace the fdok calls,
   the listen, and E1's rounds *)
Theorem client_main_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧
  NUM c cv ∧ NUM a av ∧ NUM N nv ∧ STRING_TYPE (CLITS N rqs) sv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port c w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  (∀n. erounds (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n ≠ NONE) ∧
  (∀n. ¬call_done (cstate a N rqs
                  (FST (erun (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n)))) ⇒
  app (p:'ffi ffi_proj) client_main_v [cv; av; nv; sv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
       (λi. fromList (eround_evs (n2w k) pol_never (cifds a N rqs) (cprog a N rqs)
                                 (w4, einit) i)) NONE)))
Proof
  main_prefix_tac >>
  ‘app p e1_start_v [cv; mk] (L0_EV w0 w [])
     (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
        (λi. fromList (eround_evs (n2w k) pol_never (cifds a N rqs) (cprog a N rqs)
                                  (w4, einit) i)) NONE)))’
    by (irule client_div_spec >> rpt conj_tac >>
        TRY (qexistsl [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘c’, ‘w1’, ‘w2’, ‘w3’] >> rpt conj_tac) >>
        first_assum ACCEPT_TAC) >>
  xapp >> xsimpl
QED
