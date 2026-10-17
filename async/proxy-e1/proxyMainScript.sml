(*
  The proxy's CakeML run on the E1 driver: proxy_main a b hw runs
  e1_start a on the proxy's fold (proxyCerts: pinitl, pstepl, pacts_of,
  pifds_of, pfin; pol_never), the backend port b and the Level threshold
  hw fixed.

   - mk_proxy_spec: mk_proxy b hw lfd's values meet ECODE with pinit,
     pstep, pifds_of, MAP SND ∘ last and K F (the model's fold, pprog_fold).
   - proxy_main_closed/nolisten/div_spec: e1_start's outcomes for
     proxy_main.  The proxy never finishes (fin = K F), so there is no
     terminating run after a successful listen.
*)
Theory proxyMain
Ancestors
  ml_translator cfHeapsBase cfApp cfDiv endpointHLModel asyncCore asyncLevel1 asyncM3World
  honestL0 honestL0World honestL1Model honestL1PFModel honestL1EPModel honestL0Part
  honestL0Prog honestL0Proof honestL0Fdok honestL1PFProg e1TypesProg
  e1DriverProg e1DriverSpec e1Fold e1DriverLoop e1DriverMain e1Lemmas
  moonshotProxy proxyStepL proxyProg proxyFold proxyCerts
Libs
  preamble ml_translatorLib ml_progLib cfLib cfDivLib basisFunctionsLib

val _ = translation_extends "proxyProg";

Quote add_cakeml:
  fun mk_proxy b hw lfd =
    (pol_never, pifds_of lfd, pacts_of, pstepl lfd b hw, pfin, pinitl lfd b hw);
End

Quote add_cakeml:
  fun proxy_main a b hw =
    let
      fun mk lfd = mk_proxy b hw lfd
    in e1_start a mk end;
End

Overload PST = “MOONSHOTPROXY_PST_TYPE”
Overload ERESP = “ENDPOINTHLMODEL_ERESP_TYPE”

(* ------------------------------------------------------------------------
   mk_proxy's values
   ------------------------------------------------------------------------ *)

Theorem mk_proxy_spec:
  NUM b bv ∧ NUM hw hwv ∧ WORD lfd lfdv ⇒
  app (p:'ffi ffi_proj) mk_proxy_v [bv; hwv; lfdv] emp
    (POSTv v. &(∃polv ifdsv actsv stepv finv initv.
                  v = Conv NONE [polv; ifdsv; actsv; stepv; finv; initv] ∧
                  ECODE PST lfd pol_never (pifds_of lfd) (λst. MAP SND st.last)
                    (pstep lfd b hw) (K F)
                    (Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]) ∧
                  PST (pinit lfd b hw) initv))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "mk_proxy_v_def") >>
  xlet ‘POSTv v. &PST (pinitl lfd b hw) v’ >- (xapp >> simp[]) >>
  xlet ‘POSTv v. &(PST --> LIST_TYPE (WORD : word64 -> v -> bool) --> LIST_TYPE ERESP --> PST)
                    (pstepl lfd b hw) v’
  >- (xapp_spec (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Arrow_app3) pstepl_v_thm) >>
      simp[]) >>
  xlet ‘POSTv v. &(PST --> LIST_TYPE (WORD : word64 -> v -> bool)) (pifds_of lfd) v’
  >- (xapp_spec (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Arrow_app1) pifds_of_v_thm) >>
      simp[]) >>
  xcon >> xsimpl >>
  simp[ECODE_def, proxy_init_eq, proxy_step_eq, proxy_acts_eq, proxy_fin_eq,
       pacts_of_v_thm, pfin_v_thm, fetch "e1TypesProg" "pol_never_v_thm"]
QED

(* ------------------------------------------------------------------------
   The proxy's fold is pprog (moonshotProxy)
   ------------------------------------------------------------------------ *)

Theorem proxy_fold_ifds:
  fold_ifds (pinit lfd b hw) (pstep lfd b hw) (pifds_of lfd) = pifds lfd b hw
Proof
  simp[FUN_EQ_THM, fold_ifds_def, proxy_ifds_eq]
QED

Theorem proxy_fold_prog:
  fold_prog (pinit lfd b hw) (pstep lfd b hw) (λst. MAP SND st.last) (K F) = pprog lfd b hw
Proof
  simp[pprog_fold]
QED

(* ------------------------------------------------------------------------
   proxy_main
   ------------------------------------------------------------------------ *)

(* A driver spec with its state invariant ST := PST (a type instance) and
   the proxy's fold substituted, rewritten to pifds / pprog *)
fun inst_proxy th =
  let val stv = find_term (fn t => is_var t andalso fst (dest_var t) = "ST") (concl th)
      val th1 = INST_TY_TERM (match_term stv “PST”) th
  in Q.INST [‘pol’ |-> ‘λ_. pol_never’, ‘ifds’ |-> ‘λlfd. pifds_of lfd’,
             ‘acts’ |-> ‘λ_ st. MAP SND st.last’, ‘step’ |-> ‘λlfd. pstep lfd b hw’,
             ‘fin’ |-> ‘λ_. K F’, ‘init’ |-> ‘λlfd. pinit lfd b hw’] th1
     |> BETA_RULE |> REWRITE_RULE [proxy_fold_ifds, proxy_fold_prog]
  end;

val proxy_div_spec = inst_proxy e1_start_div_spec;

(* mk defined; EMK for mk *)
val main_prefix_tac =
  rpt strip_tac >>
  xcf_with_def (fetch "-" "proxy_main_v_def") >>
  xfun_spec ‘mk’
    ‘∀(lfd : word64) lfdv. WORD lfd lfdv ⇒
       app (p:'ffi ffi_proj) mk [lfdv] emp
         (POSTv v. &(∃polv ifdsv actsv stepv finv initv.
                       v = Conv NONE [polv; ifdsv; actsv; stepv; finv; initv] ∧
                       ECODE PST lfd pol_never (pifds_of lfd) (λst. MAP SND st.last)
                         (pstep lfd b hw) (K F)
                         (Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]) ∧
                       PST (pinit lfd b hw) initv))’
  >- (rpt strip_tac >> first_x_assum irule >> xapp_spec mk_proxy_spec >> simp[]) >>
  ‘EMK p PST (λ_. pol_never) (λlfd. pifds_of lfd) (λ_ st. MAP SND st.last)
       (λlfd. pstep lfd b hw) (λ_. K F) (λlfd. pinit lfd b hw) mk’
    by (simp[EMK_def] >> first_x_assum ACCEPT_TAC);

(* stdin, stdout or stderr closed: proxy_main returns after the fdok calls *)
Theorem proxy_main_closed_spec:
  NUM a av ∧ NUM b bv ∧ NUM hw hwv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ ¬fdok_all o0 o1 o2 ⇒
  app (p:'ffi ffi_proj) proxy_main_v [av; bv; hwv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w3 [e0; e1; e2])
Proof
  main_prefix_tac >>
  ‘app p e1_start_v [av; mk] (L0_EV w0 w [])
     (POSTv v. &UNIT_TYPE () v * L0_EV w0 w3 [e0; e1; e2])’
    by (irule e1_start_closed_spec >> qexistsl [‘o0’, ‘o1’, ‘o2’, ‘w1’, ‘w2’] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  xapp >> xsimpl
QED

(* The listen fails: proxy_main returns after it *)
Theorem proxy_main_nolisten_spec:
  NUM a av ∧ NUM b bv ∧ NUM hw hwv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port a w3 = SOME (out, w4, ev) ∧ listen_fd out = NONE ⇒
  app (p:'ffi ffi_proj) proxy_main_v [av; bv; hwv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w4 [e0; e1; e2; ev])
Proof
  main_prefix_tac >>
  ‘app p e1_start_v [av; mk] (L0_EV w0 w [])
     (POSTv v. &UNIT_TYPE () v * L0_EV w0 w4 [e0; e1; e2; ev])’
    by (irule e1_start_nolisten_spec >>
        qexistsl [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘a’, ‘w1’, ‘w2’, ‘w3’] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  xapp >> xsimpl
QED

(* The listen succeeds: proxy_main diverges, the trace the fdok calls, the
   listen, and E1's rounds *)
Theorem proxy_main_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧
  NUM a av ∧ NUM b bv ∧ NUM hw hwv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port a w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  (∀n. erounds (n2w k) pol_never (pifds (n2w k) b hw) (pprog (n2w k) b hw) (w4, einit) n ≠ NONE) ⇒
  app (p:'ffi ffi_proj) proxy_main_v [av; bv; hwv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
       (λi. fromList (eround_evs (n2w k) pol_never (pifds (n2w k) b hw) (pprog (n2w k) b hw)
                                 (w4, einit) i)) NONE)))
Proof
  main_prefix_tac >>
  ‘app p e1_start_v [av; mk] (L0_EV w0 w [])
     (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
        (λi. fromList (eround_evs (n2w k) pol_never (pifds (n2w k) b hw) (pprog (n2w k) b hw)
                                  (w4, einit) i)) NONE)))’
    by (irule proxy_div_spec >> simp[] >> qexistsl [‘out’, ‘a’] >> simp[]) >>
  xapp >> xsimpl
QED
