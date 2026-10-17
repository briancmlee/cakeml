(*
  The E1 driver's startup, e1_start port mk (e1DriverProg): D33's stdio
  check (sys_fdok on fds 0, 1, 2, always all three), then listen-first on
  port, then the loop (e1DriverLoop) on the program mk builds for the
  listener.  Four outcomes, one spec each:
   - e1_start_closed_spec: some fd of 0..2 is closed; the program returns
     after the three fdok calls;
   - e1_start_nolisten_spec: the listen fails; it returns after it;
   - e1_start_term_spec: the program first finishes after n rounds; it
     returns right after round n-1;
   - e1_start_div_spec: the program never finishes; it diverges.
*)
Theory e1DriverMain
Ancestors
  ml_translator cfHeapsBase cfApp cfDiv endpointHLModel asyncCore asyncLevel1 asyncM3World
  honestL0 honestL0World honestL1Model honestL1PFModel honestL1EPModel honestL0Part
  honestL0Prog honestL0Proof honestL0Fdok honestL1PFProg honestL1PFSpec e1TypesProg
  e1DriverProg e1DriverSpec e1Fold e1DriverLoop
Libs
  preamble ml_translatorLib ml_progLib cfLib cfDivLib basisFunctionsLib

val _ = translation_extends "e1DriverProg";
val st = get_ml_prog_state ();

Overload L1E = “HONESTL1EPMODEL_L1E_TYPE”

(* mk lfd: the program for listener lfd, as (pol, ifds, acts, step, fin,
   init) values with their certificates *)
Definition EMK_def:
  EMK (p : 'ffi ffi_proj) (ST : 'st -> v -> bool) pol ifds acts
      (step : word64 -> 'st -> (word64, eresp) snapshot -> 'st) fin init mkv ⇔
    ∀lfd lfdv. WORD lfd lfdv ⇒
      app p mkv [lfdv] emp
        (POSTv v. &(∃polv ifdsv actsv stepv finv initv.
                      v = Conv NONE [polv; ifdsv; actsv; stepv; finv; initv] ∧
                      ECODE ST lfd (pol lfd) (ifds lfd) (acts lfd) (step lfd) (fin lfd)
                        (Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]) ∧
                      ST (init lfd) initv))
End

(* The listen on port, and its listener *)
Definition sys_listen_port_def:
  sys_listen_port port w = l0_do «sys_listen» (port_bytes port) 13 w
End

(* ------------------------------------------------------------------------
   The calls
   ------------------------------------------------------------------------ *)

Theorem c_fdok_spec:
  WORD f fv ∧ l0_do «sys_fdok» [f] 1 w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_fdok_v [fv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "c_fdok_v_def") >>
  rpt (xlet_auto >- (TRY xcon >> xsimpl)) >>
  ‘LIST_TYPE WORD [f] v'’ by gvs[LIST_TYPE_def] >>
  (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec L0_fdok_spec >> xsimpl >>
      gvs[bytes_str_bytes_to_str, LIST_TYPE_def] >> metis_tac[]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

Theorem c_listen_spec:
  NUM port portv ∧ sys_listen_port port w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_listen_v [portv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "e1DriverProg" "c_listen_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec L0_listen_spec >> xsimpl >>
      gvs[sys_listen_port_def, bytes_str_bytes_to_str] >> metis_tac[]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* ------------------------------------------------------------------------
   The startup
   ------------------------------------------------------------------------ *)

Overload FDOK3 = “λw w1 w2 w3 o0 o1 o2 e0 e1 e2.
   l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
   l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
   l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2)”

(* One fdok call: fd f's answer out, the world w to w', the trace evs to
   evs ++ [ev] (the spec instantiated: xapp_spec's own match loses them) *)
fun fdok_call_tac f out w w' ev evs evs_xs =
  xapp_spec (Q.INST [‘f’ |-> f, ‘out’ |-> out, ‘w'’ |-> w', ‘ev’ |-> ev,
                     ‘evs’ |-> evs] c_fdok_spec) >> xsimpl >>
  qexistsl ([‘emp’, w', ‘w0’, w, out, ev] @ evs_xs) >> xsimpl;

(* The three fdok calls, then the check *)
val fdok3_tac =
  xcf_with_def (fetch "e1DriverProg" "e1_start_v_def") >>
  (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE WORD o0 v * L0_EV w0 w1 [e0]’
  >- fdok_call_tac ‘0w’ ‘o0’ ‘w’ ‘w1’ ‘e0’ ‘[]’ [] >>
  (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE WORD o1 v * L0_EV w0 w2 [e0; e1]’
  >- fdok_call_tac ‘1w’ ‘o1’ ‘w1’ ‘w2’ ‘e1’ ‘[e0]’ [‘e0’] >>
  (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE WORD o2 v * L0_EV w0 w3 [e0; e1; e2]’
  >- fdok_call_tac ‘2w’ ‘o2’ ‘w2’ ‘w3’ ‘e2’ ‘[e0; e1]’ [‘e1’, ‘e0’] >>
  rpt (xlet_auto >- xsimpl);

(* Some fd of 0..2 is closed: e1_start returns after the three calls *)
Theorem e1_start_closed_spec:
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ ¬fdok_all o0 o1 o2 ⇒
  app (p:'ffi ffi_proj) e1_start_v [portv; mkv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w3 [e0; e1; e2])
Proof
  rpt strip_tac >> fdok3_tac >>
  xif >> qexists_tac ‘T’ >> simp[] >> xcon >> xsimpl
QED

(* The listen after the three fdok calls (as fdok_call_tac) *)
val listen_call_tac =
  xapp_spec (Q.INST [‘w'’ |-> ‘w4’, ‘evs’ |-> ‘[e0; e1; e2]’, ‘w’ |-> ‘w3’]
                    c_listen_spec) >> xsimpl >>
  qexistsl [‘emp’, ‘w4’, ‘w3’, ‘w0’, ‘out’, ‘ev’, ‘e2’, ‘e1’, ‘e0’] >>
  qexists_tac ‘port’ >> simp[] >> xsimpl;

(* The listen fails: e1_start returns after it *)
Theorem e1_start_nolisten_spec:
  NUM port portv ∧ FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port port w3 = SOME (out, w4, ev) ∧ listen_fd out = NONE ⇒
  app (p:'ffi ffi_proj) e1_start_v [portv; mkv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w4 [e0; e1; e2; ev])
Proof
  rpt strip_tac >> fdok3_tac >>
  xif >> qexists_tac ‘F’ >> simp[] >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- listen_call_tac >>
  (xlet_auto >- xsimpl) >> gvs[std_preludeTheory.OPTION_TYPE_def] >> xmatch >>
  xcon >> xsimpl
QED

Theorem l0_do_reach:
  l0_reach w0 w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒ l0_reach w0 w'
Proof
  rw[l0_do_def, AllCaseEqs()] >> metis_tac[l0_reach_step]
QED

(* The listen succeeds: lfd, then mk lfd's values, then the loop *)
val listen_ok_tac =
  xif >> qexists_tac ‘F’ >> simp[] >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- listen_call_tac >>
  (xlet_auto >- xsimpl) >> gvs[std_preludeTheory.OPTION_TYPE_def] >> xmatch >>
  (xlet_auto >- xsimpl) >>
  rename1 ‘WORD (n2w k) lfdv’ >>
  qpat_assum ‘EMK _ _ _ _ _ _ _ _ _’
    (fn th => qpat_assum ‘WORD (n2w k) lfdv’
       (strip_assume_tac o MATCH_MP (SPEC_ALL (REWRITE_RULE [EMK_def] th)))) >>
  xlet ‘POSTv v. &(∃polv ifdsv actsv stepv finv initv.
                      v = Conv NONE [polv; ifdsv; actsv; stepv; finv; initv] ∧
                      ECODE ST (n2w k : word64) (pol (n2w k)) (ifds (n2w k)) (acts (n2w k)) (step (n2w k))
                        (fin (n2w k)) (Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]) ∧
                      ST (init (n2w k)) initv) * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- (qpat_x_assum ‘app _ mkv _ _ _’ xapp_spec >> xsimpl >> rpt strip_tac >>
      qexistsl [‘polv’, ‘ifdsv’, ‘actsv’, ‘stepv’, ‘finv’, ‘initv’] >>
      asm_rewrite_tac[]) >>
  gvs[] >> xmatch >>
  assume_tac (fetch "e1DriverProg" "einit_v_thm") >>
  rpt (xlet_auto >- (TRY xcon >> xsimpl));

(* The program first finishes after n rounds: e1_start returns right after
   round n-1, the trace the fdok calls, the listen, and rounds 0..n-1 *)
Theorem e1_start_term_spec:
  NUM port portv ∧ EMK p ST pol ifds acts step fin init mkv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port port w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  FROUNDS (n2w k) (pol (n2w k)) (init (n2w k)) (step (n2w k)) (ifds (n2w k)) (acts (n2w k))
          (fin (n2w k)) (w4, einit) n = SOME (h, (w', es'), evs, logs) ∧
  fin (n2w k) (FOLDL (step (n2w k)) (init (n2w k)) h) ∧
  (∀j. j < n ⇒ ¬fin (n2w k) (FOLDL (step (n2w k)) (init (n2w k))
                    (FST (FRUN (n2w k) (pol (n2w k)) (init (n2w k)) (step (n2w k)) (ifds (n2w k))
                               (acts (n2w k)) (fin (n2w k)) (w4, einit) j)))) ⇒
  app (p:'ffi ffi_proj) e1_start_v [portv; mkv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' ([e0; e1; e2; ev] ++ evs))
Proof
  rpt strip_tac >> fdok3_tac >> listen_ok_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> xapp_spec run_e_term_spec >> xsimpl >>
  qexistsl [‘emp’, ‘w0’, ‘w'’, ‘w4’, ‘[e0; e1; e2; ev]’, ‘evs’, ‘ST’,
            ‘acts (n2w k)’, ‘es'’, ‘einit’, ‘fin (n2w k)’, ‘h’, ‘ifds (n2w k)’,
            ‘init (n2w k)’, ‘n2w k’, ‘logs’, ‘n’, ‘pol (n2w k)’, ‘step (n2w k)’] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, xsimpl]
QED

(* The program never finishes: e1_start diverges, the trace the fdok calls,
   the listen, and E1's rounds *)
Theorem e1_start_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧
  NUM port portv ∧ EMK p ST pol ifds acts step fin init mkv ∧
  FDOK3 w w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port port w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  (∀n. FROUNDS (n2w k) (pol (n2w k)) (init (n2w k)) (step (n2w k)) (ifds (n2w k))
               (acts (n2w k)) (fin (n2w k)) (w4, einit) n ≠ NONE) ∧
  (∀n. ¬fin (n2w k) (FOLDL (step (n2w k)) (init (n2w k))
                (FST (FRUN (n2w k) (pol (n2w k)) (init (n2w k)) (step (n2w k)) (ifds (n2w k))
                           (acts (n2w k)) (fin (n2w k)) (w4, einit) n)))) ⇒
  app (p:'ffi ffi_proj) e1_start_v [portv; mkv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
       (λi. fromList (FEVS (n2w k) (pol (n2w k)) (init (n2w k)) (step (n2w k)) (ifds (n2w k))
                           (acts (n2w k)) (fin (n2w k)) (w4, einit) i)) NONE)))
Proof
  rpt strip_tac >>
  ‘l0_reach w0 w4’
    by (gvs[sys_listen_port_def] >> metis_tac[l0_do_reach]) >>
  fdok3_tac >> listen_ok_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> xapp_spec run_e_div_spec >> xsimpl >>
  qexistsl [‘emp’, ‘w0’, ‘w4’, ‘step (n2w k)’, ‘pol (n2w k)’, ‘n2w k’, ‘init (n2w k)’,
            ‘ifds (n2w k)’, ‘fin (n2w k)’, ‘[e0; e1; e2; ev]’, ‘einit’, ‘acts (n2w k)’,
            ‘ST’] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, xsimpl >> NO_TAC, simp[] >> NO_TAC]
QED
