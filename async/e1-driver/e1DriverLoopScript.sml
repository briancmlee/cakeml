(*
  The E1 driver's loop (e1DriverProg's run_e) running a fold program
  (e1Fold) on E1's L1: its I/O trace is erounds' trace.
   - run_e_div_spec: if the program never finishes, the loop diverges and
     its trace is, round by round, the events of E1's rounds;
   - run_e_term_spec: if the program first finishes after n rounds, the
     loop returns right after round n, with the events of rounds 0..n-1.
  Both assume E1's rounds never fail (erounds never NONE), as the claims do.

  The program comes as translator certificates for its pure parts (ECODE):
  the step on a list snapshot (ssnap rdy rs), the round's actions, the
  interest handles and fin, each of the state; with pol, the pause policy.
*)
Theory e1DriverLoop
Ancestors
  ml_translator cfHeapsBase cfApp cfDiv endpointHLModel asyncCore asyncLevel1 asyncM3World
  honestL0 honestL0World honestL1Model honestL1PFModel honestL1EPModel honestL0Part
  honestL0Prog honestL0Proof honestL1PFProg honestL1PFSpec e1TypesProg e1DriverProg
  e1DriverSpec e1Fold
Libs
  preamble ml_translatorLib ml_progLib cfLib cfDivLib basisFunctionsLib

val _ = translation_extends "e1DriverProg";
val st = get_ml_prog_state ();

Overload L1P = “HONESTL1PFMODEL_L1P_TYPE”
Overload L1E = “HONESTL1EPMODEL_L1E_TYPE”
Overload EACT = “ENDPOINTHLMODEL_EACT_TYPE”
Overload ERESP = “ENDPOINTHLMODEL_ERESP_TYPE”

(* cv = (lfd, pol, ifds, acts, step, fin) as the loop takes them: the
   translator's certificates of the program's pure parts *)
Definition ECODE_def:
  ECODE (ST : 'st -> v -> bool) lfd pol ifds acts
        (step : 'st -> (word64, eresp) snapshot -> 'st) fin cv ⇔
    ∃lfdv polv ifdsv actsv stepv finv.
      cv = Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv] ∧
      WORD lfd lfdv ∧ (L1P --> WORD --> BOOL) pol polv ∧
      (ST --> LIST_TYPE WORD) ifds ifdsv ∧ (ST --> LIST_TYPE EACT) acts actsv ∧
      (ST --> LIST_TYPE WORD --> LIST_TYPE ERESP --> ST) (λs rdy rs. step s (ssnap rdy rs)) stepv ∧
      (ST --> BOOL) fin finv
End

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

(* A round of E1 with the state's interest and actions; the state steps
   with the round's snapshot *)
Theorem step_e_spec:
  ECODE ST lfd pol ifds acts step fin cv ∧ ST s sv ∧ L1E es esv ∧
  eround lfd pol (ifds s) (w, es) (acts s) = SOME (snap, (w', es'), log, evs1) ⇒
  app (p:'ffi ffi_proj) step_e_v [Conv NONE [cv; sv; esv]] (L0_EV w0 w evs)
    (POSTv v. &(∃sv' esv'. v = Conv NONE [cv; sv'; esv'] ∧ ST (step s snap) sv' ∧
                           L1E es' esv') *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rw[ECODE_def] >> gvs[eround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  xcf_with_def (fetch "e1DriverProg" "step_e_v_def") >> xmatch >> xmatch >>
  xlet ‘POSTv v. &LIST_TYPE EACT (acts s) v * L0_EV w0 w evs’
  >- (qpat_assum ‘(_ --> LIST_TYPE EACT) acts actsv’ xapp_spec >> xsimpl >> metis_tac[]) >>
  xlet ‘POSTv v. &(∃esv' rsv. v = Conv NONE [esv'; rsv] ∧ L1E ws11 esv' ∧
                              LIST_TYPE ERESP rs rsv) * L0_EV w0 ws10 (evs ++ evs')’
  >- (xapp_spec (INST_TYPE [alpha |-> “:l1p -> word64 -> bool”] eacts_spec) >> xsimpl >>
      qexistsl [‘acts s’, ‘es’, ‘lfd’, ‘pol’] >> simp[]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &LIST_TYPE WORD (ifds s) v * L0_EV w0 ws10 (evs ++ evs')’
  >- (qpat_assum ‘(_ --> LIST_TYPE WORD) ifds ifdsv’ xapp_spec >> xsimpl >> metis_tac[]) >>
  xlet ‘POSTv v. &(∃rdyv esv'. v = Conv NONE [rdyv; esv'] ∧ LIST_TYPE WORD rdy rdyv ∧
                               L1E es' esv') * L0_EV w0 w' (evs ++ evs' ++ tevs)’
  >- (xapp_spec etail_spec >> xsimpl >> metis_tac[]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &ST (step s (ssnap rdy rs)) v * L0_EV w0 w' (evs ++ evs' ++ tevs)’
  >- (qpat_assum ‘(_ --> _ --> _ --> ST) _ stepv’ xapp_spec >> xsimpl >> metis_tac[]) >>
  xcon >> xsimpl
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

(* The run after n rounds, and round n's events *)
Definition erun_def:
  erun lfd pol ifds m ws0 n = THE (erounds lfd pol ifds m ws0 n)
End

Definition eround_evs_def:
  eround_evs lfd pol ifds m ws0 n =
    DROP (LENGTH (FST (SND (SND (erun lfd pol ifds m ws0 n)))))
         (FST (SND (SND (erun lfd pol ifds m ws0 (SUC n)))))
End

Theorem erun_0[simp]:
  erun lfd pol ifds m ws0 0 = ([], ws0, [], [])
Proof
  simp[erun_def, erounds_def]
QED

Theorem erounds_SUC_SOME:
  erounds lfd pol ifds m ws0 (SUC n) = SOME r ⇒
  ∃h ws evs logs snap ws' log revs.
    erounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ∧
    eround lfd pol (ifds h) ws (new_actions (log_of m) h) = SOME (snap, ws', log, revs) ∧
    r = (h ++ [snap], ws', evs ++ revs, logs ++ [log])
Proof
  simp[erounds_def, AllCaseEqs()] >> rw[] >> simp[]
QED

Theorem erounds_LE_SOME:
  ∀n i. i ≤ n ∧ erounds lfd pol ifds m ws0 n ≠ NONE ⇒ erounds lfd pol ifds m ws0 i ≠ NONE
Proof
  Induct >> rw[] >> Cases_on ‘i = SUC n’ >> gvs[] >>
  first_x_assum irule >> simp[] >>
  Cases_on ‘erounds lfd pol ifds m ws0 (SUC n)’ >> gvs[] >>
  drule erounds_SUC_SOME >> rw[] >> simp[]
QED

Theorem erun_SUC:
  erounds lfd pol ifds m ws0 (SUC n) ≠ NONE ⇒
  ∃snap ws' log revs.
    eround lfd pol (ifds (FST (erun lfd pol ifds m ws0 n)))
      (FST (SND (erun lfd pol ifds m ws0 n)))
      (new_actions (log_of m) (FST (erun lfd pol ifds m ws0 n))) =
      SOME (snap, ws', log, revs) ∧
    erun lfd pol ifds m ws0 (SUC n) =
      (FST (erun lfd pol ifds m ws0 n) ++ [snap], ws',
       FST (SND (SND (erun lfd pol ifds m ws0 n))) ++ revs,
       SND (SND (SND (erun lfd pol ifds m ws0 n))) ++ [log]) ∧
    eround_evs lfd pol ifds m ws0 n = revs
Proof
  strip_tac >> Cases_on ‘erounds lfd pol ifds m ws0 (SUC n)’ >> gvs[] >>
  drule erounds_SUC_SOME >> rw[] >>
  simp[erun_def, eround_evs_def, rich_listTheory.DROP_LENGTH_APPEND]
QED

(* ------------------------------------------------------------------------
   The loop diverges (a program that never finishes)
   ------------------------------------------------------------------------ *)

(* The interest of a fold program's history: its state's *)
Definition fold_ifds_def:
  fold_ifds init step ifds (h : (word64, eresp) snapshot list) = ifds (FOLDL step init h)
End

Overload FRUN = “λlfd pol init step ifds acts fin ws0.
                   erun lfd pol (fold_ifds init step ifds) (fold_prog init step acts fin) ws0”
Overload FROUNDS = “λlfd pol init step ifds acts fin ws0.
                      erounds lfd pol (fold_ifds init step ifds) (fold_prog init step acts fin) ws0”
Overload FEVS = “λlfd pol init step ifds acts fin ws0.
                   eround_evs lfd pol (fold_ifds init step ifds) (fold_prog init step acts fin) ws0”

(* Round i of a fold program's run, from the state after rounds 0..i-1 *)
Theorem frun_SUC:
  FROUNDS lfd pol init step ifds acts fin ws0 (SUC i) ≠ NONE ∧
  FRUN lfd pol init step ifds acts fin ws0 i = (h, (w, es), evs, logs) ⇒
  ∃snap w' es' log revs.
    eround lfd pol (ifds (FOLDL step init h)) (w, es) (acts (FOLDL step init h)) =
      SOME (snap, (w', es'), log, revs) ∧
    FRUN lfd pol init step ifds acts fin ws0 (SUC i) = (h ++ [snap], (w', es'), evs ++ revs, logs ++ [log]) ∧
    FEVS lfd pol init step ifds acts fin ws0 i = revs ∧
    FOLDL step init (h ++ [snap]) = step (FOLDL step init h) snap
Proof
  strip_tac >> drule erun_SUC >> strip_tac >> gvs[fold_ifds_def, fold_prog_new_actions] >>
  PairCases_on ‘ws'’ >> simp[fold_state_SNOC]
QED

(* MAIN: a fold program that never finishes; the loop diverges, and its
   trace is, round by round, E1's events *)
Theorem run_e_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧
  ECODE ST lfd pol ifds acts step fin cv ∧ ST init sv ∧ L1E es0 esv ∧
  (∀n. FROUNDS lfd pol init step ifds acts fin (w, es0) n ≠ NONE) ∧
  (∀n. ¬fin (FOLDL step init (FST (FRUN lfd pol init step ifds acts fin (w, es0) n)))) ⇒
  app (p:'ffi ffi_proj) run_e_v [Conv NONE [cv; sv; esv]] (L0_EV w0 w evs0)
    (POSTd io. io = LAPPEND (fromList evs0) (LFLATTEN (LGENLIST
       (λi. fromList (FEVS lfd pol init step ifds acts fin (w, es0) i)) NONE)))
Proof
  strip_tac >>
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_e" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then evs0 else FEVS lfd pol init step ifds acts fin (w, es0) (i - 1)’ >>
  qexists_tac ‘λi stv. ∃sv' esv'.
                 stv = Conv NONE [cv; sv'; esv'] ∧
                 ST (FOLDL step init (FST (FRUN lfd pol init step ifds acts fin (w, es0) i))) sv' ∧
                 L1E (SND (FST (SND (FRUN lfd pol init step ifds acts fin (w, es0) i)))) esv' ∧
                 l0_reach w0 (FST (FST (SND (FRUN lfd pol init step ifds acts fin (w, es0) i))))’ >>
  qexists_tac ‘λi. l0_enc w0 (FST (FST (SND (FRUN lfd pol init step ifds acts fin (w, es0) i))))’ >>
  qexists_tac ‘l0_next w0’ >>
  simp[] >> rpt conj_tac
  >- (simp[L0_EV_def] >> xsimpl)
  >- ((* one iteration: fin is false, then a round (step_e_spec) *)
      rpt strip_tac >> gvs[] >>
      qabbrev_tac ‘r = FRUN lfd pol init step ifds acts fin (w, es0) i’ >>
      PairCases_on ‘r’ >> gvs[] >>
      ‘∃snap w' es' log revs.
         eround lfd pol (ifds (FOLDL step init r0)) (r1, r2) (acts (FOLDL step init r0)) =
           SOME (snap, (w', es'), log, revs) ∧
         FRUN lfd pol init step ifds acts fin (w, es0) (SUC i) =
           (r0 ++ [snap], (w', es'), r3 ++ revs, r4 ++ [log]) ∧
         FEVS lfd pol init step ifds acts fin (w, es0) i = revs ∧
         FOLDL step init (r0 ++ [snap]) = step (FOLDL step init r0) snap’
        by (irule frun_SUC >> simp[]) >>
      ‘¬fin (FOLDL step init r0)’
        by (first_x_assum (qspec_then ‘i’ mp_tac) >> simp[]) >>
      qpat_assum ‘ECODE _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [ECODE_def]) >>
      gvs[] >> qabbrev_tac ‘revs = FEVS lfd pol init step ifds acts fin (w, es0) i’ >>
      xmatch >> xmatch >>
      xlet ‘POSTv v. &BOOL F v * one (FFI_part (l0_enc w0 r1) (l0_next w0) l0_names [])’
      >- (qpat_assum ‘(_ --> BOOL) fin finv’ xapp_spec >> xsimpl >>
          qexistsl [‘FOLDL step init r0’, ‘fin’, ‘ST’] >> simp[]) >>
      xif >> qexists_tac ‘F’ >> simp[] >>
      sg ‘app p step_e_v [Conv NONE [Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]; sv'; esv']]
            (L0_EV w0 r1 [])
            (POSTv v. &(∃sv2 esv2. v = Conv NONE [Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]; sv2; esv2] ∧
                                   ST (step (FOLDL step init r0) snap) sv2 ∧ L1E es' esv2) *
                      L0_EV w0 w' ([] ++ revs))’
      >- (irule step_e_spec >> simp[ECODE_def] >>
          qexistsl [‘acts’, ‘r2’, ‘fin’, ‘ifds’, ‘lfd’, ‘log’, ‘pol’] >> simp[]) >>
      gvs[L0_EV_def, SEP_CLAUSES] >>
      xlet ‘POSTv v. &(∃sv2 esv2. v = Conv NONE [Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]; sv2; esv2] ∧
                                  ST (step (FOLDL step init r0) snap) sv2 ∧ L1E es' esv2) *
                     (one (FFI_part (l0_enc w0 w') (l0_next w0) l0_names revs) *
                      &l0_reach w0 w')’
      >- (qpat_x_assum ‘app _ step_e_v _ _ _’ xapp_spec >> xsimpl) >>
      xvar >> xsimpl >> rpt strip_tac >> gvs[] >> xsimpl)
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED

(* ------------------------------------------------------------------------
   The loop returns (a program that finishes)
   ------------------------------------------------------------------------ *)

Theorem erun_evs_prefix:
  ∀n i. i ≤ n ∧ erounds lfd pol ifds m ws0 n ≠ NONE ⇒
        ∃rest. FST (SND (SND (erun lfd pol ifds m ws0 n))) =
               FST (SND (SND (erun lfd pol ifds m ws0 i))) ++ rest
Proof
  Induct >> rw[] >> Cases_on ‘i = SUC n’ >> gvs[] >>
  ‘erounds lfd pol ifds m ws0 n ≠ NONE’
    by (irule erounds_LE_SOME >> qexists_tac ‘SUC n’ >> simp[]) >>
  first_x_assum (qspec_then ‘i’ mp_tac) >> simp[] >> strip_tac >>
  drule erun_SUC >> strip_tac >> simp[]
QED

Theorem erun_evs_prefix_from[local]:
  erounds lfd pol ifds m ws0 n ≠ NONE ⇒
  ∀i. i ≤ n ⇒ ∃rest. FST (SND (SND (erun lfd pol ifds m ws0 n))) =
                     FST (SND (SND (erun lfd pol ifds m ws0 i))) ++ rest
Proof
  metis_tac[erun_evs_prefix]
QED

Theorem run_e_term_gen[local]:
  ∀k i sv esv evs.
    FROUNDS lfd pol init step ifds acts fin ws0 n ≠ NONE ∧ i + k = n ∧
    fin (FOLDL step init (FST (FRUN lfd pol init step ifds acts fin ws0 n))) ∧
    (∀j. j < n ⇒ ¬fin (FOLDL step init (FST (FRUN lfd pol init step ifds acts fin ws0 j)))) ∧
    ECODE ST lfd pol ifds acts step fin cv ∧
    ST (FOLDL step init (FST (FRUN lfd pol init step ifds acts fin ws0 i))) sv ∧
    L1E (SND (FST (SND (FRUN lfd pol init step ifds acts fin ws0 i)))) esv ⇒
    app (p:'ffi ffi_proj) run_e_v [Conv NONE [cv; sv; esv]]
      (L0_EV w0 (FST (FST (SND (FRUN lfd pol init step ifds acts fin ws0 i)))) evs)
      (POSTv v. &UNIT_TYPE () v *
                L0_EV w0 (FST (FST (SND (FRUN lfd pol init step ifds acts fin ws0 n))))
                  (evs ++ DROP (LENGTH (FST (SND (SND (FRUN lfd pol init step ifds acts fin ws0 i)))))
                                 (FST (SND (SND (FRUN lfd pol init step ifds acts fin ws0 n))))))
Proof
  Induct >> rpt strip_tac
  >- ((* round n: fin holds, the loop returns *)
      gvs[] >>
      qpat_assum ‘ECODE _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [ECODE_def]) >>
      gvs[] >>
      xcf_with_def (fetch "e1DriverProg" "run_e_v_def") >> xmatch >> xmatch >>
      xlet ‘POSTv v. &BOOL T v *
              L0_EV w0 (FST (FST (SND (FRUN lfd pol init step ifds acts fin ws0 i)))) evs’
      >- (qpat_assum ‘(_ --> BOOL) fin finv’ xapp_spec >> xsimpl >>
          qexistsl [‘FOLDL step init (FST (FRUN lfd pol init step ifds acts fin ws0 i))’,
                    ‘fin’, ‘ST’] >> simp[]) >>
      xif >> qexists_tac ‘T’ >> simp[] >> xcon >> xsimpl >>
      simp[rich_listTheory.DROP_LENGTH_NIL]) >>
  (* round i < n: a round, then the rest *)
  ‘i < n’ by simp[] >>
  ‘FROUNDS lfd pol init step ifds acts fin ws0 (SUC i) ≠ NONE’
    by (irule erounds_LE_SOME >> qexists_tac ‘n’ >> simp[]) >>
  qabbrev_tac ‘r = FRUN lfd pol init step ifds acts fin ws0 i’ >>
  PairCases_on ‘r’ >> gvs[] >>
  drule_all frun_SUC >> strip_tac >>
  ‘¬fin (FOLDL step init r0)’
    by (first_x_assum (qspec_then ‘i’ mp_tac) >> simp[]) >>
  ‘∃rest. FST (SND (SND (FRUN lfd pol init step ifds acts fin ws0 (i + SUC k)))) =
          (r3 ++ revs) ++ rest’
    by (qpat_assum ‘FROUNDS _ _ _ _ _ _ _ _ (_ + _) ≠ NONE’
          (mp_tac o MATCH_MP erun_evs_prefix_from) >>
        disch_then (qspec_then ‘SUC i’ mp_tac) >> simp[]) >>
  qpat_assum ‘ECODE _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [ECODE_def]) >>
  gvs[] >> qabbrev_tac ‘revs = FEVS lfd pol init step ifds acts fin ws0 i’ >>
  xcf_with_def (fetch "e1DriverProg" "run_e_v_def") >> xmatch >> xmatch >>
  xlet ‘POSTv v. &BOOL F v * L0_EV w0 r1 evs’
  >- (qpat_assum ‘(_ --> BOOL) fin finv’ xapp_spec >> xsimpl >>
      qexistsl [‘FOLDL step init r0’, ‘fin’, ‘ST’] >> simp[]) >>
  xif >> qexists_tac ‘F’ >> simp[] >>
  xlet ‘POSTv v. &(∃sv2 esv2. v = Conv NONE [Conv NONE [lfdv; polv; ifdsv; actsv; stepv; finv]; sv2; esv2] ∧
                              ST (step (FOLDL step init r0) snap) sv2 ∧ L1E es' esv2) *
                 L0_EV w0 w' (evs ++ revs)’
  >- (xapp_spec step_e_spec >> xsimpl >> simp[ECODE_def] >>
      qexistsl [‘acts’, ‘r2’, ‘fin’, ‘ifds’, ‘lfd’, ‘log’, ‘pol’] >> simp[]) >>
  gvs[] >>
  qpat_x_assum ‘∀i sv esv evs. _ + k = _ ∧ _ ⇒ _’
    (qspecl_then [‘SUC i’, ‘sv2’, ‘esv2’, ‘evs ++ revs’] mp_tac) >>
  impl_tac >- gvs[ADD_CLAUSES] >>
  strip_tac >> xapp >> qexists_tac ‘emp’ >>
  qpat_x_assum ‘FRUN _ _ _ _ _ _ _ _ (SUC i) = _’ (fn th => REWRITE_TAC [th]) >>
  ‘DROP (LENGTH r3) (r3 ++ revs ++ rest) = revs ++ rest’
    by REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC [GSYM APPEND_ASSOC, GSYM LENGTH_APPEND, rich_listTheory.DROP_LENGTH_APPEND] >>
  xsimpl
QED

(* MAIN: a fold program that first finishes after n rounds; the loop
   returns right after round n-1, with the events of rounds 0..n-1 *)
Theorem run_e_term_spec:
  ECODE ST lfd pol ifds acts step fin cv ∧ ST init sv ∧ L1E es0 esv ∧
  FROUNDS lfd pol init step ifds acts fin (w, es0) n = SOME (h, (w', es'), evs, logs) ∧
  fin (FOLDL step init h) ∧
  (∀j. j < n ⇒ ¬fin (FOLDL step init (FST (FRUN lfd pol init step ifds acts fin (w, es0) j)))) ⇒
  app (p:'ffi ffi_proj) run_e_v [Conv NONE [cv; sv; esv]] (L0_EV w0 w evs0)
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' (evs0 ++ evs))
Proof
  strip_tac >>
  qspecl_then [‘n’, ‘0’, ‘sv’, ‘esv’, ‘evs0’] mp_tac
    (Q.INST [‘ws0’ |-> ‘(w, es0)’] run_e_term_gen) >>
  simp[erun_def] >> disch_then irule >> simp[] >> metis_tac[]
QED
