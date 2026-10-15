(*
  The blocking echo loop that selects on the live connections, in CakeML.

      fun step_l (fds, live, c) =             (* c = (acts, s) *)
        let val rs = perform acts
            val u  = case acts of [] => wait_ready live | _ => ()
            val rdy = Socket.poll fds
        in (add_accepted fds rs, upd_live live acts rs,
            Async.poll c (rdy, 0, rs)) end
      fun run_l st = run_l (step_l st)

  As asyncM4BlkLoop's step_b, with one more component: the live list
  (asyncM4LiveEcho's lstep: an accept adds the new connection, a read
  that returns EOF removes one occurrence of its fd).  select waits on the
  live list instead of the whole interest list; the poll still polls the
  whole interest list.

  MAIN:
  - upd_live_spec: the code's update is live_of over the round's pairs;
  - live_of_trans_SNOC: and that is how live_of over the transcript
    grows, so the list the loop holds after the kept history h is
    live_of l0 (trans m h);
  - run_l_spec / run_l_stuck_spec / run_l_two_outcomes: as run_b's, for
    the select set sel h = live_of l0 (trans m h).
*)
Theory asyncM4LiveLoop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncTranscript asyncCfActModel
  asyncCfActProg asyncCfReactWorld asyncM3World asyncM3Prog asyncM3Loop
  asyncM4GRounds asyncM4Loop asyncM4SockServer asyncM4BlkWorld
  asyncM4BlkTrace asyncM4BlkLoop asyncM4LiveWorld asyncM4LiveEcho
  ffiSpikeSocketFFI ffiSpikeSocketProg ffiSpikeSocketProof
  ffiSpikeSocketDiv ffiSpikeSocketFair ffiSpikeSocketSelect cfDiv
  ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "asyncM4BlkLoop"

(* ------------------------------------------------------------------------
   The live list over the transcript, round by round
   ------------------------------------------------------------------------ *)

Theorem live_of_NONE:
  ∀U l0. EVERY (λp. SND p = NONE) U ⇒ live_of l0 U = l0
Proof
  Induct >> simp[live_of_def] >> PairCases >> simp[lstep_def] >>
  rpt strip_tac >> gvs[] >> every_case_tac >> gvs[GSYM live_of_def]
QED

Theorem zipr_NIL_NONE:
  ∀acts. EVERY (λp. SND p = NONE) (zipr acts [])
Proof
  Induct >> simp[zipr_def]
QED

Theorem round_trans_SNOC:
  n < LENGTH h ⇒ round_trans m (h ++ [s]) n = round_trans m h n
Proof
  rw[round_trans_def, TAKE_APPEND1, responses_at_def, EL_APPEND1]
QED

(* MAIN: one more snapshot: the responses of the last round's actions *)
Theorem live_of_trans_SNOC:
  live_of l0 (trans m (h ++ [s])) =
  live_of (live_of l0 (trans m h)) (zipr (new_actions (log_of m) h) s.results)
Proof
  REWRITE_TAC[trans_def] >>
  ‘SUC (LENGTH (h ++ [s])) = SUC (SUC (LENGTH h))’ by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[GENLIST, SNOC_APPEND, FLAT_APPEND, FLAT, APPEND_NIL, live_of_APPEND] >>
  ‘GENLIST (round_trans m (h ++ [s])) (LENGTH h) = GENLIST (round_trans m h) (LENGTH h)’
    by simp[GENLIST_FUN_EQ, round_trans_SNOC] >>
  simp[] >>
  ‘round_trans m h (LENGTH h) = zipr (new_actions (log_of m) h) []’
    by simp[round_trans_def, responses_at_def] >>
  ‘round_trans m (h ++ [s]) (LENGTH h) = zipr (new_actions (log_of m) h) s.results’
    by simp[round_trans_def, responses_at_def, TAKE_LENGTH_APPEND, EL_LENGTH_APPEND] >>
  ‘EVERY (λp. SND p = NONE) (round_trans m (h ++ [s]) (SUC (LENGTH h)))’
    by simp[round_trans_def, responses_at_def, zipr_NIL_NONE] >>
  simp[live_of_NONE, zipr_NIL_NONE]
QED

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun remove_one c l =
    case l of
      [] => []
    | x :: rest => if x = c then rest else x :: remove_one c rest;

  fun lstep_one live a r =
    case a of
      Accept l => (case r of Accepted (Some c) => c :: live | _ => live)
    | Read c n =>
        (case r of
           Got (Some s) => if String.size s = 0 then remove_one c live else live
         | _ => live)
    | Write c s => live;

  fun upd_live live acts rs =
    case acts of
      [] => live
    | a :: rest =>
        (case rs of
           [] => live
         | r :: rrest => upd_live (lstep_one live a r) rest rrest);

  fun step_l st =
    case st of (fds, live, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val u = (case acts of [] => wait_ready live | a :: rest => ())
        val rdy = Socket.poll fds
      in (add_accepted fds rs, upd_live live acts rs,
          Async.poll c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun run_l st = run_l (step_l st);
End

val st = get_ml_prog_state ();

val eq_num_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCT1);

(* ------------------------------------------------------------------------
   Specs of the live list's code
   ------------------------------------------------------------------------ *)

Theorem remove_one_spec:
  ∀l c lv cv. NUM (w2n c) cv ∧ LIST_TYPE NUM (MAP w2n l) lv ⇒
    app (p:'ffi ffi_proj) remove_one_v [cv; lv] emp
      (POSTv v. &LIST_TYPE NUM (MAP w2n (remove_one c l)) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "remove_one_v_def") >>
  gvs[LIST_TYPE_def, remove_one_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >> xlet ‘POSTv bv. &BOOL (h = c) bv’
  >- (xapp_spec eq_num_v_thm >> xsimpl >> qexistsl [‘w2n c’, ‘w2n h’] >> simp[])
  >> xif
  >- (xvar >> xsimpl >> gvs[])
  >> xlet ‘POSTv rv. &LIST_TYPE NUM (MAP w2n (remove_one c l)) rv’
  >- (xapp >> simp[])
  >> xcon >> xsimpl >> gvs[LIST_TYPE_def]
QED

Theorem lstep_simps:
  lstep live (Write c d, ro) = live ∧
  lstep live (Accept l, SOME r) =
    (case r of Accepted (SOME c) => c :: live | _ => live) ∧
  lstep live (Read c n, SOME r) =
    (case r of Got (SOME bs) => if bs = [] then remove_one c live else live | _ => live)
Proof
  rpt conj_tac
  >- (Cases_on ‘ro’ >> simp[lstep_def] >> every_case_tac)
  >- (Cases_on ‘r’ >> simp[lstep_def] >> every_case_tac)
  >- (Cases_on ‘r’ >> simp[lstep_def] >> every_case_tac)
QED

Theorem lstep_one_spec:
  LIST_TYPE NUM (MAP w2n live) lv ∧ SACT a av ∧ SRESP r rv ⇒
  app (p:'ffi ffi_proj) lstep_one_v [lv; av; rv] emp
    (POSTv v. &LIST_TYPE NUM (MAP w2n (lstep live (a, SOME r))) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "lstep_one_v_def") >>
  Cases_on ‘a’ >> gvs[SACT_def] >> xmatch >> simp[lstep_simps] >>
  TRY (xvar >> xsimpl >> gvs[] >> NO_TAC) >>
  Cases_on ‘r’ >> gvs[SRESP_def] >>
  TRY (rename1 ‘OPTION_MAP _ o'’ >> Cases_on ‘o'’) >>
  gvs[OPTION_TYPE_def] >> xmatch >>
  TRY (xvar >> xsimpl >> gvs[] >> NO_TAC) >>
  TRY (xcon >> xsimpl >> gvs[LIST_TYPE_def] >> NO_TAC) >>
  rename1 ‘bytes_str bs’ >>
  xlet ‘POSTv nv. &NUM (LENGTH bs) nv’
  >- (xapp >> xsimpl >> qexists_tac ‘bytes_str bs’ >> simp[]) >>
  xlet ‘POSTv bv. &BOOL (LENGTH bs = 0) bv’
  >- (xapp_spec eq_num_v_thm >> xsimpl >> qexists_tac ‘LENGTH bs’ >>
      simp[LENGTH_NIL]) >>
  xif >> gvs[LENGTH_NIL]
  >- (xapp >> simp[])
  >> xvar >> xsimpl >> gvs[]
QED

Theorem upd_live_spec:
  ∀acts live rs lv av rsv.
    LIST_TYPE NUM (MAP w2n live) lv ∧ LIST_TYPE SACT acts av ∧
    LIST_TYPE SRESP rs rsv ⇒
    app (p:'ffi ffi_proj) upd_live_v [lv; av; rsv] emp
      (POSTv v. &LIST_TYPE NUM (MAP w2n (live_of live (zipr acts rs))) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "upd_live_v_def") >>
  gvs[LIST_TYPE_def, zipr_def, live_of_def] >> xmatch
  >- (xvar >> xsimpl)
  >> Cases_on ‘rs’ >> gvs[LIST_TYPE_def] >> xmatch
  >- (xvar >> xsimpl >>
      simp[GSYM live_of_def] >>
      ‘live_of (lstep live (h, NONE)) (zipr acts []) = live’
        suffices_by simp[] >>
      ‘lstep live (h, NONE) = live’ by (simp[lstep_def] >> every_case_tac) >>
      simp[live_of_NONE, zipr_NIL_NONE])
  >> rename1 ‘SRESP r rv0’
  >> xlet ‘POSTv v. &LIST_TYPE NUM (MAP w2n (lstep live (h, SOME r))) v’
  >- (xapp_spec lstep_one_spec >> xsimpl >> metis_tac[])
  >> xapp >> simp[GSYM live_of_def] >> metis_tac[]
QED
