(*
  The never-ending event loop in a reactive world (asyncCfReactWorld).

      fun step (nr, c) =             (* c = (acts, s) *)
        buf := acts ++ nr zero bytes;
        #(round) "" buf;             (* the world answers the round *)
        poll c (readiness bytes, 0, responses)
      fun run st = run (step st)

  One FFI call per round hands the world all the round's actions and gets
  back the positional responses and the readiness bytes.  nr is the
  world's number of readiness bytes (wd.nready), carried in the loop state.

  Result (run_spec): the loop diverges and its trace is one round_event per
  round, for the history the world generates; with wtrace_actions_rounds,
  the actions handed to the world are exactly the model's action log.
*)
Theory asyncCfReactLoop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  asyncCfActSpec asyncCfReactWorld cfDiv ml_translator mlbasicsProg
  Word8Prog Word8ArrayProof ListProg llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfActProg"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun fill buf i xs =
    case xs of
      [] => ()
    | x :: rest => (Word8Array.update buf i x; fill buf (i + 1) rest);

  fun read_bytes buf i n =
    if n = 0 then []
    else Word8Array.sub buf i :: read_bytes buf (i + 1) (n - 1);

  fun step st =
    case st of (nr, c) =>
    case c of (acts, s) =>
      let
        val k = List.length acts
        val buf = Word8Array.array (k + nr) (Word8.fromInt 0)
        val u1 = fill buf 0 acts
        val u2 = #(round) "" buf
        val rs = read_bytes buf 0 k
        val rdy = read_bytes buf k nr
      in (nr, poll c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun run st = run (step st);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Byte-buffer helpers
   ------------------------------------------------------------------------ *)

Theorem TAKE_LUPDATE_SUC[local]:
  ∀bs i. i < LENGTH bs ⇒ TAKE (i + 1) (LUPDATE h i bs) = TAKE i bs ++ [h]
Proof
  Induct >> Cases_on ‘i’ >> gvs[LUPDATE_def, ADD1]
QED

Theorem DROP_LUPDATE_LT[local]:
  ∀bs i j. i < j ⇒ DROP j (LUPDATE h i bs) = DROP j bs
Proof
  Induct >> Cases_on ‘i’ >> Cases_on ‘j’ >> gvs[LUPDATE_def]
QED

(* fill buf i xs writes xs into buf from index i on *)
Theorem fill_spec:
  ∀xs xsv i iv bs.
    LIST_TYPE WORD xs xsv ∧ NUM i iv ∧ i + LENGTH xs ≤ LENGTH bs ⇒
    app (p:'ffi ffi_proj) fill_v [bufv; iv; xsv] (W8ARRAY bufv bs)
      (POSTv u. &UNIT_TYPE () u *
                W8ARRAY bufv (TAKE i bs ++ xs ++ DROP (i + LENGTH xs) bs))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "fill_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[TAKE_DROP])
  >- (xlet ‘POSTv u. W8ARRAY bufv (LUPDATE h i bs)’
      >- (xapp >> xsimpl >> qexistsl [‘h’, ‘i’] >> simp[]) >>
      xlet ‘POSTv jv. &NUM (i + 1) jv * W8ARRAY bufv (LUPDATE h i bs)’
      >- (xapp >> xsimpl >> qexists_tac ‘&i’ >> gvs[NUM_def, INT_def] >>
          intLib.COOPER_TAC) >>
      xapp >> xsimpl >> qexists_tac ‘i + 1’ >>
      simp[TAKE_LUPDATE_SUC, DROP_LUPDATE_LT] >>
      simp[ADD1])
QED

(* read_bytes buf i n returns the n bytes of buf from index i on *)
Theorem read_bytes_spec:
  ∀n nv i iv.
    NUM n nv ∧ NUM i iv ∧ i + n ≤ LENGTH bs ⇒
    app (p:'ffi ffi_proj) read_bytes_v [bufv; iv; nv] (W8ARRAY bufv bs)
      (POSTv v. &LIST_TYPE WORD (TAKE n (DROP i bs)) v * W8ARRAY bufv bs)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "read_bytes_v_def") >>
  (xlet_auto >- xsimpl) >> xif
  >- (qexists_tac ‘T’ >> simp[] >> xcon >> xsimpl >> simp[LIST_TYPE_def])
  >- (qexists_tac ‘F’ >> simp[] >>
      xlet ‘POSTv mv. &NUM n mv * W8ARRAY bufv bs’
      >- (xapp >> xsimpl >> qexists_tac ‘&SUC n’ >> gvs[NUM_def, INT_def] >>
          intLib.COOPER_TAC) >>
      xlet ‘POSTv jv. &NUM (i + 1) jv * W8ARRAY bufv bs’
      >- (xapp >> xsimpl >> qexists_tac ‘&i’ >> gvs[NUM_def, INT_def] >>
          intLib.COOPER_TAC) >>
      xlet ‘POSTv rv. &LIST_TYPE WORD (TAKE n (DROP (i + 1) bs)) rv *
                      W8ARRAY bufv bs’
      >- (xapp >> simp[]) >>
      xlet ‘POSTv bv. &WORD (EL i bs) bv * W8ARRAY bufv bs’
      >- (xapp >> xsimpl >> qexists_tac ‘i’ >> simp[]) >>
      xcon >> xsimpl >>
      ‘i < LENGTH bs’ by decide_tac >>
      simp[DROP_CONS_EL, LIST_TYPE_def, ADD1])
QED

(* ------------------------------------------------------------------------
   One round, and the loop
   ------------------------------------------------------------------------ *)

(* The readiness bytes bs represent the ready set `set bs` *)
Definition READYL_def:
  READYL rdy v ⇔ ∃bs:word8 list. rdy = set bs ∧ LIST_TYPE WORD bs v
End

(* MAIN: one loop iteration in a reactive world.  If cv implements m and
   the world is in state s, the iteration hands the world m's first-round
   actions in one `round` call; the world answers with responses rs and
   readiness bytes rdy and moves to s'; and the loop returns a value
   implementing m with the snapshot (set rdy, 0, rs) delivered. *)
Theorem step_spec:
  world_ok wd ∧ limited_parts [«round»] p ∧ NUM wd.nready nrv ∧
  COMP p WORD A (SNAPSHOT READYL WORD) m cv ⇒
  app (p:'ffi ffi_proj) step_v [Conv NONE [nrv; cv]] (RW wd s [])
    (POSTv v.
       &(∃cv'. v = Conv NONE [nrv; cv'] ∧
               COMP p WORD A (SNAPSHOT READYL WORD)
                 (suspended m [wsnap (FST (wd.step s (m []).actions))
                                     (FST (SND (wd.step s (m []).actions)))])
                 cv') *
       RW wd (SND (SND (wd.step s (m []).actions)))
          [round_event wd (m []).actions (FST (wd.step s (m []).actions))
                          (FST (SND (wd.step s (m []).actions)))])
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_v_def") >> xmatch >> xmatch >>
  qabbrev_tac ‘acts = (m []).actions’ >>
  qabbrev_tac ‘r = wd.step s acts’ >>
  ‘LENGTH (FST r) = LENGTH acts ∧ LENGTH (FST (SND r)) = wd.nready’
    by gvs[world_ok_def, Abbr ‘r’] >>
  xlet ‘POSTv kv. &NUM (LENGTH acts) kv * RW wd s []’
  >- (xapp_spec (INST_TYPE [alpha |-> “:word8”] ListProgTheory.length_v_thm) >>
      xsimpl >> metis_tac[]) >>
  xlet ‘POSTv zv. &WORD (0w:word8) zv * RW wd s []’
  >- (xapp >> xsimpl >> simp[]) >>
  xlet ‘POSTv tv. &NUM (LENGTH acts + wd.nready) tv * RW wd s []’
  >- (xapp >> xsimpl >> qexistsl [‘&wd.nready’, ‘&LENGTH acts’] >>
      gvs[NUM_def, INT_def] >> intLib.COOPER_TAC) >>
  xlet ‘POSTv bufv. W8ARRAY bufv (REPLICATE (LENGTH acts + wd.nready) 0w) *
                    RW wd s []’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xlet ‘POSTv u. W8ARRAY bufv (acts ++ REPLICATE wd.nready 0w) * RW wd s []’
  >- (xapp >> xsimpl >> simp[rich_listTheory.DROP_REPLICATE] >>
      qexists_tac ‘acts’ >> simp[]) >>
  xlet ‘POSTv u. W8ARRAY bufv (FST r ++ FST (SND r)) *
                 RW wd (SND (SND r)) [round_event wd acts (FST r) (FST (SND r))]’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘wd.enc s’, ‘round_update wd’, ‘[«round»]’, ‘[]’] >>
      simp[RW_def] >>
      DEP_REWRITE_TAC[round_update_enc] >> simp[] >>
      simp[round_event_def, Abbr ‘r’] >> xsimpl) >>
  xlet ‘POSTv rsv. &LIST_TYPE WORD (FST r) rsv *
                   W8ARRAY bufv (FST r ++ FST (SND r)) *
                   RW wd (SND (SND r)) [round_event wd acts (FST r) (FST (SND r))]’
  >- (xapp >> xsimpl >> qexists_tac ‘LENGTH acts’ >>
      ‘LENGTH acts = LENGTH (FST r)’ by simp[] >>
      pop_assum SUBST1_TAC >> simp[TAKE_LENGTH_APPEND]) >>
  xlet ‘POSTv rdv. &LIST_TYPE WORD (FST (SND r)) rdv *
                   W8ARRAY bufv (FST r ++ FST (SND r)) *
                   RW wd (SND (SND r)) [round_event wd acts (FST r) (FST (SND r))]’
  >- (xapp >> xsimpl >> qexistsl [‘wd.nready’, ‘LENGTH acts’] >>
      ‘LENGTH acts = LENGTH (FST r)’ by simp[] >>
      pop_assum SUBST1_TAC >>
      simp[DROP_LENGTH_APPEND, TAKE_LENGTH_ID_rwt]) >>
  xlet ‘POSTv wv. &SNAPSHOT READYL WORD (wsnap (FST r) (FST (SND r))) wv *
                  W8ARRAY bufv (FST r ++ FST (SND r)) *
                  RW wd (SND (SND r)) [round_event wd acts (FST r) (FST (SND r))]’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, wsnap_def, READYL_def] >> metis_tac[]) >>
  ‘app p poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p WORD A (SNAPSHOT READYL WORD)
                 (suspended m [wsnap (FST r) (FST (SND r))]) v)’
    by (irule poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p WORD A (SNAPSHOT READYL WORD)
                     (suspended m [wsnap (FST r) (FST (SND r))]) cv' *
                   W8ARRAY bufv (FST r ++ FST (SND r)) *
                   RW wd (SND (SND r)) [round_event wd acts (FST r) (FST (SND r))]’
  >- (qpat_x_assum ‘app _ poll_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl
QED

(* MAIN: in any well-behaved reactive world wd started in state s0, the
   event loop never terminates, and its I/O trace is one round event per
   round, for the history the world generates (wrounds: iterate the world's
   step function with the model's new actions).  With
   wtrace_actions_rounds, the actions handed to the world in rounds 0..n
   are exactly the model's action log on that history.  (Invariant: after i
   iterations the loop holds a value implementing
   suspended m (whist wd m s0 i), and the world is in state
   SND (wrounds wd m s0 i).) *)
Theorem run_spec:
  world_ok wd ∧ limited_parts [«round»] p ∧ wf m ∧ NUM wd.nready nrv ∧
  COMP p WORD A (SNAPSHOT READYL WORD) m cv ⇒
  app (p:'ffi ffi_proj) run_v [Conv NONE [nrv; cv]] (RW wd s0 [])
    (POSTd io. io = LGENLIST (wround_event wd m s0) NONE)
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then [] else [wround_event wd m s0 (i - 1)]’ >>
  qexists_tac ‘λi stv. ∃cv. stv = Conv NONE [nrv; cv] ∧
                 COMP p WORD A (SNAPSHOT READYL WORD)
                   (suspended m (FST (wrounds wd m s0 i))) cv’ >>
  qexists_tac ‘λi. wd.enc (SND (wrounds wd m s0 i))’ >>
  qexists_tac ‘round_update wd’ >>
  simp[CONJUNCT1 wrounds_def] >> rpt conj_tac
  >- (simp[RW_def] >> xsimpl)
  >- ((* one iteration: step_spec, with the model and the world advanced *)
      rpt strip_tac >> gvs[] >> simp[GSYM RW_def] >>
      qabbrev_tac ‘h = FST (wrounds wd m s0 i)’ >>
      qabbrev_tac ‘s = SND (wrounds wd m s0 i)’ >>
      drule_all step_spec >> disch_then (qspec_then ‘s’ mp_tac) >>
      simp[suspended_first_poll, suspended_suspended_one] >>
      strip_tac >>
      xlet ‘POSTv v.
              &(∃cv'. v = Conv NONE [nrv; cv'] ∧
                      COMP p WORD A (SNAPSHOT READYL WORD)
                        (suspended m (FST (wrounds wd m s0 (SUC i)))) cv') *
              RW wd (SND (wrounds wd m s0 (SUC i))) [wround_event wd m s0 i]’
      >- (qpat_x_assum ‘app _ step_v _ _ _’ xapp_spec >> xsimpl >>
          simp[wrounds_SUC, wround_event_alt, Abbr ‘h’, Abbr ‘s’] >>
          rpt strip_tac >> gvs[] >> xsimpl) >>
      xvar >> xsimpl >> rpt strip_tac >> gvs[] >> metis_tac[])
  >- ((* the trace: no events before the first iteration, then one per round *)
      simp[LFLATTEN_LGENLIST_shift1] >>
      AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM])
QED
