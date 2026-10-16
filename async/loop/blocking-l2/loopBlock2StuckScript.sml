(*
  The blocking event loop (Level 2) without the liveness assumption
  blk_live: two outcomes.

  loopBlock2's brun_spec assumes blk_live c ws: whenever the loop
  blocks, a declared byte eventually arrives.  It need not.  Without it,
  either
  1. blk_live holds after all, and brun_spec applies: the loop diverges,
     with the same actions as the polling loop (no busy waiting); or
  2. the loop blocks in select in some round n in which no declared byte
     ever arrives (bstuck).  Then the run ends in an FFI divergence of
     «select», after the events of the first n rounds, and the polling
     loop would never have performed another action either.

  MAIN:
  - brounds_inv_upto: loopBlock2World's invariant, up to the first round
    that is stuck (no blk_live);
  - bstuck_polling_quiet: stuck ⇒ the polling loop's computation never
    changes after that point (same actions forever);
  - bstuck_trace_actions: the trace up to the stuck round has exactly the
    polling loop's actions;
  - brun_two_outcomes: the two outcomes, at the level of the code.
  Nothing in loopBlock2World / loopBlock2 is changed.
*)
Theory loopBlock2Stuck
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncSched2 libModel
  libProg libWorld loopBlock2Model loopBlock2Prog
  loopBlock2Spec loopBlock2World loopBlock2Ffi loopBlock2 cfDiv
  ml_translator mlbasicsProg Word8Prog Word8ArrayProof llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

(* ------------------------------------------------------------------------
   The world
   ------------------------------------------------------------------------ *)

(* The loop blocks after the kept history kept, at stream position pos, and
   no declared byte ever arrives: select blocks forever *)
Definition bstuck_def:
  bstuck c (ws : num -> word8) kept (pos : num) ⇔
    blocks c kept ∧ ∀j. ws (pos + j) ∉ c.interest kept
End

(* No round before n is stuck *)
Definition bfree_def:
  bfree c ws n ⇔
    ∀m kept full pos. m < n ∧ brounds c ws m = (kept, full, pos) ⇒
                      ¬bstuck c ws kept pos
End

Theorem bfree_mono:
  bfree c ws n ∧ m ≤ n ⇒ bfree c ws m
Proof
  rewrite_tac[bfree_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘m'’,‘kept’,‘full’,‘pos’] mp_tac) >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem blk_live_bfree:
  blk_live c ws ⇔ ∀n. bfree c ws n
Proof
  rw[blk_live_def, bfree_def, bstuck_def, EQ_IMP_THM] >>
  TRY (metis_tac[] >> NO_TAC) >>
  first_x_assum (qspecl_then [‘SUC n’, ‘n’, ‘kept’, ‘full’, ‘pos’] mp_tac) >>
  simp[]
QED

(* MAIN: the invariant of loopBlock2World, before the first stuck round *)
Theorem brounds_inv_upto:
  wf c.run ∧ quiet c ⇒
  ∀n kept full pos. bfree c ws n ∧ brounds c ws n = (kept, full, pos) ⇒
                    binv c ws kept full pos
Proof
  strip_tac >> Induct
  >- simp[brounds_def, binv_def, same_for_def, blocked_def, rounds_def] >>
  qx_genl_tac [‘k1’, ‘f1’, ‘p1’] >> strip_tac >>
  ‘∃kept0 full0 pos0. brounds c ws n = (kept0, full0, pos0)’
    by metis_tac[pair_CASES] >>
  ‘bfree c ws n’
    by (qpat_assum ‘bfree c ws (SUC n)’ mp_tac >> rewrite_tac[bfree_def] >>
        rpt strip_tac >>
        first_x_assum (qspecl_then [‘m’, ‘kept’, ‘full’, ‘pos’] mp_tac) >> simp[]) >>
  ‘¬bstuck c ws kept0 pos0’
    by (qpat_assum ‘bfree c ws (SUC n)’ mp_tac >> rewrite_tac[bfree_def] >>
        disch_then (qspecl_then [‘n’, ‘kept0’, ‘full0’, ‘pos0’] mp_tac) >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum ‘brounds c ws (SUC n) = _’ mp_tac >>
  simp[brounds_def] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[binv_def] >>
  qabbrev_tac ‘kept0 = blocked (loop_skip c) [] full0’
  >- ((* blocking round *)
      qabbrev_tac ‘E = c.interest kept0’ >>
      qabbrev_tac ‘j = skips E ws pos0’ >>
      ‘∃j. ws (pos0 + j) ∈ E’
        by (qpat_x_assum ‘¬bstuck _ _ _ _’ mp_tac >>
            simp[bstuck_def, Abbr ‘E’] >> metis_tac[]) >>
      mp_tac (Q.INST [‘pos’ |-> ‘pos0’, ‘E’ |-> ‘E’, ‘ws’ |-> ‘ws’]
                (INST_TYPE [alpha |-> “:word8”] skips_least)) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      ‘same_for c (full0 ++ GENLIST (λi'. idle_snap ws (pos0 + i')) j) kept0 ∧
       blocked (loop_skip c) kept0 (GENLIST (λi'. idle_snap ws (pos0 + i')) j) = kept0 ∧
       rounds c.run ws (LENGTH full0 + j) =
         (full0 ++ GENLIST (λi'. idle_snap ws (pos0 + i')) j, pos0 + j)’
        by (irule skip_snaps >> gvs[Abbr ‘j’, Abbr ‘E’]) >>
      qabbrev_tac ‘sn = idle_snap ws (pos0 + j)’ >>
      ‘¬loop_skip c kept0 sn’
        by gvs[loop_skip_def, Abbr ‘sn’, idle_snap_ready, Abbr ‘E’] >>
      gvs[GENLIST, SNOC_APPEND] >> rpt conj_tac >>
      TRY (irule same_for_keep >> gvs[Abbr ‘sn’] >> NO_TAC) >>
      TRY (gvs[blocked_APPEND, blocked_def, Abbr ‘sn’] >> NO_TAC) >>
      (simp[GSYM ADD_SUC, rounds_SUC] >>
          ‘new_actions (log_of c.run) (full0 ++ GENLIST (λi'. idle_snap ws (i' + pos0)) j) =
           new_actions (log_of c.run) kept0’ by gvs[same_for_def] >>
          gvs[blocks_def, Abbr ‘sn’, idle_snap_def, sdrop_sdrop] >> simp[ADD1]))
  >- ((* polling round *)
      qabbrev_tac ‘sn = world_snap (sdrop pos0 ws)
                          (LENGTH (new_actions (log_of c.run) kept0))’ >>
      ‘¬loop_skip c kept0 sn’ by gvs[loop_skip_def, blocks_def] >>
      rpt conj_tac >>
      TRY (irule same_for_keep >> simp[] >> NO_TAC) >>
      TRY (simp[blocked_APPEND, blocked_def] >> NO_TAC) >>
      (simp[GSYM ADD1, rounds_SUC] >>
          ‘new_actions (log_of c.run) full0 = new_actions (log_of c.run) kept0’
            by gvs[same_for_def] >>
          simp[Abbr ‘sn’]))
QED

(* MAIN: stuck ⇒ the polling loop's computation never changes again: for
   every later number of polling rounds, it is in the state c reached with
   the kept history (so it performs no more actions). *)
Theorem bstuck_polling_quiet:
  wf c.run ∧ quiet c ∧ bfree c ws n ∧ brounds c ws n = (kept, full, pos) ∧
  bstuck c ws kept pos ⇒
  ∀j. c.run (hist c.run ws (LENGTH full + j)) = c.run kept
Proof
  strip_tac >> drule_all brounds_inv_upto >>
  disch_then (assume_tac o REWRITE_RULE [binv_def]) >> gen_tac >>
  ‘same_for c full kept ∧ rounds c.run ws (LENGTH full) = (full, pos)’
    by fs[] >>
  ‘same_for c (full ++ GENLIST (λi'. idle_snap ws (pos + i')) j) kept ∧
   blocked (loop_skip c) kept (GENLIST (λi'. idle_snap ws (pos + i')) j) = kept ∧
   rounds c.run ws (LENGTH full + j) =
     (full ++ GENLIST (λi'. idle_snap ws (pos + i')) j, pos + j)’
    by (irule skip_snaps >> fs[bstuck_def]) >>
  simp[hist_def] >>
  qpat_x_assum ‘same_for c (full ++ _) kept’ mp_tac >> simp[same_for_def] >>
  disch_then (qspec_then ‘[]’ mp_tac o CONJUNCT1) >> simp[]
QED

(* MAIN: the trace up to the stuck round has exactly the actions of c's
   log on the kept history, which (bstuck_polling_quiet) the polling loop
   never goes beyond *)
Theorem bstuck_trace_actions:
  wf c.run ∧ brounds c ws n = (kept, full, pos) ∧ blocks c kept ⇒
  trace_actions (FLAT (GENLIST (bround_events c ws) n)) = (c.run kept).actions
Proof
  Cases_on ‘n’
  >- (rw[brounds_def] >> gvs[blocks_def, new_actions_NIL, log_of_def] >>
      simp[trace_actions_def])
  >> strip_tac >> rename1 ‘SUC m’ >>
  drule trace_actions_brounds >> disch_then (qspecl_then [‘ws’, ‘m’] assume_tac) >>
  ‘∃k0 f0 p0. brounds c ws m = (k0, f0, p0)’ by metis_tac[pair_CASES] >>
  qspecl_then [‘ws’, ‘m’, ‘c’] strip_assume_tac (GEN_ALL brounds_kept_SUC) >>
  gvs[] >>
  ‘log_of c.run k0 ≼ log_of c.run (k0 ++ [s])’ by simp[log_of_def, wf_SNOC_actions] >>
  drule new_actions_prefix >> gvs[blocks_def, log_of_def]
QED

(* ------------------------------------------------------------------------
   The code: select that blocks forever, and the loop
   ------------------------------------------------------------------------ *)

Theorem io2_update_select_diverge:
  (∀j. ws j ∉ set l) ⇒
  io2_update «select» l [b] (io_state ws) = SOME FFIdiverge
Proof
  rw[io2_update_def, io_state_def, LNTH_LGENLIST, n2w_w2n]
QED

Theorem byte_chr_eq[local]:
  byte_chr = CHR o w2n
Proof
  simp[FUN_EQ_THM, byte_chr_def]
QED

(* select on declared events none of which ever arrives: the run ends in an
   FFI divergence of «select» *)
Theorem bselect_stuck_spec:
  limited_parts io2_names p ∧ EVLIST WORD E esv ∧ (∀j. ws j ∉ E) ⇒
  app (p:'ffi ffi_proj) bselect_v [esv] (IOS2 ws evs)
    (POSTf n. λcf b. &(n = «select» ∧ cf = SET_TO_LIST E ∧ b = [0w]) *
                     IOS2 ws evs * SEP_EXISTS bv. W8ARRAY bv [0w])
Proof
  rpt strip_tac >> gvs[EVLIST_def] >>
  ‘io2_update «select» (SET_TO_LIST E) [0w:word8] (io_state ws) = SOME FFIdiverge’
    by (irule io2_update_select_diverge >> gvs[MEM_SET_TO_LIST]) >>
  xcf_with_def (DB.fetch "loopBlock2" "bselect_v_def") >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  xlet ‘POSTv sv. &STRING_TYPE (bytes_str (SET_TO_LIST E)) sv * W8ARRAY bv [0w] *
                  IOS2 ws evs’
  >- (xapp >> xsimpl >> qexists_tac ‘SET_TO_LIST E’ >> simp[] >> EVAL_TAC) >>
  xlet ‘POSTf n. λcf b. &(n = «select» ∧ cf = SET_TO_LIST E ∧ b = [0w]) *
                        IOS2 ws evs * W8ARRAY bv [0w]’
  >- (xffi >> xsimpl >>
      gvs[STRING_TYPE_def, bytes_str_def, byte_chr_eq] >>
      qexistsl [‘SET_TO_LIST E’, ‘emp’, ‘io_state ws’, ‘io2_update’,
                ‘io2_names’, ‘evs’] >>
      gvs[io2_names_def, IOS2_def] >> xsimpl) >>
  xsimpl >> qexists_tac ‘bv’ >> simp[SEP_IMP_REFL]
QED

(* ------------------------------------------------------------------------
   One round, with earlier events (loopBlock2's bstep_spec with an
   arbitrary event history; same proof)
   ------------------------------------------------------------------------ *)

Theorem SNAPSHOT_world_snap[local]:
  WORD (ws k) bv ∧ LIST_TYPE WORD (GENLIST ws k) rsv ∧ NUM 0 nv ⇒
  SNAPSHOT BREADY1 WORD (world_snap ws k) (Conv NONE [bv; nv; rsv])
Proof
  simp[SNAPSHOT_def, world_snap_def, BREADY1_def]
QED

Theorem bstep_spec_ev:
  limited_parts io2_names p ∧
  COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) c cv ∧
  (blocks c [] ⇒ ∃j. ws j ∈ c.interest []) ⇒
  app (p:'ffi ffi_proj) bstep_v [cv] (IOS2 ws evs)
    (POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                 (suspended2 c [FST (bstep_world c ws)]) v *
              IOS2 (sdrop (FST (SND (bstep_world c ws))) ws)
                   (evs ++ SND (SND (bstep_world c ws))))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP2 _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP2_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (DB.fetch "loopBlock2" "bstep_v_def") >> xmatch >>
  qabbrev_tac ‘k = LENGTH (c.run []).actions’ >>
  xlet ‘POSTv rsv. &LIST_TYPE WORD (GENLIST ws k) rsv *
          IOS2 (sdrop k ws) (evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k))’
  >- (xapp >> qexistsl [‘emp’, ‘ws’, ‘evs’, ‘(c.run []).actions’] >>
      simp[Abbr ‘k’] >> xsimpl) >>
  qpat_x_assum ‘STEPA2 _ _ _ _ _ _ _’ mp_tac >> simp[Once STEPA2_cases] >>
  strip_tac >> gvs[]
  >- ((* Done2: never blocks; reads the ready byte *)
      ‘¬blocks c []’ by gvs[blocks_def, finished_def] >>
      simp[bstep_world_def] >>
      xlet ‘POSTv bv. &WORD (ws k) bv * IOS2 (sdrop 1 (sdrop k ws))
              (evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
      >- (xmatch >> xlet ‘POSTv u. &UNIT_TYPE () u *
                            IOS2 (sdrop k ws)
                              (evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k))’
          >- (xcon >> xsimpl) >>
          xapp >> qexistsl [‘emp’, ‘sdrop k ws’,
                            ‘evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k)’] >>
          ‘sdrop k ws 0 = ws k’ by simp[sdrop_def] >> simp[] >> xsimpl) >>
      xlet ‘POSTv wv. &SNAPSHOT BREADY1 WORD (world_snap ws k) wv *
              IOS2 (sdrop 1 (sdrop k ws))
                (evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
      >- (xcon >> xsimpl >> irule SNAPSHOT_world_snap >> simp[NUM_def, INT_def]) >>
      ‘app p poll2_v [Conv NONE [av; Done2V xv]; wv] emp
         (POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                     (suspended2 c [world_snap ws k]) v)’
        by (irule poll2_spec >> simp[]) >>
      qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl >>
      qunabbrev_tac ‘k’ >>
      fs[sdrop_sdrop, round_events_of_def, finished_def] >> xsimpl)
  >- ((* Pending2 *)
      Cases_on ‘(c.run []).actions = []’
      >- ((* no action to perform: block in select *)
          ‘blocks c []’ by gvs[blocks_def, new_actions_NIL, log_of_def] >>
          qunabbrev_tac ‘k’ >> gvs[LIST_TYPE_def] >> simp[bstep_world_def] >>
          qabbrev_tac ‘jb = skips (c.interest []) ws 0’ >>
          xlet ‘POSTv bv. &WORD (ws jb) bv *
                  IOS2 (sdrop (SUC jb) ws)
                    (evs ++ [select_event (SET_TO_LIST (c.interest [])) (ws jb)])’
          >- (xmatch >> xmatch >> xapp >>
              qexistsl [‘emp’, ‘ws’, ‘evs’, ‘c.interest []’] >>
              fs[Abbr ‘jb’] >> conj_tac >- metis_tac[] >> xsimpl) >>
          xlet ‘POSTv wv. &SNAPSHOT BREADY1 WORD (idle_snap ws jb) wv *
                  IOS2 (sdrop (SUC jb) ws)
                    (evs ++ [select_event (SET_TO_LIST (c.interest [])) (ws jb)])’
          >- (xcon >> xsimpl >>
              simp[SNAPSHOT_def, idle_snap_def, world_snap_def, BREADY1_def,
                   NUM_def, INT_def, LIST_TYPE_def, sdrop_def]) >>
          qpat_x_assum ‘COMP2 _ _ _ _ _ c _’ assume_tac >>
          drule_all poll2_spec >> strip_tac >>
          qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl)
      >- ((* actions to perform: poll *)
          Cases_on ‘(c.run []).actions’ >> gvs[LIST_TYPE_def] >>
          ‘¬blocks c []’ by gvs[blocks_def, new_actions_NIL, log_of_def] >>
          simp[bstep_world_def] >>
          xlet ‘POSTv bv. &WORD (ws k) bv * IOS2 (sdrop 1 (sdrop k ws))
                  (evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
          >- (xmatch >> xmatch >>
              xlet ‘POSTv u. &UNIT_TYPE () u *
                      IOS2 (sdrop k ws)
                        (evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k))’
              >- (xcon >> xsimpl) >>
              xapp >> qexistsl [‘emp’, ‘sdrop k ws’,
                                ‘evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k)’] >>
              ‘sdrop k ws 0 = ws k’ by simp[sdrop_def] >> simp[] >> xsimpl) >>
          xlet ‘POSTv wv. &SNAPSHOT BREADY1 WORD (world_snap ws k) wv *
                  IOS2 (sdrop 1 (sdrop k ws))
                    (evs ++ MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
          >- (xcon >> xsimpl >> irule SNAPSHOT_world_snap >> simp[NUM_def, INT_def]) >>
          qpat_x_assum ‘COMP2 _ _ _ _ _ c _’ assume_tac >>
          drule_all poll2_spec >> strip_tac >>
          qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl >>
          simp[sdrop_sdrop, round_events_of_def, Abbr ‘k’] >> xsimpl))
QED

(* ------------------------------------------------------------------------
   The round in which select blocks forever, and the loop
   ------------------------------------------------------------------------ *)

Theorem bstep_stuck_spec:
  limited_parts io2_names p ∧
  COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) c cv ∧
  blocks c [] ∧ (∀j. ws j ∉ c.interest []) ⇒
  app (p:'ffi ffi_proj) bstep_v [cv] (IOS2 ws evs)
    (POSTf n. λcf b. &(n = «select» ∧ cf = SET_TO_LIST (c.interest []) ∧ b = [0w]) *
                     IOS2 ws evs * SEP_EXISTS bv. W8ARRAY bv [0w])
Proof
  rpt strip_tac >>
  ‘(c.run []).actions = [] ∧ (c.run []).result = NONE’
    by gvs[blocks_def, new_actions_NIL, log_of_def] >>
  qpat_assum ‘COMP2 _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP2_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (DB.fetch "loopBlock2" "bstep_v_def") >> xmatch >>
  xlet ‘POSTv rsv. &LIST_TYPE WORD ([] : word8 list) rsv * IOS2 ws evs’
  >- (xapp >> qexistsl [‘emp’, ‘ws’, ‘evs’, ‘[]’] >> gvs[LIST_TYPE_def] >> xsimpl >>
      simp[LIST_TYPE_def]) >>
  qpat_x_assum ‘STEPA2 _ _ _ _ _ _ _’ mp_tac >> simp[Once STEPA2_cases] >>
  strip_tac >> gvs[finished_def, LIST_TYPE_def] >>
  xlet ‘POSTf n. λcf b. &(n = «select» ∧ cf = SET_TO_LIST (c.interest []) ∧ b = [0w]) *
                        IOS2 ws evs * SEP_EXISTS bv. W8ARRAY bv [0w]’
  >- (xmatch >> xmatch >> xapp_spec bselect_stuck_spec >> simp[] >>
      TRY (qexistsl [‘emp’, ‘ws’, ‘evs’, ‘c.interest []’]) >> xsimpl >>
      metis_tac[]) >>
  xsimpl
QED

Theorem brounds_SUC_SND[local]:
  ∀n. ∃h. FST (brounds c ws (SUC n)) = FST (brounds c ws n) ++ [h]
Proof
  metis_tac[brounds_kept_SUC]
QED

Theorem FLAT_GENLIST_SUC[local]:
  FLAT (GENLIST f (SUC n)) = FLAT (GENLIST f n) ++ f n
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

(* MAIN (outcome 2): the loop blocks forever in select in round n (the first
   stuck round): the run ends in an FFI divergence of «select» on c's
   declared events, after the events of the first n rounds. *)
Theorem brun_stuck_spec:
  limited_parts io2_names p ∧ wf c.run ∧
  bfree c ws n ∧ brounds c ws n = (kept, full, pos) ∧ bstuck c ws kept pos ∧
  COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) c cv ⇒
  app (p:'ffi ffi_proj) brun_v [cv] (IOS2 ws [])
    (POSTf nm. λcf b.
       &(nm = «select» ∧ cf = SET_TO_LIST (c.interest kept) ∧ b = [0w]) *
       IOS2 (sdrop pos ws) (FLAT (GENLIST (bround_events c ws) n)) *
       SEP_EXISTS bv. W8ARRAY bv [0w])
Proof
  strip_tac >>
  ‘∀j i k1 f1 p1 cv.
     i + j = n ∧ brounds c ws i = (k1, f1, p1) ∧
     COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) (suspended2 c k1) cv ⇒
     app p brun_v [cv]
       (IOS2 (sdrop p1 ws) (FLAT (GENLIST (bround_events c ws) i)))
       (POSTf nm. λcf b.
          &(nm = «select» ∧ cf = SET_TO_LIST (c.interest kept) ∧ b = [0w]) *
          IOS2 (sdrop pos ws) (FLAT (GENLIST (bround_events c ws) n)) *
          SEP_EXISTS bv. W8ARRAY bv [0w])’
    suffices_by (disch_then (qspecl_then [‘n’, ‘0’] mp_tac) >>
                 simp[brounds_def]) >>
  Induct
  >- ((* round n: select blocks forever *)
      rpt strip_tac >> ‘i = n’ by simp[] >> pop_assum SUBST_ALL_TAC >>
      ‘k1 = kept ∧ p1 = pos’ by gvs[] >>
      qpat_x_assum ‘k1 = kept’ SUBST_ALL_TAC >>
      qpat_x_assum ‘p1 = pos’ SUBST_ALL_TAC >>
      drule blocks_suspended2 >> strip_tac >>
      xcf_with_def (DB.fetch "loopBlock2" "brun_v_def") >>
      xlet ‘POSTf nm. λcf b.
              &(nm = «select» ∧ cf = SET_TO_LIST (c.interest kept) ∧ b = [0w]) *
              IOS2 (sdrop pos ws) (FLAT (GENLIST (bround_events c ws) n)) *
              SEP_EXISTS bv. W8ARRAY bv [0w]’
      >- (‘app p bstep_v [cv']
             (IOS2 (sdrop pos ws) (FLAT (GENLIST (bround_events c ws) n)))
             (POSTf nm. λcf b.
                &(nm = «select» ∧ cf = SET_TO_LIST ((suspended2 c kept).interest []) ∧
                  b = [0w]) *
                IOS2 (sdrop pos ws) (FLAT (GENLIST (bround_events c ws) n)) *
                SEP_EXISTS bv. W8ARRAY bv [0w])’
            by (irule bstep_stuck_spec >> gvs[bstuck_def, sdrop_def] >>
                metis_tac[ADD_COMM]) >>
          qpat_x_assum ‘app _ bstep_v _ _ _’ xapp_spec >> gvs[] >> xsimpl) >>
      xsimpl)
  >- ((* round i < n returns *)
      rpt strip_tac >>
      ‘bfree c ws (SUC i)’
        by (irule bfree_mono >> qexists_tac ‘n’ >> simp[]) >>
      ‘¬bstuck c ws k1 p1’
        by (qpat_x_assum ‘bfree c ws n’ mp_tac >> rewrite_tac[bfree_def] >>
            disch_then (qspecl_then [‘i’, ‘k1’, ‘f1’, ‘p1’] mp_tac) >> simp[]) >>
      drule_all bstep_world_brounds >> strip_tac >>
      drule blocks_suspended2 >> strip_tac >>
      ‘∃k2 f2 p2. brounds c ws (SUC i) = (k2, f2, p2)’ by metis_tac[pair_CASES] >>
      gvs[] >>
      qabbrev_tac ‘bw = bstep_world (suspended2 c k1) (sdrop p1 ws)’ >>
      ‘app p bstep_v [cv'] (IOS2 (sdrop p1 ws) (FLAT (GENLIST (bround_events c ws) i)))
         (POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                      (suspended2 (suspended2 c k1) [FST bw]) v *
                   IOS2 (sdrop (FST (SND bw)) (sdrop p1 ws))
                     (FLAT (GENLIST (bround_events c ws) i) ++ SND (SND bw)))’
        by (simp[Abbr ‘bw’] >> irule bstep_spec_ev >> simp[] >>
            gvs[bstuck_def, sdrop_def] >> rpt strip_tac >> gvs[] >>
            metis_tac[ADD_COMM]) >>
      xcf_with_def (DB.fetch "loopBlock2" "brun_v_def") >>
      xlet ‘POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                        (suspended2 c (k1 ++ [FST bw])) v *
                      IOS2 (sdrop (p1 + FST (SND bw)) ws)
                        (FLAT (GENLIST (bround_events c ws) (SUC i)))’
      >- (qpat_x_assum ‘app _ bstep_v _ _ _’ xapp_spec >> xsimpl >>
          simp[suspended2_suspended2_one, sdrop_sdrop, FLAT_GENLIST_SUC] >> xsimpl) >>
      first_x_assum (qspecl_then [‘SUC i’, ‘k1 ++ [FST bw]’, ‘f2’,
                                  ‘p1 + FST (SND bw)’, ‘v’] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >> xapp)
QED

(* MAIN: the blocking loop's two outcomes, without blk_live.  Either
   blk_live holds (so brun_spec applies: the loop diverges, with the
   polling loop's actions, blocking_trace_same_actions), or in some round n
   (the first stuck one) no declared byte ever arrives: the run ends in an
   FFI divergence of select after the events of the first n rounds, whose
   actions are c's log on the kept history (bstuck_trace_actions), which
   the polling loop never goes beyond (bstuck_polling_quiet). *)
(* If some round is stuck, there is a first stuck round *)
Theorem bfree_first_stuck:
  (∃n. ¬bfree c ws n) ⇒
  ∃m kept full pos.
    bfree c ws m ∧ brounds c ws m = (kept,full,pos) ∧ bstuck c ws kept pos
Proof
  strip_tac >>
  ‘∃m. ¬bfree c ws (SUC m) ∧ bfree c ws m’
    by (pop_assum mp_tac >> qid_spec_tac ‘n’ >> Induct >- simp[bfree_def] >>
        metis_tac[]) >>
  ‘∃kept full pos. brounds c ws m = (kept, full, pos)’ by metis_tac[pair_CASES] >>
  qexistsl [‘m’, ‘kept’, ‘full’, ‘pos’] >> asm_rewrite_tac[] >>
  qpat_x_assum ‘¬bfree c ws (SUC m)’ mp_tac >>
  qpat_x_assum ‘bfree c ws m’ mp_tac >>
  PURE_REWRITE_TAC[bfree_def, NOT_FORALL_THM, NOT_IMP] >> rpt strip_tac >>
  qpat_x_assum ‘¬∀m'. _’
    (strip_assume_tac o SIMP_RULE bool_ss [NOT_FORALL_THM, NOT_IMP]) >>
  Cases_on ‘m' < m’ >- metis_tac[] >>
  ‘m' = m’ by decide_tac >> gvs[]
QED

Theorem brun_two_outcomes:
  limited_parts io2_names p ∧ wf c.run ∧
  COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) c cv ⇒
  (blk_live c ws ∧
   app (p:'ffi ffi_proj) brun_v [cv] (IOS2 ws [])
     (POSTd io. io = LFLATTEN (LGENLIST (λi. fromList (bround_events c ws i)) NONE))) ∨
  (∃n kept full pos.
     bfree c ws n ∧ brounds c ws n = (kept, full, pos) ∧ bstuck c ws kept pos ∧
     app (p:'ffi ffi_proj) brun_v [cv] (IOS2 ws [])
       (POSTf nm. λcf b.
          &(nm = «select» ∧ cf = SET_TO_LIST (c.interest kept) ∧ b = [0w]) *
          IOS2 (sdrop pos ws) (FLAT (GENLIST (bround_events c ws) n)) *
          SEP_EXISTS bv. W8ARRAY bv [0w]))
Proof
  strip_tac >> Cases_on ‘blk_live c ws’
  >- (disj1_tac >> asm_rewrite_tac[] >> irule brun_spec >> asm_rewrite_tac[] >>
      metis_tac[]) >>
  disj2_tac >>
  ‘∃n. ¬bfree c ws n’ by metis_tac[blk_live_bfree] >>
  ‘∃m kept full pos.
     bfree c ws m ∧ brounds c ws m = (kept,full,pos) ∧ bstuck c ws kept pos’
    by metis_tac[bfree_first_stuck] >>
  qexistsl [‘m’, ‘kept’, ‘full’, ‘pos’] >> asm_rewrite_tac[] >>
  irule brun_stuck_spec >> asm_rewrite_tac[] >> metis_tac[]
QED
