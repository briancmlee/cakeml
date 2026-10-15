(*
  The world of the blocking event loop, and why blocking is sound.

  The world is cf-actions' byte stream (asyncCfActWorld): responses and
  ready bytes are read from one stream ws in order; a polling round reads
  one ready byte b, and the snapshot's ready set is {b}.  The blocking
  loop adds a `select` call: when the computation c has no action to
  perform and has not finished, the loop does not poll every round but
  blocks until a byte in c's declared interest appears, letting the
  rounds with other bytes pass.

  brounds c ws n = (kept, full, pos) after n rounds of the blocking loop:
  - kept: the snapshots c is actually polled with;
  - full: the snapshots of the rounds the world went through, i.e. the
    history of the *polling* loop (cf-actions) over the same stream;
  - pos: how much of the stream has been consumed.

  MAIN results:
  - brounds_full: full is exactly the polling loop's history (hist), and
    the stream positions agree;
  - brounds_blocked: kept = blocked loop_skip [] full, the model's own
    `blocked` (async/model/asyncSched2Script.sml);
  - blocking_same_actions: the blocking loop emits exactly the polling
    loop's actions and reaches the same result (via blocked_sound /
    same_for, i.e. the model's no-busy-waiting argument).
  All under one named assumption, blk_live: whenever the loop blocks, a
  declared byte eventually appears in the stream.
*)
Theory asyncL2BlkWorld
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncSched2 asyncCfActModel
  asyncCfActWorld asyncL2BlkModel
Libs
  preamble

(* The loop blocks through snapshot s, after the kept history h, when c
   has no action to perform, has not finished, and none of its declared
   events is ready (and s carries no responses). *)
Definition loop_skip_def:
  loop_skip c h s ⇔
    new_actions (log_of c.run) h = [] ∧ (c.run h).result = NONE ∧
    DISJOINT (c.interest h) s.ready ∧ s.results = []
End

Theorem loop_skip_irrelevant:
  loop_skip c h s ⇒ irrelevant c h s
Proof
  rw[loop_skip_def, irrelevant_def]
QED

(* The loop blocks in a round after the kept history h *)
Definition blocks_def:
  blocks c h ⇔ new_actions (log_of c.run) h = [] ∧ (c.run h).result = NONE
End

(* The empty-results snapshot of the stream position p *)
Definition idle_snap_def:
  idle_snap ws p = world_snap (sdrop p ws) 0
End

(* How many bytes select skips at position pos, for interest E *)
Definition skips_def:
  skips E ws pos = LEAST j. ws (pos + j) ∈ E
End

Definition brounds_def:
  brounds c ws 0 = ([], [], 0n) ∧
  brounds c ws (SUC n) =
    let (kept, full, pos) = brounds c ws n;
        k = LENGTH (new_actions (log_of c.run) kept)
    in if blocks c kept then
         let j = skips (c.interest kept) ws pos in
           (kept ++ [idle_snap ws (pos + j)],
            full ++ GENLIST (λi. idle_snap ws (pos + i)) (SUC j),
            pos + j + 1)
       else
         (kept ++ [world_snap (sdrop pos ws) k],
          full ++ [world_snap (sdrop pos ws) k],
          pos + k + 1)
End

(* ASSUMPTION blk_live: whenever the loop blocks, a byte c declares
   eventually appears in the stream (select returns). *)
Definition blk_live_def:
  blk_live c ws ⇔
    ∀n kept full pos. brounds c ws n = (kept, full, pos) ∧ blocks c kept ⇒
                      ∃j. ws (pos + j) ∈ c.interest kept
End

(* ------------------------------------------------------------------------
   blocked over appended histories
   ------------------------------------------------------------------------ *)

Theorem blocked_APPEND:
  ∀xs kept. blocked skip kept (xs ++ ys) = blocked skip (blocked skip kept xs) ys
Proof
  Induct >> simp[blocked_def]
QED


(* ------------------------------------------------------------------------
   The blocking round, one skipped snapshot at a time
   ------------------------------------------------------------------------ *)

Theorem idle_snap_ready:
  (idle_snap ws p).ready = {ws p} ∧ (idle_snap ws p).results = []
Proof
  simp[idle_snap_def, world_snap_def, sdrop_def]
QED

Theorem skips_least:
  (∃j. ws (pos + j) ∈ E) ⇒
  ws (pos + skips E ws pos) ∈ E ∧ ∀i. i < skips E ws pos ⇒ ws (pos + i) ∉ E
Proof
  strip_tac >> simp[skips_def] >> conj_tac
  >- (numLib.LEAST_ELIM_TAC >> metis_tac[ADD_COMM])
  >- (rpt strip_tac >> drule_at Any WhileTheory.LESS_LEAST >> simp[])
QED

Theorem same_for_skip:
  wf c.run ∧ quiet c ∧ same_for c full kept ∧ loop_skip c kept s ⇒
  same_for c (full ++ [s]) kept
Proof
  strip_tac >>
  mp_tac (Q.INST [‘skip’ |-> ‘loop_skip c’] same_for_step) >>
  simp[loop_skip_irrelevant]
QED

Theorem same_for_keep:
  wf c.run ∧ quiet c ∧ same_for c full kept ∧ ¬loop_skip c kept s ⇒
  same_for c (full ++ [s]) (kept ++ [s])
Proof
  strip_tac >>
  mp_tac (Q.INST [‘skip’ |-> ‘loop_skip c’] same_for_step) >>
  simp[loop_skip_irrelevant]
QED

(* The invariant: same_for, kept is blocked full, and full is the polling
   loop's history with the same stream position *)
Definition binv_def:
  binv c ws kept full pos ⇔
    same_for c full kept ∧ kept = blocked (loop_skip c) [] full ∧
    rounds c.run ws (LENGTH full) = (full, pos)
End

(* Skipping i idle snapshots keeps the invariant (except kept/blocked,
   handled at the end of the round) *)
Theorem skip_snaps:
  wf c.run ∧ quiet c ∧ blocks c kept ∧
  same_for c full kept ∧ rounds c.run ws (LENGTH full) = (full, pos) ∧
  (∀i'. i' < i ⇒ ws (pos + i') ∉ c.interest kept) ⇒
  same_for c (full ++ GENLIST (λi'. idle_snap ws (pos + i')) i) kept ∧
  blocked (loop_skip c) kept (GENLIST (λi'. idle_snap ws (pos + i')) i) = kept ∧
  rounds c.run ws (LENGTH full + i) =
    (full ++ GENLIST (λi'. idle_snap ws (pos + i')) i, pos + i)
Proof
  strip_tac >> Induct_on ‘i’ >- simp[blocked_def] >>
  strip_tac >> gvs[] >>
  ‘loop_skip c kept (idle_snap ws (i + pos))’
    by gvs[loop_skip_def, blocks_def, idle_snap_ready] >>
  simp[GENLIST, SNOC_APPEND, blocked_APPEND, blocked_def] >>
  conj_tac
  >- (irule same_for_skip >> simp[])
  >- (simp[GSYM ADD_SUC, rounds_SUC] >>
      ‘new_actions (log_of c.run) (full ++ GENLIST (λi'. idle_snap ws (pos + i')) i) =
       new_actions (log_of c.run) kept’ by gvs[same_for_def] >>
      gvs[blocks_def, idle_snap_def, sdrop_sdrop] >> simp[ADD1])
QED

(* MAIN: the invariant holds after every round of the blocking loop *)
Theorem brounds_inv:
  wf c.run ∧ quiet c ∧ blk_live c ws ⇒
  ∀n kept full pos. brounds c ws n = (kept, full, pos) ⇒ binv c ws kept full pos
Proof
  strip_tac >> Induct
  >- simp[brounds_def, binv_def, same_for_def, blocked_def, rounds_def] >>
  qx_genl_tac [‘k1’, ‘f1’, ‘p1’] >>
  ‘∃kept0 full0 pos0. brounds c ws n = (kept0, full0, pos0)’
    by metis_tac[pair_CASES] >>
  first_x_assum drule >> strip_tac >>
  simp[brounds_def] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[binv_def] >>
  qabbrev_tac ‘kept0 = blocked (loop_skip c) [] full0’
  >- ((* blocking round *)
      qabbrev_tac ‘E = c.interest kept0’ >>
      qabbrev_tac ‘j = skips E ws pos0’ >>
      ‘∃j. ws (pos0 + j) ∈ E’ by (gvs[blk_live_def, Abbr ‘E’] >> metis_tac[]) >>
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

(* MAIN: the blocking loop is the polling loop with the idle rounds
   skipped.  After n rounds of the blocking loop, the world has gone
   through the polling loop's history over the same stream
   (hist c.run ws (LENGTH full)), the computation has been polled with
   exactly the model's blocked subsequence of it, and it has emitted the
   same actions and reached the same result as under polling. *)
Theorem blocking_same_actions:
  wf c.run ∧ quiet c ∧ blk_live c ws ∧ brounds c ws n = (kept, full, pos) ⇒
  full = hist c.run ws (LENGTH full) ∧
  kept = blocked (loop_skip c) [] full ∧
  c.run kept = c.run full
Proof
  strip_tac >> drule_all brounds_inv >> simp[binv_def, hist_def] >>
  strip_tac >> fs[same_for_def] >>
  first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]
QED
