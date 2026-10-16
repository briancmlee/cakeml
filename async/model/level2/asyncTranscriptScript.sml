(*
  Transcripts: a computation's action log, with each action paired with
  its response.

  The response to an action emitted in round n is in snapshot n+1, at the
  action's position in round n's batch (positional routing).  So the
  transcript pairs round n's actions with snapshot n+1's results, in order;
  an action whose response has not arrived yet (or that the world did not
  answer) is paired with NONE.

     trans m h : ('act # 'r option) list       (MAP FST = the action log)

  How transcripts compose:
   - bind: the transcript of m, then that of f x (for settled m);
   - both: per round, the left side's pairs then the right side's.  So for
     any property of pairs that one side never has, filtering the
     transcript of both gives the filtered transcript of the other side
     (trans_both_filter_left/right).  This is what keeps the echo server's
     connections apart.
*)
Theory asyncTranscript
Ancestors
  combin pair list rich_list arithmetic option asyncCore asyncLevel1 asyncLevel2
Libs
  BasicProvers

(* Pair actions with responses, in order *)
Definition zipr_def:
  zipr [] rs = [] ∧
  zipr (a :: as) rs = (a, oHD rs) :: zipr as (DROP 1 rs)
End

(* The responses to round n's actions: snapshot n+1's results *)
Definition responses_at_def:
  responses_at h n = if n < LENGTH h then (EL n h).results else []
End

Definition round_trans_def:
  round_trans m h n = zipr (new_actions (log_of m) (TAKE n h)) (responses_at h n)
End

(* The transcript of m after the snapshots h: rounds 0 .. LENGTH h *)
Definition trans_def:
  trans m h = FLAT (GENLIST (round_trans m h) (SUC (LENGTH h)))
End

Theorem zipr_APPEND:
  ∀a1 a2 rs. zipr (a1 ++ a2) rs =
             zipr a1 (TAKE (LENGTH a1) rs) ++ zipr a2 (DROP (LENGTH a1) rs)
Proof
  Induct >> simp[zipr_def] >> rpt gen_tac
  >> Cases_on ‘rs’ >> simp[zipr_def]
QED

Theorem MAP_FST_zipr[simp]:
  ∀as rs. MAP FST (zipr as rs) = as
Proof
  Induct >> simp[zipr_def]
QED

(* The transcript is the action log, annotated with responses *)
Theorem MAP_FST_trans:
  wf m ⇒ MAP FST (trans m h) = (m h).actions
Proof
  strip_tac >> qid_spec_tac ‘h’ >> Induct_on ‘h’ using SNOC_INDUCT
  >- simp[trans_def, round_trans_def, new_actions_NIL, log_of_def]
  >> rpt strip_tac >> pop_assum mp_tac
  >> simp[trans_def, GENLIST, SNOC_APPEND, MAP_FLAT, MAP_GENLIST, o_DEF,
          round_trans_def]
  >> ‘GENLIST (λn. new_actions (log_of m) (TAKE n (h ++ [x]))) (LENGTH h) =
      GENLIST (λn. new_actions (log_of m) (TAKE n h)) (LENGTH h)’
       by simp[GENLIST_FUN_EQ, TAKE_APPEND1]
  >> simp[TAKE_LENGTH_APPEND] >> strip_tac
  >> qspecl_then [‘log_of m’, ‘h’, ‘x’] mp_tac
       (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
  >> simp[log_of_def, wf_SNOC_actions]
QED

(* ------------------------------------------------------------------------
   Primitives and map
   ------------------------------------------------------------------------ *)

Theorem trans_wait[simp]:
  trans (wait p) h = []
Proof
  simp[trans_def, round_trans_def, FLAT_EQ_NIL, EVERY_GENLIST]
  >> rw[] >> Cases_on ‘TAKE i h’ using SNOC_CASES
  >> simp[new_actions_def, log_of_def, wait_def, zipr_def]
QED

Theorem trans_return[simp]:
  trans (return x) h = []
Proof
  simp[trans_def, round_trans_def, FLAT_EQ_NIL, EVERY_GENLIST]
  >> rw[] >> simp[new_actions_def, log_of_def, return_def, zipr_def]
QED

Theorem trans_emit:
  trans (emit a) h = [(a, if h = [] then NONE else oHD (HD h).results)]
Proof
  simp[trans_def, GENLIST_CONS, round_trans_def, new_actions_NIL, log_of_def,
       emit_def, zipr_def, responses_at_def]
  >> Cases_on ‘h’ >> simp[]
  >> simp[FLAT_EQ_NIL, EVERY_GENLIST]
  >> rw[round_trans_def, new_actions_def, log_of_def, emit_def, zipr_def]
QED

Theorem trans_map[simp]:
  trans (map f m) h = trans m h
Proof
  ‘round_trans (map f m) = round_trans m’ by simp[FUN_EQ_THM, round_trans_def]
  >> simp[trans_def]
QED

(* ------------------------------------------------------------------------
   bind
   ------------------------------------------------------------------------ *)

(* Before m finishes, bind's transcript is m's *)
Theorem trans_bind_running:
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒
  trans (bind m f) h = trans m h
Proof
  rw[trans_def] >> AP_TERM_TAC >> simp[GENLIST_FUN_EQ, round_trans_def]
  >> rpt strip_tac >> AP_THM_TAC >> AP_TERM_TAC
  >> irule new_actions_bind_running
  >> rw[TAKE_TAKE_MIN, LENGTH_TAKE_EQ] >> first_x_assum irule
  >> gvs[MIN_DEF] >> rw[]
QED

(* MAIN: once a settled m has finished, bind's transcript is m's, then the
   continuation's *)
Theorem trans_bind_continues:
  wf m ∧ settled m ∧ first_done m h1 x ⇒
  trans (bind m f) (h1 ++ h2) = trans m h1 ++ trans (f x) h2
Proof
  strip_tac
  >> ‘new_actions (log_of m) h1 = []’ by gvs[settled_def, first_done_def]
  (* the rounds before m finished are m's *)
  >> ‘GENLIST (round_trans (bind m f) (h1 ++ h2)) (LENGTH h1) =
      GENLIST (round_trans m h1) (LENGTH h1)’
       by (simp[GENLIST_FUN_EQ, round_trans_def] >> rpt strip_tac
           >> simp[TAKE_APPEND1, responses_at_def, EL_APPEND1]
           >> AP_THM_TAC >> AP_TERM_TAC
           >> irule new_actions_bind_running
           >> rw[TAKE_TAKE_MIN, LENGTH_TAKE_EQ] >> gvs[first_done_def]
           >> first_x_assum irule >> gvs[MIN_DEF] >> rw[])
  (* from the round in which m finished, they are f x's *)
  >> ‘GENLIST (λt. round_trans (bind m f) (h1 ++ h2) (t + LENGTH h1)) (SUC (LENGTH h2)) =
      GENLIST (round_trans (f x) h2) (SUC (LENGTH h2))’
       by (simp[GENLIST_FUN_EQ, round_trans_def] >> rpt strip_tac
           >> rename1 ‘t < SUC (LENGTH h2)’
           >> simp[responses_at_def, EL_APPEND2]
           >> ‘TAKE (t + LENGTH h1) (h1 ++ h2) = h1 ++ TAKE t h2’
                by simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
           >> simp[]
           >> Cases_on ‘t = 0’
           >- (gvs[] >> drule_all new_actions_bind_at
               >> disch_then (qspec_then ‘f’ SUBST1_TAC)
               >> simp[new_actions_NIL, log_of_def])
           >> ‘TAKE t h2 ≠ []’ by (Cases_on ‘h2’ >> gvs[])
           >> qspecl_then [‘m’, ‘h1’, ‘x’, ‘TAKE t h2’, ‘f’] mp_tac
                (Q.GENL [‘m’, ‘h1’, ‘x’, ‘q’, ‘f’] new_actions_bind_after)
           >> simp[])
  (* m's round in which it finished contributes nothing (m is settled) *)
  >> ‘FLAT (GENLIST (round_trans m h1) (SUC (LENGTH h1))) =
      FLAT (GENLIST (round_trans m h1) (LENGTH h1))’
       by simp[GENLIST, SNOC_APPEND, round_trans_def, TAKE_LENGTH_ID, zipr_def]
  >> simp[trans_def]
  >> ‘SUC (LENGTH h1 + LENGTH h2) = SUC (LENGTH h2) + LENGTH h1’ by simp[]
  >> pop_assum SUBST1_TAC
  >> REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >> ASM_REWRITE_TAC[]
QED

(* ------------------------------------------------------------------------
   both
   ------------------------------------------------------------------------ *)

Theorem new_actions_both:
  new_actions (log_of (both m1 m2)) h =
    new_actions (log_of m1) (left_view m1 m2 h) ++
    new_actions (log_of m2) (right_view m1 m2 h)
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, both_def, par_log_def, par_actions_NIL,
          left_view_def, right_view_def]
  >> simp[SNOC_APPEND, both_new_actions]
QED

Theorem views_TAKE:
  left_view m1 m2 (TAKE n h) = TAKE n (left_view m1 m2 h) ∧
  right_view m1 m2 (TAKE n h) = TAKE n (right_view m1 m2 h)
Proof
  simp[left_view_def, right_view_def, par_views_TAKE]
QED

Theorem responses_at_views:
  responses_at (left_view m1 m2 h) n =
    TAKE (LENGTH (new_actions (log_of m1) (left_view m1 m2 (TAKE n h))))
         (responses_at h n) ∧
  responses_at (right_view m1 m2 h) n =
    DROP (LENGTH (new_actions (log_of m1) (left_view m1 m2 (TAKE n h))))
         (responses_at h n)
Proof
  simp[responses_at_def] >> Cases_on ‘n < LENGTH h’ >> simp[]
  >> ‘TAKE (n + 1) h = TAKE n h ++ [EL n h]’ by simp[TAKE_EL_SNOC, SNOC_APPEND]
  >> ‘EL n (left_view m1 m2 h) = EL n (left_view m1 m2 (TAKE (n + 1) h)) ∧
      EL n (right_view m1 m2 h) = EL n (right_view m1 m2 (TAKE (n + 1) h))’
       by simp[views_TAKE, EL_TAKE]
  >> pop_assum (fn th => REWRITE_TAC[th])
  >> pop_assum (fn th => REWRITE_TAC[th])
  >> simp[left_view_SNOC_eq, right_view_SNOC_eq, EL_APPEND2]
QED

(* Each round, both's transcript is the left side's, then the right side's *)
Theorem round_trans_both:
  round_trans (both m1 m2) h n =
    round_trans m1 (left_view m1 m2 h) n ++ round_trans m2 (right_view m1 m2 h) n
Proof
  simp[round_trans_def, new_actions_both, zipr_APPEND, responses_at_views,
       views_TAKE]
QED

Theorem FILTER_FLAT_GENLIST_APPEND[local]:
  ∀k. (∀n. n < k ⇒ FILTER Q (g n) = []) ⇒
      FILTER Q (FLAT (GENLIST (λn. f n ++ g n) k)) = FILTER Q (FLAT (GENLIST f k))
Proof
  Induct >> simp[GENLIST, SNOC_APPEND, FILTER_APPEND_DISTRIB]
QED

Theorem FILTER_FLAT_GENLIST_APPEND'[local]:
  ∀k. (∀n. n < k ⇒ FILTER Q (f n) = []) ⇒
      FILTER Q (FLAT (GENLIST (λn. f n ++ g n) k)) = FILTER Q (FLAT (GENLIST g k))
Proof
  Induct >> simp[GENLIST, SNOC_APPEND, FILTER_APPEND_DISTRIB]
QED

Theorem FILTER_FLAT_GENLIST_NIL[local]:
  FILTER Q (FLAT (GENLIST g k)) = [] ⇒ ∀n. n < k ⇒ FILTER Q (g n) = []
Proof
  simp[FILTER_FLAT, FLAT_EQ_NIL, EVERY_MAP, EVERY_GENLIST]
QED

(* MAIN: if the right side's transcript has no pair satisfying Q, then the
   pairs of both's transcript satisfying Q are exactly the left side's *)
Theorem trans_both_filter_left:
  FILTER Q (trans m2 (right_view m1 m2 h)) = [] ⇒
  FILTER Q (trans (both m1 m2) h) = FILTER Q (trans m1 (left_view m1 m2 h))
Proof
  simp[trans_def] >> strip_tac
  >> drule FILTER_FLAT_GENLIST_NIL >> strip_tac
  >> ‘GENLIST (round_trans (both m1 m2) h) (SUC (LENGTH h)) =
      GENLIST (λn. round_trans m1 (left_view m1 m2 h) n ++
                   round_trans m2 (right_view m1 m2 h) n) (SUC (LENGTH h))’
       by simp[GENLIST_FUN_EQ, round_trans_both]
  >> simp[] >> irule FILTER_FLAT_GENLIST_APPEND >> simp[]
QED

(* MAIN: the same, with the sides swapped *)
Theorem trans_both_filter_right:
  FILTER Q (trans m1 (left_view m1 m2 h)) = [] ⇒
  FILTER Q (trans (both m1 m2) h) = FILTER Q (trans m2 (right_view m1 m2 h))
Proof
  simp[trans_def] >> strip_tac
  >> drule FILTER_FLAT_GENLIST_NIL >> strip_tac
  >> ‘GENLIST (round_trans (both m1 m2) h) (SUC (LENGTH h)) =
      GENLIST (λn. round_trans m1 (left_view m1 m2 h) n ++
                   round_trans m2 (right_view m1 m2 h) n) (SUC (LENGTH h))’
       by simp[GENLIST_FUN_EQ, round_trans_both]
  >> simp[] >> irule FILTER_FLAT_GENLIST_APPEND' >> simp[]
QED
