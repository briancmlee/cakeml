(*
  Completed transcripts, shared by the world-async experiments
  (design/12-world-as-async.md).

  trans m h (asyncTranscript) includes the last round, whose actions have no
  responses yet.  ctrans m h keeps only the rounds whose responses have
  arrived, so it grows by exactly one round per snapshot (ctrans_SNOC),
  which is what a round-by-round run of a closed system needs.
*)
Theory worldAsyncCtrans
Ancestors
  pair list rich_list arithmetic option
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Completed transcripts: only the rounds whose responses have arrived
   ------------------------------------------------------------------------ *)

Definition ctrans_def:
  ctrans m h = FLAT (GENLIST (round_trans m h) (LENGTH h))
End

Theorem ctrans_NIL[simp]:
  ctrans m [] = []
Proof
  simp[ctrans_def]
QED

Theorem ctrans_SNOC:
  ctrans m (h ++ [s]) = ctrans m h ++ zipr (new_actions (log_of m) h) s.results
Proof
  simp[ctrans_def] >> REWRITE_TAC[GSYM ADD1, GENLIST, SNOC_APPEND, FLAT_APPEND]
  >> simp[round_trans_def, responses_at_def, EL_APPEND2, TAKE_LENGTH_APPEND, zipr_def]
  >> AP_TERM_TAC >> simp[GENLIST_FUN_EQ, round_trans_def, TAKE_APPEND1,
                         responses_at_def, EL_APPEND1]
QED

Theorem trans_ctrans:
  trans m h = ctrans m h ++ zipr (new_actions (log_of m) h) []
Proof
  simp[trans_def, ctrans_def, GENLIST, SNOC_APPEND, round_trans_def,
       responses_at_def]
QED

Theorem zipr_NIL_read:
  ∀as. read fd (zipr as []) = []
Proof
  Induct >> simp[zipr_def]
  >> Cases >> simp[]
QED

Theorem zipr_NIL_accepted:
  ∀as. accepted (zipr as []) = []
Proof
  Induct >> simp[zipr_def]
  >> Cases >> simp[]
QED

Theorem LENGTH_zipr[simp]:
  ∀as rs. LENGTH (zipr as rs) = LENGTH as
Proof
  Induct >> simp[zipr_def]
QED

