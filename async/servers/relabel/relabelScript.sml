(*
  Relabelling a computation's vocabulary, in the model.

  The echo server speaks the model's vocabulary (echoServer: num fds,
  string data, events Readable fd).  M3's event loop (spike/m3-assembly)
  speaks the socket model's (sact/sresp: word64 fds, byte lists, a ready
  set of fds).  The bridge is a relabelling: translate each emitted action
  with fa, and each snapshot the world delivers with fs.

     relabel fa fs m h = m (MAP fs h), with its actions mapped by fa

  This theory proves that relabelling preserves well-formedness, and how
  transcripts correspond (trans_relabel): the relabelled computation's
  transcript is the original's, with actions mapped by fa and responses
  read back with fr.  So every property of the original transcript on the
  history MAP fs h (e.g. echo_server_safety) is a property of the
  relabelled computation's transcript on h.  This file does not depend on
  M3's definitions.
*)
Theory relabel
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncLevel2
  asyncTranscript
Libs
  BasicProvers

(* m, run in another vocabulary: snapshots are translated with fs before m
   sees them, and m's actions are translated with fa *)
Definition relabel_def:
  relabel fa fs m h =
    <| actions := MAP fa (m (MAP fs h)).actions;
       result := (m (MAP fs h)).result |>
End

(* MAIN: relabelling preserves well-formedness *)
Theorem wf_relabel:
  wf m ⇒ wf (relabel fa fs m)
Proof
  rw[wf_def, relabel_def] >>
  first_x_assum (qspecl_then [‘MAP fs h’, ‘fs s’] strip_assume_tac) >>
  gvs[isPREFIX_MAP]
QED

(* The actions of each round are the original's, translated *)
Theorem new_actions_relabel:
  new_actions (log_of (relabel fa fs m)) h =
  MAP fa (new_actions (log_of m) (MAP fs h))
Proof
  rw[new_actions_def, log_of_def, relabel_def, MAP_DROP, MAP_FRONT]
QED

Theorem responses_at_MAP:
  (∀s. (fs s).results = MAP fr s.results) ⇒
  responses_at (MAP fs h) n = MAP fr (responses_at h n)
Proof
  rw[responses_at_def, EL_MAP]
QED

Theorem zipr_MAP:
  ∀as rs.
    MAP (λ(a, r). (fa a, r)) (zipr as (MAP fr rs)) =
    MAP (λ(a, r). (a, OPTION_MAP fr r)) (zipr (MAP fa as) rs)
Proof
  Induct >> simp[zipr_def] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[zipr_def]
  >- (first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[])
  >> gs[]
QED

(* MAIN: transcripts of a relabelled computation.  If fs translates the
   responses of a snapshot with fr, then the transcript of m on the
   translated history, with its actions translated by fa, is the
   transcript of relabel fa fs m on the original history, with its
   responses translated by fr. *)
Theorem trans_relabel:
  (∀s. (fs s).results = MAP fr s.results) ⇒
  MAP (λ(a, r). (fa a, r)) (trans m (MAP fs h)) =
  MAP (λ(a, r). (a, OPTION_MAP fr r)) (trans (relabel fa fs m) h)
Proof
  rw[trans_def, MAP_FLAT, MAP_GENLIST, combinTheory.o_DEF] >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ] >> rpt strip_tac >>
  simp[round_trans_def, new_actions_relabel, GSYM MAP_TAKE] >>
  drule responses_at_MAP >> simp[zipr_MAP]
QED
