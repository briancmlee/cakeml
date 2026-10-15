(*
  The echo loop at Level 2: it declares which event it waits for, erases to
  the Level 1 echo loop, and is quiet, so a scheduler may block until fd is
  readable instead of polling it.
*)
Theory asyncEcho2
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncEcho asyncLevel2 asyncLoop2
Libs
  BasicProvers

Definition echo_body2_def:
  echo_body2 R fd =
    bind2 (wait_on (Readable fd) (λs. SOME ())) (λu.
    bind2 (emit2 (Read fd)) (λres.
      case res of
        Data d => bind2 (emit2 (Write fd d)) (λw. R fd)
      | Eof => return2 ()
      | _ => R fd))
End

Theorem echo_body2_contractive:
  contractive2 echo_body2
Proof
  rw[contractive2_def, echo_body2_def]
  >> ho_match_mp_tac guarded2_bind2
  >> simp[wait_on_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
  >> Cases >> simp[nonexpansive2_call, nonexpansive2_const]
  >> ho_match_mp_tac nonexpansive2_bind2
  >> simp[nonexpansive2_const, nonexpansive2_call]
QED

(* The Level 2 body erases to the Level 1 body *)
Theorem erase_echo_body2:
  erase (echo_body2 R fd) = echo_body (λq. erase (R q)) fd
Proof
  simp[echo_body2_def, echo_body_def, erase_bind2, erase_wait_on, erase_emit2,
       readable_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> Cases_on ‘res’ >> simp[erase_bind2, erase_emit2, erase_return2]
QED

Definition echo2_def:
  echo2 = fix2 echo_body2
End

(* MAIN: the Level 2 echo loop satisfies its recursive equation *)
Theorem echo2_unfold:
  echo2 fd =
    bind2 (wait_on (Readable fd) (λs. SOME ())) (λu.
    bind2 (emit2 (Read fd)) (λres.
      case res of
        Data d => bind2 (emit2 (Write fd d)) (λw. echo2 fd)
      | Eof => return2 ()
      | _ => echo2 fd))
Proof
  simp[echo2_def]
  >> simp[Once (MATCH_MP fix2_unfold echo_body2_contractive)]
  >> simp[echo_body2_def]
QED

(* MAIN: erasing the Level 2 echo loop gives the Level 1 echo loop *)
Theorem erase_echo2:
  erase (echo2 fd) = echo fd
Proof
  simp[echo2_def, echo_def]
  >> irule erase_fix2
  >> simp[echo_body_contractive, echo_body2_contractive, erase_echo_body2]
QED

(* MAIN: the Level 2 echo loop is well-formed and quiet: a scheduler may
   block until fd is readable *)
Theorem wf2_echo2:
  wf2 (echo2 fd)
Proof
  simp[echo2_def] >> irule wf2_fix2 >> simp[echo_body2_contractive]
  >> rw[echo_body2_def]
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> Cases
  >> simp[wf2_return2] >> irule wf2_bind2 >> simp[wf2_emit2]
QED

(* Sanity checks: what echo2 waits for *)
Theorem example_echo2_waits_readable:
  status (echo2 0) [] = Waiting {Readable 0}
Proof
  EVAL_TAC
QED

Theorem example_echo2_waits_response:
  status (echo2 0) [snap {Readable 0} []] = Waiting ∅
Proof
  EVAL_TAC
QED

Theorem example_echo2_waits_again:
  status (echo2 0) [snap {Readable 0} []; snap {} [Data "hi"]; snap {} [Written]] =
    Waiting {Readable 0}
Proof
  EVAL_TAC
QED

(* MAIN: the Level 2 echo loop is quiet: it makes no progress, now or later,
   on a snapshot in which fd is not readable (and no response is due), so a
   scheduler may block in select until fd becomes readable *)
Theorem quiet_echo2:
  quiet (echo2 fd)
Proof
  mp_tac wf2_echo2 >> simp[wf2_def]
QED
