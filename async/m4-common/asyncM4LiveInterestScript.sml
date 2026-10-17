(*
  D26: live interest lists.  The servers' loop drops a handle from its
  interest list in the round its Read returns end-of-file (Got (SOME [])),
  as well as adding the connections handed out (add_accepted).  Results
  are positional to the round's actions, so a round's update reads both.

    live_round fds acts rs   one round: the actions emitted, their results
    live fds0 acts h         after the snapshots h (acts = log_of m): round i's
                             actions are new_actions acts (TAKE i h), their
                             results (EL i h).results

  The shape is the translator's (recursion, plain patterns), for the
  CakeML loop (honest-l1-cf step_pf, honest-l1b-cf step_pfb).  Design:
  design/48-live-interest.md.

  MAIN: live_SNOC, MEM_live_round.
*)
Theory asyncM4LiveInterest
Ancestors
  list rich_list asyncCore asyncLevel1 asyncM3World asyncM4Loop
Libs
  preamble

(* The handles whose Read returned end-of-file, in a round *)
Definition eof_reads_def:
  eof_reads [] rs = [] ∧
  eof_reads (a :: acts) rs =
    case rs of
    | [] => []
    | r :: rs' =>
        case a of
        | Read h k =>
            (case r of
             | Got (SOME bs) => if bs = [] then h :: eof_reads acts rs' else eof_reads acts rs'
             | _ => eof_reads acts rs')
        | _ => eof_reads acts rs'
End

Definition live_round_def:
  live_round fds acts rs =
    FILTER (λh. ¬MEM h (eof_reads acts rs)) (add_accepted fds rs)
End

Definition live_def:
  live fds0 acts (h : (word64, sresp) snapshot list) =
    FOLDL (λfds i. live_round fds (new_actions acts (TAKE i h)) (EL i h).results)
          fds0 (COUNT_LIST (LENGTH h))
End

Theorem live_NIL[simp]:
  live fds0 acts [] = fds0
Proof
  simp[live_def, COUNT_LIST_def]
QED

Theorem COUNT_LIST_ADD1[local]:
  COUNT_LIST (n + 1) = COUNT_LIST n ++ [n]
Proof
  REWRITE_TAC [GSYM ADD1, COUNT_LIST_SNOC, SNOC_APPEND]
QED

(* MAIN: one more round *)
Theorem live_SNOC:
  live fds0 acts (h ++ [s]) = live_round (live fds0 acts h) (new_actions acts h) s.results
Proof
  simp[live_def, COUNT_LIST_ADD1, FOLDL_APPEND, EL_LENGTH_APPEND, TAKE_LENGTH_APPEND] >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  irule FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
  simp[EL_APPEND1, TAKE_APPEND1]
QED

Theorem MEM_eof_reads:
  ∀acts rs. LENGTH acts = LENGTH rs ⇒
            (MEM x (eof_reads acts rs) ⇔ ∃k. MEM (Read x k, Got (SOME [])) (ZIP (acts, rs)))
Proof
  Induct >> simp[eof_reads_def] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[] >>
  strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >> strip_tac >>
  Cases_on ‘h’ >> simp[] >> TRY (Cases_on ‘h'’) >> simp[] >>
  TRY (Cases_on ‘o'’ >> simp[] >> rw[]) >>
  metis_tac[]
QED

(* MAIN *)
Theorem MEM_live_round:
  LENGTH acts = LENGTH rs ⇒
  (MEM x (live_round fds acts rs) ⇔
     MEM x (add_accepted fds rs) ∧ ¬∃k. MEM (Read x k, Got (SOME [])) (ZIP (acts, rs)))
Proof
  strip_tac >> simp[live_round_def, MEM_FILTER, MEM_eof_reads] >> metis_tac[]
QED
