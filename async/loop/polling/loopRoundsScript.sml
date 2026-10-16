(*
  The history the socket world generates, with an interest list that may
  depend on the history (shared by M4's echo_safe and echo_live).

  M3's srounds (loopPollWorld) polls a fixed list of fds every round.  An
  echo server must also poll the connections it has accepted, so the
  interest list of round n is a function ifds of the history so far:

     grounds ifds m s0 0       = ([], s0)
     grounds ifds m s0 (SUC n) = let (h, s) = grounds ifds m s0 n;
                                  (rs, evs, s1) = sock_acts_tot s (new_actions (log_of m) h);
                                  (rdy, s2) = sock_poll (ifds h) s1
                              in (h ++ [ssnap rdy rs], s2)

  M3's definitions are the special case ifds = K fds (srounds_grounds,
  sround_events_grounds, srun_ok_grun_ok).  The trace lemma carries over
  unchanged (gstrace_actions_rounds).  Depends on loopPollWorld only.
*)
Theory loopRounds
Ancestors
  asyncCore asyncLevel1 asyncChoose libModel socketWorld ffi
  loopPollWorld
Libs
  preamble

(* grounds ifds m s0 n = (h, s): after n rounds of a loop running m, whose
   round polls the fds ifds h (h: the history so far), in the socket world
   started in s0: the history m has been polled with, and the world. *)
Definition grounds_def:
  grounds ifds m s0 0 = ([], s0) ∧
  grounds ifds m s0 (SUC n) =
    let (h, s) = grounds ifds m s0 n;
        (rs, evs, s1) = sock_acts_tot s (new_actions (log_of m) h);
        (rdy, s2) = sock_poll (ifds h) s1
    in (h ++ [ssnap rdy rs], s2)
End

Definition ghist_def:
  ghist ifds m s0 n = FST (grounds ifds m s0 n)
End

(* The world's state at the start of round n *)
Definition gstate_def:
  gstate ifds m s0 n = SND (grounds ifds m s0 n)
End

(* The actions of round n: m's new actions on the history so far *)
Definition gacts_def:
  gacts ifds m s0 n = new_actions (log_of m) (ghist ifds m s0 n)
End

(* The ifds/O events of round n: the socket calls of m's new actions, then
   the poll of ifds h *)
Definition grounds_events_def:
  grounds_events ifds m s0 n =
    let (h, s) = grounds ifds m s0 n;
        (rs, evs, s1) = sock_acts_tot s (new_actions (log_of m) h)
    in evs ++ [spoll_event (ifds h) s1]
End

(* No action of the run is a misuse *)
Definition grun_ok_def:
  grun_ok ifds m s0 ⇔
    ∀n. sock_acts (gstate ifds m s0 n) (gacts ifds m s0 n) ≠ NONE
End

Theorem grounds_SUC:
  grounds ifds m s0 (SUC n) =
    (ghist ifds m s0 n ++
       [ssnap (FST (sock_poll (ifds (ghist ifds m s0 n))
                 (SND (SND (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n))))))
              (FST (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n)))],
     SND (sock_poll (ifds (ghist ifds m s0 n))
            (SND (SND (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n))))))
Proof
  simp[grounds_def, ghist_def, gstate_def, gacts_def] >>
  Cases_on ‘grounds ifds m s0 n’ >> simp[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem grounds_events_alt:
  grounds_events ifds m s0 n =
    FST (SND (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n))) ++
    [spoll_event (ifds (ghist ifds m s0 n))
       (SND (SND (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n))))]
Proof
  simp[grounds_events_def, ghist_def, gstate_def, gacts_def] >>
  Cases_on ‘grounds ifds m s0 n’ >> simp[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem LENGTH_ghist[simp]:
  ∀n. LENGTH (ghist ifds m s0 n) = n
Proof
  Induct >- simp[ghist_def, grounds_def] >>
  simp[Once ghist_def, grounds_SUC]
QED

Theorem ghist_SUC:
  ∀ifds m s0 n. ∃sn. ghist ifds m s0 (SUC n) = ghist ifds m s0 n ++ [sn]
Proof
  simp[Once ghist_def, grounds_SUC]
QED

(* The history of a later round extends that of an earlier one *)
Theorem ghist_TAKE:
  ∀n k. k ≤ n ⇒ TAKE k (ghist ifds m s0 n) = ghist ifds m s0 k
Proof
  Induct >- simp[ghist_def, grounds_def] >> rpt strip_tac >>
  Cases_on ‘k = SUC n’
  >- (gvs[] >> irule TAKE_LENGTH_ID_rwt >> simp[]) >>
  ‘k ≤ n’ by simp[] >>
  simp[Once ghist_def, grounds_SUC, TAKE_APPEND1]
QED

(* ------------------------------------------------------------------------
   M3's definitions are the case of a fixed interest list
   ------------------------------------------------------------------------ *)

Theorem srounds_grounds:
  ∀n. srounds fds m s0 n = grounds (K fds) m s0 n
Proof
  Induct >> simp[srounds_def, grounds_def]
QED

Theorem sround_events_grounds:
  sround_events fds m s0 n = grounds_events (K fds) m s0 n
Proof
  simp[sround_events_def, grounds_events_def, srounds_grounds]
QED

Theorem srun_ok_grun_ok:
  srun_ok fds m s0 ⇔ grun_ok (K fds) m s0
Proof
  simp[srun_ok_def, grun_ok_def, srounds_grounds, gstate_def, gacts_def,
       ghist_def]
QED

(* ------------------------------------------------------------------------
   The trace lemma, for any interest function
   ------------------------------------------------------------------------ *)

Theorem gstrace_actions_round:
  grun_ok ifds m s0 ⇒
  strace_actions (grounds_events ifds m s0 n) = gacts ifds m s0 n
Proof
  rw[grun_ok_def, grounds_events_alt, strace_actions_APPEND] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘sock_acts s acts’ >>
  Cases_on ‘sock_acts s acts’ >> simp[] >> PairCases_on ‘x’ >>
  simp[sock_acts_tot_def] >> metis_tac[strace_actions_sock_acts]
QED

(* MAIN: the socket trace and the model agree, for any interest function ifds:
   if no action of the run is a misuse, the actions performed by the socket
   calls in the first n+1 rounds are exactly m's action log on the history
   the socket world generates. *)
Theorem gstrace_actions_rounds:
  grun_ok ifds m s0 ∧ wf m ⇒
  strace_actions (FLAT (GENLIST (grounds_events ifds m s0) (SUC n))) =
  (m (ghist ifds m s0 n)).actions
Proof
  strip_tac >> Induct_on ‘n’
  >- (simp[gstrace_actions_round, gacts_def] >>
      simp[ghist_def, grounds_def, new_actions_NIL, log_of_def]) >>
  ONCE_REWRITE_TAC[GENLIST] >>
  simp[SNOC_APPEND, FLAT_APPEND, strace_actions_APPEND, gstrace_actions_round] >>
  simp[gacts_def, GSYM ghist_def] >>
  qspecl_then [‘ifds’, ‘m’, ‘s0’, ‘n’] strip_assume_tac
    ghist_SUC >> simp[] >>
  ‘log_of m (ghist ifds m s0 n) ≼ log_of m (ghist ifds m s0 n ++ [sn])’
    by simp[log_of_def, wf_SNOC_actions] >>
  drule new_actions_prefix >> simp[log_of_def]
QED
