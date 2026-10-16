(*
  A blocking select for the socket model (socketWorld).

  sock_select fds s: block until one of fds is ready, i.e. let rounds of
  the schedule pass (tick) until, after some round, one of fds is ready;
  return the ready ones among fds and the world after that round.  If no
  fd of fds ever becomes ready, select blocks forever (NONE): as an FFI
  call that is FFIdiverge.

  The main facts:
  - select is exactly polling with the empty polls skipped
    (sock_select_polls): the rounds select lets pass are the rounds in
    which a poll of fds would have returned nothing -- the rounds a
    blocking scheduler may skip (asyncSched2's `blocked`);
  - under the schedule assumption sched_wf, select returns as soon as an
    arrival for one of fds is scheduled (sock_select_live).
*)
Theory socketSelect
Ancestors
  llist socketWorld socketFair
Libs
  preamble

(* Some fd of fds is ready in s *)
Definition any_ready_def:
  any_ready fds s ⇔ EXISTS (is_ready s) fds
End

Definition sock_select_def:
  sock_select fds s =
    if ∃n. any_ready fds (ticks (SUC n) s) then
      let n = LEAST n. any_ready fds (ticks (SUC n) s);
          s' = ticks (SUC n) s
      in SOME (FILTER (is_ready s') fds, s')
    else NONE
End

(* MAIN: select is polling with the empty polls skipped.  If select
   returns after n+1 rounds, then polling fds in each of the first n rounds
   would have returned nothing, and the poll of round n+1 returns what
   select returns, in the same world. *)
Theorem sock_select_polls:
  sock_select fds s = SOME (r, s') ⇒
  ∃n. (∀m. m < n ⇒ FST (sock_poll fds (ticks m s)) = []) ∧
      sock_poll fds (ticks n s) = (r, s') ∧ r ≠ []
Proof
  rw[sock_select_def] >>
  qabbrev_tac ‘P = λn. any_ready fds (ticks (SUC n) s)’ >>
  ‘P (LEAST n. P n) ∧ ∀m. m < (LEAST n. P n) ⇒ ¬P m’
    by (conj_tac >- (numLib.LEAST_ELIM_TAC >> simp[Abbr ‘P’] >> metis_tac[]) >>
        rpt strip_tac >> drule_at Any WhileTheory.LESS_LEAST >> simp[]) >>
  qexists_tac ‘LEAST n. P n’ >>
  gvs[Abbr ‘P’, sock_poll_def, GSYM ticks_SUC, any_ready_def] >>
  rw[] >> gvs[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

(* select returns nothing new: what it reports ready is ready *)
Theorem sock_select_ready:
  sock_select fds s = SOME (r, s') ⇒ EVERY (is_ready s') r ∧ r ≠ []
Proof
  strip_tac >> drule sock_select_polls >> rw[sock_poll_def] >>
  simp[EVERY_FILTER]
QED

(* MAIN (liveness): under sched_wf, if an arrival for one of fds is
   scheduled for round k, select returns (within k+1 rounds). *)
Theorem sock_select_live:
  sched_wf s ∧ MEM a (next_step (ticks k s)) ∧ arrival_nonempty a ∧
  MEM (arrival_fd a) fds ⇒
  ∃r s'. sock_select fds s = SOME (r, s')
Proof
  strip_tac >> simp[sock_select_def] >>
  ‘any_ready fds (ticks (SUC k) s)’
    by (simp[any_ready_def, EXISTS_MEM] >> qexists_tac ‘arrival_fd a’ >>
        simp[] >> mp_tac (Q.SPECL [‘k’, ‘s’, ‘a’] ticks_ready) >>
        simp[] >> disch_then (qspec_then ‘SUC k’ mp_tac) >> simp[]) >>
  rw[] >> metis_tac[]
QED
