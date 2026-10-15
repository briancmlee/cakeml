(*
  The idle-deadline loop at Level 2: a loop that carries its pending read
  across timeouts, and is quiet, so a scheduler may block until the fd is
  readable or the deadline's timer event is reported.

  Ingredients, all at Level 2:
   - choose2 is well-formed (wf_choose_with) and its losers are well-formed
     and quiet (choose2_results, wf2_suspended2);
   - the split recursion rule (guarded2_bind2_split), as at Level 1.

  At Level 2 the deadline waits for the world to report a `Timer t` event
  (deadline2), rather than comparing the snapshot's time, so the loop erases
  to a Level 1 loop of the same shape with that timer.
*)
Theory asyncIdle2
Ancestors
  pair list rich_list arithmetic option pred_set string sum
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncEcho
  asyncLevel2 asyncLoop2
Libs
  BasicProvers

Theorem IS_PREFIX_APPEND_APPEND[local]:
  l ≼ l ++ a ++ b
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]
QED

Theorem FRONT_SNOC'[local]:
  FRONT (p ++ [s]) = p
Proof
  simp[FRONT_APPEND]
QED

(* ------------------------------------------------------------------------
   choose2 is well-formed, and so are its losers
   ------------------------------------------------------------------------ *)

(* choose with any packaging of the loser is well-formed (as wf_choose) *)
Theorem wf_choose_with:
  wf (choose_with k1 k2 m1 m2)
Proof
  simp[wf_def] >> rpt gen_tac
  >> Cases_on ‘first_prefix (either_done m1 m2) h’
  >- (simp[choose_with_def]
      >> Cases_on ‘first_prefix (either_done m1 m2) (h ++ [s])’
      >- simp[par_log_SNOC, IS_PREFIX_APPEND_APPEND]
      >> rename1 ‘_ = SOME n’
      >> ‘n = LENGTH h + 1’ by gvs[first_prefix_SNOC, AllCaseEqs()]
      >> simp[TAKE_LENGTH_TOO_LONG]
      >> every_case_tac
      >> rw[log_before_def, FRONT_SNOC', par_log_SNOC, IS_PREFIX_APPEND_APPEND])
  >> rename1 ‘_ = SOME n’
  >> ‘first_prefix (either_done m1 m2) (h ++ [s]) = SOME n’
       by simp[first_prefix_APPEND]
  >> ‘n ≤ LENGTH h’ by fs[first_prefix_SOME]
  >> simp[choose_with_def, TAKE_APPEND1]
  >> rpt (CASE_TAC >> simp[])
  >> ‘n + 1 ≤ LENGTH h’ by simp[]
  >> simp[TAKE_APPEND1]
QED

Theorem quiet_suspended2:
  wf c.run ∧ quiet c ⇒ quiet (suspended2 c v)
Proof
  rw[quiet_def, suspended2_def]
  >> gvs[new_actions_suspended]
  >> first_x_assum (qspecl_then [‘v ++ h’, ‘s’, ‘h'’] mp_tac) >> simp[]
  >> strip_tac
  >> simp[outcome_component_equality, suspended_actions]
QED

(* MAIN: the rest of a Level 2 computation is Level 2 well-formed (and so
   quiet) *)
Theorem wf2_suspended2:
  wf2 c ⇒ wf2 (suspended2 c v)
Proof
  rw[wf2_def] >- simp[suspended2_def, wf_suspended]
  >> irule quiet_suspended2 >> simp[]
QED

(* MAIN: choose2 is Level 2 well-formed if its sides are *)
Theorem wf2_choose2:
  wf2 c1 ∧ wf2 c2 ⇒ wf2 (choose2 c1 c2)
Proof
  rw[wf2_def]
  >- simp[choose2_def, wf_choose_with]
  >> irule quiet_choose2 >> simp[]
QED

(* MAIN: what choose2 can return: the winner's result and the other side,
   suspended *)
Theorem choose2_results:
  ((choose2 c1 c2).run h).result = SOME z ⇒
  (∃x v. z = INL (x, suspended2 c2 v) ∧ can_return c1.run x) ∨
  (∃y v. z = INR (suspended2 c1 v, y) ∧ can_return c2.run y)
Proof
  strip_tac >> pop_assum mp_tac >> simp[choose2_def, choose_with_def]
  >> Cases_on ‘first_prefix (either_done c1.run c2.run) h’ >> simp[]
  >> rename1 ‘_ = SOME n’
  >> ‘either_done c1.run c2.run (TAKE n h)’ by fs[first_prefix_SOME]
  >> Cases_on ‘(c1.run (left_view c1.run c2.run (TAKE n h))).result’ >> simp[]
  >- (‘∃y. (c2.run (right_view c1.run c2.run (TAKE n h))).result = SOME y’
        by (gvs[either_done_def]
            >> Cases_on ‘(c2.run (right_view c1.run c2.run (TAKE n h))).result’
            >> gvs[])
      >> rw[can_return_def] >> metis_tac[])
  >> rw[can_return_def] >> metis_tac[]
QED

(* If the right side needs a snapshot, choose2's results before any
   snapshot are the left side's *)
Theorem choose2_at_start:
  (c2.run []).result = NONE ∧ ((choose2 c1 c2).run []).result = SOME z ⇒
  ∃x l. z = INL (x, l)
Proof
  rw[choose2_def, choose_with_def, Once first_prefix_def, either_done_def,
     AllCaseEqs()] >> gvs[]
  >> Cases_on ‘(c1.run []).result’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   The split recursion rule at Level 2
   ------------------------------------------------------------------------ *)

(* MAIN: the split recursion rule at Level 2 (as guarded_bind_split) *)
Theorem guarded2_bind2_split:
  (∀x. nonexpansive2 (λR. G x R)) ∧
  (∀x. (c.run []).result = SOME x ⇒ guarded2 (λR. G x R)) ⇒
  guarded2 (λR. bind2 c (λx. G x R))
Proof
  rw[guarded2_def, nonexpansive2_def, guarded_def, nonexpansive_def]
  >> rename1 ‘∀p. agree_below n (R1 p) (R2 p)’
  >> simp[agree_below_pack] >> qx_gen_tac ‘h’ >> strip_tac
  >> simp[bind2_def, bind_def, bind_interest_def]
  >> CASE_TAC >> simp[]
  >> rename1 ‘TAKE j h’
  >> qabbrev_tac ‘x = THE (c.run (TAKE j h)).result’
  >> qabbrev_tac
       ‘v = skip_results (LENGTH (new_actions (log_of c.run) (TAKE j h))) (DROP j h)’
  >> ‘j ≤ LENGTH h ∧ (c.run (TAKE j h)).result ≠ NONE’ by fs[first_prefix_SOME]
  >> ‘LENGTH v = LENGTH h - j’ by simp[Abbr ‘v’]
  >> ‘(G x (λq. unpack (R1 q))).run v = (G x (λq. unpack (R2 q))).run v ∧
      (G x (λq. unpack (R1 q))).interest v = (G x (λq. unpack (R2 q))).interest v’
       suffices_by simp[]
  >> Cases_on ‘j = 0’
  >- (‘(c.run []).result = SOME x’
        by (gvs[Abbr ‘x’] >> Cases_on ‘(c.run []).result’ >> gvs[])
      >> first_x_assum drule >> disch_then (qspecl_then [‘n’, ‘R1’, ‘R2’] mp_tac)
      >> simp[agree_below_pack] >> disch_then (qspec_then ‘v’ mp_tac) >> simp[])
  >> first_x_assum (qspecl_then [‘x’, ‘n’, ‘R1’, ‘R2’] mp_tac)
  >> simp[agree_below_pack] >> disch_then (qspec_then ‘v’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The loop
   ------------------------------------------------------------------------ *)

(* Finishes when the world reports the timer event for time t *)
Definition deadline2_def:
  deadline2 t = wait_on (Timer t) (λs. SOME ())
End

(* Wait until fd is readable, then read it *)
Definition reader2_def:
  reader2 fd = bind2 (wait_on (Readable fd) (λs. SOME ())) (λu. emit2 (Read fd))
End

Definition idle_body2_def:
  idle_body2 d fd R (pend, t) =
    bind2 (choose2 pend (deadline2 t)) (λres.
      case res of
        INL (resp, timer) =>
          (case resp of
             Data s => bind2 (emit2 (Write fd s)) (λw. R (reader2 fd, t))
           | WouldBlock =>
               bind2 (wait_on (Readable fd) (λs. SOME ())) (λu. R (reader2 fd, t))
           | Eof => return2 ()
           | Written => return2 ())
      | INR (pend', u) => R (pend', t + d))
End

(* MAIN: the Level 2 idle loop is a well-defined recursive definition *)
Theorem idle_body2_contractive:
  contractive2 (idle_body2 d fd)
Proof
  rw[contractive2_def] >> PairCases_on ‘p’ >> simp[idle_body2_def]
  >> ho_match_mp_tac guarded2_bind2_split >> conj_tac
  >- (Cases >> simp[]
      >- (PairCases_on ‘x’ >> Cases_on ‘x0’ >> simp[nonexpansive2_const]
          >> ho_match_mp_tac nonexpansive2_bind2
          >> simp[nonexpansive2_const, nonexpansive2_call])
      >> PairCases_on ‘y’ >> simp[nonexpansive2_call])
  >> rpt strip_tac
  >> drule_at (Pos last) choose2_at_start
  >> simp[deadline2_def, wait_on_def, wait_needs_snapshot]
  >> strip_tac >> gvs[]
  >> Cases_on ‘x’ >> simp[]
  >> TRY (simp[guarded2_def, guarded_const] >> NO_TAC)
  >> ho_match_mp_tac guarded2_bind2
  >> simp[emit2_def, emit_needs_snapshot, wait_on_def, wait_needs_snapshot,
          nonexpansive2_call]
QED

Definition idle2_def:
  idle2 d fd = fix2 (idle_body2 d fd)
End

(* MAIN: the Level 2 idle loop satisfies its recursive equation *)
Theorem idle2_unfold:
  idle2 d fd (pend, t) = idle_body2 d fd (idle2 d fd) (pend, t)
Proof
  simp[idle2_def]
  >> simp[Once (MATCH_MP fix2_unfold idle_body2_contractive)]
QED

Theorem wf2_reader2:
  wf2 (reader2 fd)
Proof
  simp[reader2_def] >> irule wf2_bind2 >> simp[wf2_wait_on, wf2_emit2]
QED

(* MAIN: the Level 2 idle loop is well-formed and quiet whenever the pending
   read is: a scheduler may block until fd is readable or the timer event is
   reported *)
Theorem wf2_idle2:
  wf2 pend ⇒ wf2 (idle2 d fd (pend, t))
Proof
  strip_tac >> simp[idle2_def]
  >> qspecl_then [‘idle_body2 d fd’, ‘λ(pend, t). wf2 pend’] mp_tac
       (Q.GENL [‘body2’, ‘ok’] wf2_fix2_on)
  >> impl_tac
  >- (simp[idle_body2_contractive] >> rpt strip_tac
      >> PairCases_on ‘p’ >> gvs[idle_body2_def]
      >> fs[FORALL_PROD]
      >> irule wf2_bind2_on
      >> simp[wf2_choose2, deadline2_def, wf2_wait_on] >> rpt strip_tac
      >> fs[can_return_def] >> drule choose2_results >> strip_tac >> gvs[]
      (* the read won *)
      >- (Cases_on ‘x'’ >> simp[wf2_return2]
          >> irule wf2_bind2 >> simp[wf2_emit2, wf2_wait_on, wf2_reader2])
      (* the deadline passed: the pending read, suspended, is still wf2 *)
      >> first_x_assum irule >> simp[wf2_suspended2])
  >> simp[FORALL_PROD]
QED

(* MAIN: in particular, the Level 2 idle loop is quiet *)
Theorem quiet_idle2:
  wf2 pend ⇒ quiet (idle2 d fd (pend, t))
Proof
  strip_tac >> drule wf2_idle2 >> simp[wf2_def]
QED

(* Sanity checks: at first the loop waits for the fd to become readable or
   the deadline's timer; after the timer fires it still waits for the same
   read, and for the next deadline *)
Theorem example_idle2_waits:
  status (idle2 5 0 (reader2 0, 5)) [] = Waiting {Readable 0; Timer 5}
Proof
  EVAL_TAC >> simp[EXTENSION] >> metis_tac[]
QED

Theorem example_idle2_after_timeout:
  status (idle2 5 0 (reader2 0, 5)) [snap {Timer 5} []] =
    Waiting {Readable 0; Timer 10}
Proof
  EVAL_TAC >> simp[EXTENSION] >> metis_tac[]
QED
