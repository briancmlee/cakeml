(*
  The schedule, round by round (EchoSpec's world vs the event loop's).

  EchoSpec states liveness against the schedule of the initial world:
  sent_upto c n sk is the data the client of c sends in the first n steps
  of the schedule.  The event loop (loopPollDyn, grounds) lets exactly one
  step of the schedule arrive per round, in its poll; the socket operations
  in between never touch the schedule.  So:

   - grounds_arrivals: after n rounds the world has consumed exactly the
     first n steps: arrivals_upto (n + k) of the initial schedule is
     arrivals_upto n of it followed by arrivals_upto k of the world's
     remaining schedule;
   - grounds_sched_wf: the fairness assumption sched_wf holds of the world
     throughout the run (by the socket worker's sched_wf_preserved), so
     every arrival delivered in the run is effective (arrival_ok).
*)
Theory echoLiveSched
Ancestors
  pair list rich_list arithmetic option llist alist
  socketWorld socketFair EchoSpec loopPollWorld loopRounds
Libs
  preamble

(* ------------------------------------------------------------------------
   Arrivals, step by step
   ------------------------------------------------------------------------ *)

Theorem arrivals_upto_LHD_NONE:
  ∀k l. LHD l = NONE ⇒ arrivals_upto k l = []
Proof
  Cases >> simp[arrivals_upto_def]
QED

Theorem tick_sched:
  (tick s).sched = case LHD s.sched of NONE => s.sched | SOME _ => THE (LTL s.sched)
Proof
  rw[tick_def] >> CASE_TAC >> simp[]
QED

(* One tick delivers the next step of the schedule *)
Theorem arrivals_upto_tick:
  arrivals_upto (SUC k) s.sched = next_step s ++ arrivals_upto k (tick s).sched
Proof
  simp[arrivals_upto_def, next_step_def, tick_sched] >> CASE_TAC >> simp[]
  >> Cases_on ‘k’ >> gvs[arrivals_upto_def]
QED

(* The socket operations leave the schedule alone *)
Theorem sock_do_sched:
  sock_do s a = SOME (r, s') ⇒ s'.sched = s.sched
Proof
  Cases_on ‘a’ >> rw[sock_do_def, sock_accept_def, sock_read_def, sock_write_def]
  >> gvs[AllCaseEqs()]
QED

Theorem sock_acts_sched:
  ∀acts s rs evs s'. sock_acts s acts = SOME (rs, evs, s') ⇒ s'.sched = s.sched
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()]
  >> first_x_assum drule >> drule sock_do_sched >> simp[]
QED

Theorem sock_acts_tot_sched:
  (SND (SND (sock_acts_tot s acts))).sched = s.sched
Proof
  rw[sock_acts_tot_def] >> CASE_TAC >> simp[] >> PairCases_on ‘x’
  >> drule sock_acts_sched >> simp[]
QED

(* The world in round n, after the round's actions and before the poll *)
Definition gmid_def:
  gmid ifds m s0 n = SND (SND (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n)))
End

Theorem gstate_SUC:
  gstate ifds m s0 (SUC n) = tick (gmid ifds m s0 n)
Proof
  simp[Once gstate_def, grounds_SUC, gmid_def, sock_poll_def]
QED

Theorem gmid_sched:
  (gmid ifds m s0 n).sched = (gstate ifds m s0 n).sched
Proof
  simp[gmid_def, sock_acts_tot_sched]
QED

(* MAIN: after n rounds the world has consumed exactly the first n steps of
   its initial schedule *)
Theorem grounds_arrivals:
  ∀n k. arrivals_upto (n + k) s0.sched =
        arrivals_upto n s0.sched ++ arrivals_upto k (gstate ifds m s0 n).sched
Proof
  Induct >- simp[gstate_def, grounds_def, arrivals_upto_def]
  >> rpt gen_tac
  >> ‘∀k. arrivals_upto (SUC k) (gstate ifds m s0 n).sched =
          next_step (gmid ifds m s0 n) ++ arrivals_upto k (gstate ifds m s0 (SUC n)).sched’
       by (gen_tac >> simp[gstate_SUC, GSYM arrivals_upto_tick, gmid_sched])
  >> ‘arrivals_upto (n + SUC k) s0.sched =
        arrivals_upto n s0.sched ++ arrivals_upto (SUC k) (gstate ifds m s0 n).sched ∧
      arrivals_upto (n + SUC 0) s0.sched =
        arrivals_upto n s0.sched ++ arrivals_upto (SUC 0) (gstate ifds m s0 n).sched’
       by metis_tac[]
  >> ‘SUC n + k = n + SUC k ∧ SUC n = n + SUC 0’ by simp[] >> ASM_REWRITE_TAC[]
  >> qpat_x_assum ‘∀k. arrivals_upto (SUC k) _ = _’ (fn th => REWRITE_TAC[th])
  >> simp[arrivals_upto_def]
QED

(* The data client c sends in a list of arrivals *)
Definition sent_of_def:
  sent_of c as =
    FLAT (MAP (λa. case a of Data c' bs => if c' = c then bs else [] | _ => []) as)
End

Theorem sent_upto_sent_of:
  sent_upto c n sk = sent_of c (arrivals_upto n sk.sched)
Proof
  simp[sent_upto_def, sent_of_def]
QED

(* MAIN: in round n the clients' data that arrives is that of step n of the
   initial schedule *)
Theorem sent_upto_SUC:
  sent_upto c (SUC n) s0 =
  sent_upto c n s0 ++ sent_of c (next_step (gmid ifds m s0 n))
Proof
  qspecl_then [‘n’, ‘1’] mp_tac grounds_arrivals
  >> ‘arrivals_upto 1 (gstate ifds m s0 n).sched = next_step (gmid ifds m s0 n)’
       by (simp[next_step_def, gmid_sched] >> REWRITE_TAC[ONE, arrivals_upto_def]
           >> CASE_TAC >> simp[arrivals_upto_def])
  >> simp[sent_upto_sent_of, GSYM ADD1, sent_of_def, FLAT_APPEND]
QED

(* ------------------------------------------------------------------------
   Fairness, throughout the run
   ------------------------------------------------------------------------ *)

Theorem sock_do_sched_wf:
  sched_wf s ∧ sock_do s a = SOME (r, s') ⇒ sched_wf s'
Proof
  Cases_on ‘a’ >> rw[sock_do_def] >> TRY (PairCases_on ‘z’) >> gvs[]
  >> drule sched_wf_preserved >> rw[] >> res_tac
QED

Theorem sock_acts_sched_wf:
  ∀acts s rs evs s'.
    sched_wf s ∧ sock_acts s acts = SOME (rs, evs, s') ⇒ sched_wf s'
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()]
  >> metis_tac[sock_do_sched_wf]
QED

(* MAIN: the fairness assumption holds of the world throughout the run *)
Theorem grounds_sched_wf:
  sched_wf s0 ∧ grun_ok ifds m s0 ⇒
  ∀n. sched_wf (gstate ifds m s0 n) ∧ sched_wf (gmid ifds m s0 n)
Proof
  strip_tac
  >> ‘∀n. sched_wf (gstate ifds m s0 n) ⇒ sched_wf (gmid ifds m s0 n)’
       by (rw[gmid_def, sock_acts_tot_def] >> gvs[grun_ok_def]
           >> first_x_assum (qspec_then ‘n’ mp_tac)
           >> CASE_TAC >> simp[] >> PairCases_on ‘x’ >> simp[]
           >> drule_all sock_acts_sched_wf >> simp[])
  >> ‘∀n. sched_wf (gstate ifds m s0 n)’ suffices_by simp[]
  >> Induct >- simp[gstate_def, grounds_def]
  >> simp[gstate_SUC] >> irule sched_wf_tick >> simp[]
QED

(* MAIN: so every arrival delivered in the run is effective (the world
   never drops one): the arrivals of each step are effective in turn *)
Theorem grounds_step_ok:
  sched_wf s0 ∧ grun_ok ifds m s0 ⇒
  ∀n. step_ok (gmid ifds m s0 n) (next_step (gmid ifds m s0 n))
Proof
  rpt strip_tac >> drule_all grounds_sched_wf
  >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> gvs[sched_wf_def] >> first_x_assum (qspec_then ‘0’ mp_tac)
  >> simp[ticks_def]
QED
