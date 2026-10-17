(*
  Step 17 (design/45 §4.2): fairness of the multi-process L0 system, DRAFT
  statements for review (trusted, liveness only).  Nothing here is proved.

  [F0] sched_fair (approved), [F4] (approved), infinite runs l0sys_irun
  (approved), and kernel fairness in the OBSERVED form (user ruling):
  kernel_fair_obs states what processes SEE (call results), owed to a
  process that keeps asking.  The internal form kernel_fair (weak fairness
  of the kernel's Move / Ack / Fin / settle steps) is kept as the source of
  the sanity lemma kernel_fair_obs_of_internal: under sched_fair, [F1] and
  [F2], the internal form implies the observed one (so the observed form is
  satisfiable), and corollaries in internal form.

  Fix in can_step (moonshot-live's note): "finished" is a normal end of the
  program (Terminate Success), not prog_makes of the prefix, which holds at
  every prefix through the replay oracle's FFI_failed.
*)
Theory l0sysFair
Ancestors
  l0sys honestL0World honestL1Model
Libs
  preamble

(* ------------------------------------------------------------------------
   Runs and the scheduler (approved; can_step's "finished" fixed)
   ------------------------------------------------------------------------ *)

Definition l0sys_irun_def:
  l0sys_irun S (ss : num -> sysstate) (rs : num -> syslabel) ⇔
    sys_init S (ss 0) ∧ (∀n. sys_step (ss n) (rs n) (ss (SUC n))) ∧
    ∀k n. k < LENGTH S ⇒ ∃more. prog_makes (EL k S) (proc_events k (GENLIST rs n) ++ more)
End

(* The program, answered as recorded, ends normally after the calls evs *)
Definition finished_def:
  finished (prog : dec list) evs ⇔
    semantics_prog (init_state (replay_ffi evs)) init_env prog (Terminate Success evs)
End

Definition can_step_def:
  can_step S ss rs k n ⇔
    (ss n).alive k ∧
    ((∃nm conf bytes out s' more.
        prog_makes (EL k S) (proc_events k (GENLIST rs n) ++
                             [IO_event (ExtCall nm) conf (ZIP (bytes, out))] ++ more) ∧
        sys_step (ss n) (Call k nm conf bytes out) s') ∨
     finished (EL k S) (proc_events k (GENLIST rs n)))
End

Definition sched_fair_def:
  sched_fair S ss rs ⇔
    ∀k. (∀n0. ∃n. n0 ≤ n ∧ can_step S ss rs k n) ⇒
        ∀n0. ∃n. n0 ≤ n ∧ ((∃nm c b o'. rs n = Call k nm c b o') ∨ rs n = Exit k)
End

(* ------------------------------------------------------------------------
   What a process sees, and when it asks
   ------------------------------------------------------------------------ *)

Definition io_def:
  io (P : num -> bool) ⇔ ∀n0. ∃n. n0 ≤ n ∧ P n
End

(* At step n, fd f of process k is the fd of its channel j *)
Definition fd_at_def:
  fd_at (ss : num -> sysstate) k j f n ⇔ l0_chan_of (EL k (ss n).procs) f = SOME j
End

(* The revents a successful poll in label l reported for fd f *)
Definition poll_saw_def:
  poll_saw k f (l : syslabel) r ⇔
    ∃conf bytes out e.
      l = Call k «sys_poll» conf bytes out ∧ (∃v. dec_res out = SOME (Ok v)) ∧
      MEM e (pollfd_entries (DROP 16 out)) ∧ pe_fd e = f ∧ r = abi_revents (DROP 6 e)
End

(* k asks for input on channel j at step n: a recv on j's fd, or a poll
   listing it for input (moonshot-live's asks_in) *)
Definition asks_in_def:
  asks_in ss rs k j n ⇔
    ∃conf bytes out f.
      fd_at ss k j f n ∧
      ((rs n = Call k «sys_recv» conf bytes out ∧ LENGTH conf = 8 ∧ bytes_fd conf = f) ∨
       (rs n = Call k «sys_poll» conf bytes out ∧
        ∃ev. MEM (f, ev) (MAP pe_fe (pollfd_entries (DROP 16 bytes))) ∧ ODD ev))
End

(* k asks to write on j: a poll listing its fd for output, or a send on it *)
Definition asks_out_def:
  asks_out ss rs k j n ⇔
    ∃conf bytes out f.
      fd_at ss k j f n ∧
      ((rs n = Call k «sys_send» conf bytes out ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = f) ∨
       (rs n = Call k «sys_poll» conf bytes out ∧
        ∃ev. MEM (f, ev) (MAP pe_fe (pollfd_entries (DROP 16 bytes))) ∧ 2 ≤ ev))
End

(* k sees input on j at step n: a recv that returned bytes or end-of-file,
   or a poll reporting j's fd readable (or hung up, or in error) *)
Definition sees_in_def:
  sees_in ss rs k j n ⇔
    ∃f. fd_at ss k j f n ∧
        ((∃conf bytes out m. rs n = Call k «sys_recv» conf bytes out ∧ LENGTH conf = 8 ∧
                             bytes_fd conf = f ∧ dec_res out = SOME (Ok m)) ∨
         ∃r. poll_saw k f (rs n) r ∧ (r.rin ∨ r.rhup ∨ r.rerr))
End

(* k sees j writable at step n: a send that took bytes, or a poll
   reporting j's fd writable (or hung up, or in error) *)
Definition sees_out_def:
  sees_out ss rs k j n ⇔
    ∃f. fd_at ss k j f n ∧
        ((∃conf bytes out m. rs n = Call k «sys_send» conf bytes out ∧ 8 ≤ LENGTH conf ∧
                             bytes_fd (TAKE 8 conf) = f ∧ dec_res out = SOME (Ok m) ∧ 0 < m) ∨
         ∃r. poll_saw k f (rs n) r ∧ (r.rout ∨ r.rhup ∨ r.rerr))
End

(* ------------------------------------------------------------------------
   [F0] kernel fairness, OBSERVED form (the main theorems' hypothesis)
   ------------------------------------------------------------------------ *)

(* io P from n0 on: P holds again after every step *)
Definition io_from_def:
  io_from (n0 : num) (P : num -> bool) ⇔ ∀n1. n0 ≤ n1 ⇒ ∃n. n1 ≤ n ∧ P n
End

Definition kernel_fair_obs_def:
  kernel_fair_obs (ss : num -> sysstate) (rs : num -> syslabel) ⇔
    (* (D) DELIVERY to a receiver that keeps ASKING (a recv, or a poll
       listing the fd for input): the kernel does not hold its bytes back
       for ever.  Owed only to an asking receiver: l0sys inboxes are
       unbounded, so unconditional delivery would drain every channel
       whatever the receiver does, and exclude a stalled reader *)
    (∀e k' j' (n0:num).
       (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e = SOME (k', j') ∧
                     (ss n).moved e < LENGTH (sys_chan (ss n) e).sent) ∧
       io_from n0 (asks_in ss rs k' j') ⇒ F) ∧
    (* (A) ACKNOWLEDGEMENT of moved bytes (they are in the receiver's kernel
       buffer, [T] RFC 9293 §3.4): unconditional *)
    (∀e (n0:num).
       (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧
                     (ss n).acked e < (ss n).moved e) ⇒ F) ∧
    (* (F) EOF AFTER FIN, to a receiver that keeps asking *)
    (∀e k' j' (n0:num).
       (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e = SOME (k', j') ∧
                     (sys_chan (ss n) e).shut ∧ ¬(ss n).finned e ∧
                     (ss n).moved e = LENGTH (sys_chan (ss n) e).sent) ∧
       io_from n0 (asks_in ss rs k' j') ⇒ F) ∧
    (* (C) CONNECT SETTLEMENT: unconditional (as the internal form) *)
    (∀e (n0:num).
       (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (sys_chan (ss n) e).connecting ∧
                     ¬(sys_chan (ss n) e).closed) ⇒ F)
End

(* The OBSERVED OUTCOMES (what processes see), as claims to prove from
   kernel_fair_obs, sched_fair, [F1] and [F2]: an asking receiver with
   bytes owed sees input; an end whose process keeps asking to write, with
   an asking peer, is seen writable; an asking peer of a shut end sees the
   end of file; a pending connect polled for output is seen settled *)
Definition observed_outcomes_def:
  observed_outcomes ss rs ⇔
    (∀k j k' j' n0.
       (∀n. n0 ≤ n ⇒ is_end (ss n) (k', j') ∧ (ss n).peer (k', j') = SOME (k, j) ∧
                     (ss n).moved (k', j') < LENGTH (sys_chan (ss n) (k', j')).sent) ∧
       io (asks_in ss rs k j) ⇒ io (sees_in ss rs k j)) ∧
    (∀k j k' j' n0.
       (∀n. n0 ≤ n ⇒ is_end (ss n) (k, j) ∧ (ss n).peer (k, j) = SOME (k', j')) ∧
       io (asks_out ss rs k j) ∧ io (asks_in ss rs k' j') ⇒ io (sees_out ss rs k j)) ∧
    (∀k j k' j' n0.
       (∀n. n0 ≤ n ⇒ is_end (ss n) (k, j) ∧ (ss n).peer (k, j) = SOME (k', j') ∧
                     (sys_chan (ss n) (k, j)).shut) ∧
       io (asks_in ss rs k' j') ⇒ io (sees_in ss rs k' j')) ∧
    (∀k j n0.
       (∀n. n0 ≤ n ⇒ is_end (ss n) (k, j) ∧ ¬(sys_chan (ss n) (k, j)).closed ∧
                     (sys_chan (ss n) (k, j)).connecting) ∧
       io (asks_out ss rs k j) ⇒ io (sees_out ss rs k j))
End

(* (5) A BLOCKING POLL whose condition becomes true eventually returns: in
   l0sys a blocking poll is a Call step enabled exactly when it may return
   (poll_may_return); so this is sched_fair's strong fairness (can_step),
   not a kernel clause.  Stated as a lemma to prove, not an assumption: *)
Definition blocked_poll_def:
  blocked_poll S ss rs k conf bytes n ⇔
    ∃out s' more.
      prog_makes (EL k S) (proc_events k (GENLIST rs n) ++
                           [IO_event (ExtCall «sys_poll») conf (ZIP (bytes, out))] ++ more) ∧
      sys_step (ss n) (Call k «sys_poll» conf bytes out) s'
End


(* ------------------------------------------------------------------------
   The internal form, and the sanity lemma (to prove)
   ------------------------------------------------------------------------ *)

Definition kernel_fair_def:
  kernel_fair (ss : num -> sysstate) (rs : num -> syslabel) ⇔
    (∀e (n0:num). (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧
                           (ss n).moved e < LENGTH (sys_chan (ss n) e).sent) ⇒ F) ∧
    (∀e (n0:num). (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧
                           (ss n).acked e < (ss n).moved e) ⇒ F) ∧
    (∀e (n0:num). (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e ≠ NONE ∧ (sys_chan (ss n) e).shut ∧
                           ¬(ss n).finned e ∧ (ss n).moved e = LENGTH (sys_chan (ss n) e).sent) ⇒ F) ∧
    (∀e (n0:num). (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (sys_chan (ss n) e).connecting ∧
                           ¬(sys_chan (ss n) e).closed) ⇒ F)
End

(* [F1] per process, on its labels (moonshot-live's F1_sys, restated) *)
Definition retried_lab_def:
  retried_lab (Call k nm conf bytes out) =
    (case dec_res out of
     | SOME (Fail e _) => nm = «sys_poll» ∨ l1_transient e
     | _ => F) ∧
  retried_lab _ = F
End

Definition F1_sys_def:
  F1_sys (S : dec list list) (rs : num -> syslabel) ⇔
    ∀k nm f. k < LENGTH S ∧
             io (λn. ∃conf b out. rs n = Call k nm conf b out ∧ 8 ≤ LENGTH conf ∧
                                  bytes_fd (TAKE 8 conf) = f) ⇒
             io (λn. ∃conf b out. rs n = Call k nm conf b out ∧ 8 ≤ LENGTH conf ∧
                                  bytes_fd (TAKE 8 conf) = f ∧ ¬retried_lab (rs n))
End

Definition F2_sys_def:
  F2_sys S (ss : num -> sysstate) ⇔
    ∀k j h n. k < LENGTH S ∧ 0 < n ⇒ 0 < (EL k (ss 0).procs).ch.takes j h 0 n
End

(* TO PROVE (the sanity lemma): the internal form implies the observed
   one (each clause of kernel_fair_obs is a weakening: immediate) *)
Definition obs_of_internal_claim_def:
  obs_of_internal_claim ⇔ ∀ss rs. kernel_fair ss rs ⇒ kernel_fair_obs ss rs
End

(* TO PROVE (the observed outcomes, the substantive layer) *)
Definition outcomes_claim_def:
  outcomes_claim ⇔
    ∀S ss rs. l0sys_irun S ss rs ∧ sched_fair S ss rs ∧ kernel_fair_obs ss rs ∧
              F1_sys S rs ∧ F2_sys S ss ⇒ observed_outcomes ss rs
End

(* TO PROVE: clause (5) from sched_fair *)
Definition blocking_poll_claim_def:
  blocking_poll_claim ⇔
    ∀S ss rs k conf bytes.
      l0sys_irun S ss rs ∧ sched_fair S ss rs ∧ io (blocked_poll S ss rs k conf bytes) ⇒
      io (λn. ∃c b out. rs n = Call k «sys_poll» c b out)
End

(* The sanity lemma, proved: every clause of kernel_fair_obs weakens one of
   kernel_fair (so the observed form is satisfiable wherever the internal
   one is) *)
Theorem kernel_fair_obs_of_internal:
  kernel_fair ss rs ⇒ kernel_fair_obs ss rs
Proof
  rw[kernel_fair_def, kernel_fair_obs_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘e’, ‘n0’] mp_tac) >> simp[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED
