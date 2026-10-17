(*
  Since D31 the guard-free argument (unhanded_sn and the rest) lives in
  honestEchoL0Safe, and echo_safe_l0 has no accept guard; the _ng names
  here are kept as aliases.  Also: handles vs accepts on the trace, and the
  D25 stop seen on the trace (for cf-actions).
*)
Theory honestEchoL0NoGuard
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out honestEchoL0Run
  asyncCore asyncLevel1 asyncTranscript honestL1PFProg honestL1PFSpec
  asyncServer asyncServerSafety asyncM4GTrans
  honestEchoL0Prog honestEchoL0Main honestEchoL0Sem honestL1PFInv honestL1Inv
  honestEchoL0Safe
Libs
  preamble

(* ------------------------------------------------------------------------
   Sends land on handed-out episodes only
   ------------------------------------------------------------------------ *)


Theorem echo_run_safe_ng = echo_run_safe


(* MAIN: the program's trace when the listen succeeds is safe, with no
   guard on the number of connections *)
Theorem echo_l0_run_safe_ng:
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  ∀evs j. LPREFIX (fromList evs) (LCONS ev (echo_l0_run k w1)) ⇒ l0_sent j evs ≼ l0_read j evs
Proof
  strip_tac >> drule_all echo_l0_run_safe >> simp[echo_safe_l0_def]
QED

(* echo_l0_safe has no guard on the number of connections since D31 (and
   its D33 outcomes); this name is kept for the earlier references *)
Theorem echo_l0_safe_ng = echo_l0_safe;

(* ------------------------------------------------------------------------
   Handles and accepts (for the D25 stop on the trace)
   ------------------------------------------------------------------------ *)

Theorem ri_nxt_accepted:
  ri lfd m (h, (w, ps), evs) ⇒ ps.b.nxt + LENGTH ps.acq = LENGTH (l0_accepted evs)
Proof
  rw[ri_def] >> Cases_on ‘l0_ep_st (0, []) evs’ >>
  ‘q = LENGTH (l0_accepted evs)’ by metis_tac[FST_l0_ep_st, FST, ADD] >>
  gvs[own_ok_def]
QED

(* When the echo loop's guard fails, the trace has accepted all but at most
   the round's accepts of the 2^64 − 1 handles *)
Theorem echo_guard_stop:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  prounds_t lfd hw ifds (srelabel (server k)) ws0 n = SOME (h, (w, ps), evs, logs) ∧
  ¬hdl_room lfd ps (naccepts (new_actions (log_of (srelabel (server k))) h)) ⇒
  2 ** 64 ≤ LENGTH (l0_accepted evs) + naccepts (new_actions (log_of (srelabel (server k))) h)
Proof
  strip_tac >> drule_all ri_echo >> strip_tac >>
  drule ri_nxt_accepted >> gvs[hdl_room_def]
QED
