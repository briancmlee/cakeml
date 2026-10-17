(*
  TEMPORARY VERBATIM COPY for moonshotClientLiveStmts: remove at the merge
  with the theories they come from (user policy: temporary copies are fine
  if recorded and removed at merge).  Copied unchanged from:
   - l0_step, l0_replay, ev_lcall, world_at, drains: moonshotLiveCopy
     (spike/moonshot-live @ 3fd01a615), itself a copy of honestL0Part and
     honestL1BStmts;
   - F1_io, F2, hard_err_on: honestL1BStmts (spike/d26-s1-live @ b232bfdc5);
   - in_ask, asks_io, chan_frozen: proxyL0Stmts revision 10
     (spike/moonshot-step9-stmts @ c2506784e).
*)
Theory clientLiveCopy
Ancestors
  llist ffi honestL0 honestL0World honestL1Model honestL1PFRound honestEchoL0SpecCopy
Libs
  preamble

(* ---- moonshotLiveCopy (honestL0Part, honestL1BStmts) ---- *)

Definition l0_step_def:
  l0_step (SOME w) ((n, conf, bytes) : lcall) =
    (case l0_ffi_fn n conf bytes w of
     | SOME (FFIreturn _ w') => SOME w'
     | _ => NONE) ∧
  l0_step NONE _ = NONE
End

Definition l0_replay_def:
  l0_replay w0 (h : lcall list) = FOLDL l0_step (SOME w0) h
End

(* An IO event as the call the L0 world recorded *)
Definition ev_lcall_def:
  ev_lcall (IO_event nm conf bs) =
    ((case nm of ExtCall n => n | _ => «»), conf, MAP FST bs : word8 list)
End

(* The L0 world after the events evs *)
Definition world_at_def:
  world_at w0 evs = l0_replay w0 (MAP ev_lcall evs)
End

Definition drains_def:
  drains w0 io c ⇔
    ∀evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧ c < LENGTH w.chans ∧
            (∀evs' w'. LPREFIX (fromList (evs ++ evs')) io ∧
                       world_at w0 (evs ++ evs') = SOME w' ⇒
                       (EL c w'.chans).sent = (EL c w.chans).sent) ⇒
            ∃evs' w'. LPREFIX (fromList (evs ++ evs')) io ∧
                      world_at w0 (evs ++ evs') = SOME w' ∧
                      c < LENGTH w'.chans ∧ (EL c w'.chans).inflight = 0
End

(* ---- honestL1BStmts ---- *)

Definition F1_io_def:
  F1_io (io : io_event llist) ⇔
    ∀nm f.
      (∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ ev_on nm f ev) ⇒
      (∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ ev_on nm f ev ∧ ¬retried ev)
End

Definition F2_def:
  F2 (w0 : l0world) ⇔ ∀j h n. 0 < n ⇒ 0 < w0.ch.takes j h 0 n
End

Definition hard_err_on_def:
  hard_err_on f (IO_event nm conf bs) ⇔
    (nm = ExtCall «sys_recv» ∨ nm = ExtCall «sys_send») ∧ 8 ≤ LENGTH conf ∧
    bytes_fd (TAKE 8 conf) = f ∧
    ∃e x. l0_ev_res bs = SOME (Fail e x) ∧ ¬l1_transient e
End

(* ---- proxyL0Stmts revision 10 ---- *)

Definition in_ask_def:
  in_ask f ev ⇔
    (∃conf bs. ev = IO_event (ExtCall «sys_recv») conf bs ∧ LENGTH conf = 8 ∧
               bytes_fd conf = f) ∨
    (∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs ∧
               ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e)
End

Definition asks_io_def:
  asks_io f (io : io_event llist) ⇔ ∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ in_ask f ev
End

Definition chan_frozen_def:
  chan_frozen w0 io c ⇔
    ∃evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧ c < LENGTH w.chans ∧
            ((EL c w.chans).peer_eof ∨ (EL c w.chans).broken ∨ (EL c w.chans).closed)
End
