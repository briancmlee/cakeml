(*
  TEMPORARY VERBATIM COPY: remove at the merge with the theories they
  come from (user policy: temporary copies are fine if recorded and
  removed at merge).  Copied unchanged from spike/echo-live-pol @fb223e4ad:
   - l0_step, l0_replay: async/honest-l0-cf/honestL0PartScript.sml
     (honestL0Part; also on spike/l3-quiet @0821c6d22);
   - ev_lcall, world_at, drains: async/honest-l1b/honestL1BStmtsScript.sml
     (honestL1BStmts, itself a temporary copy of final/L3-00-statements,
     PR #153).
  N2 (moonshotLiveWorldDrains) proves `drains` from the system's drain;
  the per-program claims take `drains` as their premise.  If #153's
  drains changes, resync this copy.
*)
Theory moonshotLiveCopy
Ancestors
  llist ffi honestL0 honestL0World
Libs
  preamble

(* ---- honestL0Part ---- *)

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

(* ---- honestL1BStmts ---- *)

(* An IO event as the call the L0 world recorded *)
Definition ev_lcall_def:
  ev_lcall (IO_event nm conf bs) =
    ((case nm of ExtCall n => n | _ => «»), conf, MAP FST bs : word8 list)
End

(* The L0 world after the events evs *)
Definition world_at_def:
  world_at w0 evs = l0_replay w0 (MAP ev_lcall evs)
End

(* D(c), per episode (not trusted; the condition under which service is
   owed, D4): the peer reads what it was sent.  If nothing more is sent on
   channel c after a prefix, c's bytes in flight eventually reach 0.
   (Corrected 2026-10-17: the earlier form, "while bytes are in flight, the
   peer's read count `drained` later grows", was satisfied by a peer that
   only makes zero-byte reads, since LDrain j 0 counts as a read; under it
   the echo's replies could stall for ever.  This is the trace form of
   honestL1PFFlush's drains.) *)
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
