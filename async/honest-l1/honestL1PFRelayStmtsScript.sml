(*
  DRAFT (moonshot step 9, for review): S4_relay at L1, as a CLAIM (a
  definition; nothing is proved).  For the proxy, feeds k g f ⇔ g and f
  are a pair at round k.  Two L2 facts of the relay program, both from the
  Level gate (evaluated at the round's start; true levels by level_true)
  and from writing in a round exactly what it read in that round:
   - gated_writes: nothing is written onto an outbox over hw;
   - chunk_writes: a round writes at most pf_chunk bytes onto an fd (what
     it read from the partner's inbox, which a fetch fills only when empty,
     with at most pf_chunk bytes).
  The claim: every outbox is ≤ hw infinitely often (no hypothesis on the
  peer: the D23 drop), and never exceeds hw + pf_chunk (the bound deferred
  from step 8).  design/45's middle clause ("while B is over hw, A is
  neither fetched nor read") is the program's pauses_feeders plus
  pol_never's interest: a hypothesis of the liveness steps (15–16), not a
  conclusion here.

  Stated on the PF run (prun); after E1's rebase (close-v2) it moves to the
  E1 run, whose PF part is this machinery.
*)
Theory honestL1PFRelayStmts
Ancestors
  honestL1PFS4w honestL1PFOutLive honestL1PFFlush honestL1PFLive honestL1PFModel
Libs
  preamble

(* Bytes written in round k on handles naming f at the round's start or end *)
Definition wbytes_def:
  wbytes lfd pol ifds m w0 f k =
    SUM (MAP (λa. case a of
                  | Write h bs =>
                      if ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME f ∨
                         ALOOKUP (rstate lfd pol ifds m w0 (SUC k)).b.tbl h = SOME f
                      then LENGTH bs else 0
                  | _ => 0) (racts lfd pol ifds m w0 k))
End

Definition gated_writes_def:
  gated_writes lfd pol hw ifds m w0 ⇔
    ∀k f. hw < LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b f) ⇒
          wclean lfd pol ifds m w0 f k
End

Definition chunk_writes_def:
  chunk_writes lfd pol ifds m w0 ⇔
    ∀k f. wbytes lfd pol ifds m w0 f k ≤ pf_chunk
End

(* To prove for all arguments *)
Definition S4_relay_claim_def:
  S4_relay_claim lfd pol hw ifds m w0 ⇔
    oassm lfd pol ifds m w0 ∧ gated_writes lfd pol hw ifds m w0 ∧
    chunk_writes lfd pol ifds m w0 ⇒
    ∀f. S4g lfd pol hw ifds m w0 f ∧
        ∀n. LENGTH (outbox_of (rstate lfd pol ifds m w0 n).b f) ≤ hw + pf_chunk
End
