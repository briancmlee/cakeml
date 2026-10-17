(*
  DRAFT (moonshot step 9, for review): S4_relay at L1, as a CLAIM (a
  definition; nothing is proved).  For the proxy, feeds k g f ⇔ g and f
  are a pair at round k.

  REVISION 2 (honest-ffi): a handle-layer computation emits a round's
  actions before any of the round's results, so the proxy cannot gate a
  read on a Level answer of the same round, and it writes in round k+1
  what it read in round k.  Its gate is a CREDIT gate: it reads its front
  in round k only if the backend's Level answered in round k−1 (asked
  first in that round), plus the bytes it writes to the backend in rounds
  k−1 and k, is ≤ hw.  With true levels (level_true) that is, at L1:
   - credit_writes: a round k that writes onto f has 2 ≤ k, and f's
     outbox at round k−2's start plus what rounds k−2 and k−1 wrote onto
     f is ≤ hw;
   - chunk_writes: a round writes at most pf_chunk bytes onto an fd (what
     it read in the previous round from the partner's inbox, which a
     fetch fills only when empty, with at most pf_chunk bytes).
  The claim: every outbox is ≤ hw infinitely often (no hypothesis on the
  peer: the D23 drop), and never exceeds hw + pf_chunk.  design/45's
  middle clause ("while B is over hw, A is neither fetched nor read") is
  the program's pauses_feeders plus pol_never's interest: a hypothesis of
  the liveness steps (15–16), not a conclusion here.

  Stated on the PF run (prun); after E1's rebase (done: spike/e1-s4g) it
  moves to the E1 run, whose PF part is this machinery.
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

Definition credit_writes_def:
  credit_writes lfd pol hw ifds m w0 ⇔
    ∀k f. 0 < wbytes lfd pol ifds m w0 f k ⇒
          2 ≤ k ∧
          LENGTH (outbox_of (rstate lfd pol ifds m w0 (k − 2)).b f) +
          wbytes lfd pol ifds m w0 f (k − 2) + wbytes lfd pol ifds m w0 f (k − 1) ≤ hw
End

Definition chunk_writes_def:
  chunk_writes lfd pol ifds m w0 ⇔
    ∀k f. wbytes lfd pol ifds m w0 f k ≤ pf_chunk
End

(* To prove for all arguments *)
Definition S4_relay_claim_def:
  S4_relay_claim lfd pol hw ifds m w0 ⇔
    oassm lfd pol ifds m w0 ∧ credit_writes lfd pol hw ifds m w0 ∧
    chunk_writes lfd pol ifds m w0 ⇒
    ∀f. S4g lfd pol hw ifds m w0 f ∧
        ∀n. LENGTH (outbox_of (rstate lfd pol ifds m w0 n).b f) ≤ hw + pf_chunk
End
