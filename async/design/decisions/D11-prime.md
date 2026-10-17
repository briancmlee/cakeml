# D11′: [F1] restated on observed outcomes

Status: **approved (user, via coordinator)**

**[F1] restated on observed outcomes** (replaces D11's world-choice form; does not add to it). Per call kind and per fd: a call on f made infinitely often does not return a *retried* outcome infinitely often. Retried = an `l1_transient` error (EAGAIN, EINTR, ENOBUFS, ENOMEM) for recv, accept and send; any failure for poll (L1 retries every failed poll next round). Reason: the weakest single assumption, and no extra narrowing of POSIX. It covers both the world's transient choice and a broken channel's transient-looking errors (`broken_recv`, an `LBreak` error), with no trusted "broken errors are never transient" fact. Stated on the run's IO-event trace (the observed results)

<!-- split from design/36 §9 (spike/echo-live-pol @e179dae84), 2026-10-17 -->
