# L2 (peers): the headline statements, drafted for review

`peerStatementsScript.sml` states each server's peer-world headline over the
**simple class** of peer worlds: no backpressure, open loop, not filling the
fd space (`nonsat1`: reserved + M + 4 < 2^64 connections in all, user-approved).
`nonsat1` is used **uniformly**, for every claim. Only the converse (⇒)
directions need it, but it is stronger than `nonsat`, so the echo-with-close
claim, whose converse needs only `nonsat`, still follows. The file carries a
verbatim copy of close-v2's `endpointV1EchoConv.nonsat1` (spike/v1-conv); the
copy is removed when L2 is folded. Over all peer worlds these specs are false for our
servers, because a full write under backpressure is a misuse; backpressure,
fd limits and errors are L3's job.

**What the simple class leaves out, and where each piece is covered** (user condition, 2026-10-16: the simple-class scope is acceptable *provided* these are covered later). Status as of 2026-10-17:

| excluded behaviour | covered where | statement or section | status |
|---|---|---|---|
| **backpressure and partial writes** (a server's full write that doesn't fit) | L3: the prefetching L1 wrappers buffer each fd's writes in an outbox, retry partial sends, and pause reading a fd whose outbox is above the high-water mark | design/36 §5.1 (write row) and §6; safety: R1-safe `l1pf_refines_hl` (`honestL1PFRefine`); liveness: R1-live (`fetch_progress`), with per-server obligations S3/S4 (D15) | R1-safe **proved** (model level); `fetch_progress` **proved**; live-data (D16) **in progress** |
| **cross-fd backpressure** (proxies and clients: stop reading A while B's outbox is full) | the moonshot: an L1 pause-policy parameter (`pol_self` for servers, `pol_never` for proxy and client), plus an outbox-level query | design/45 §2.2 (decision Q1 = P2, approved), §2.3 (`S4_relay`), §2.6 (the no-deadlock lemma) | design **approved**; not proved |
| **fd exhaustion** (EMFILE/ENFILE, `fd_limit`) | L3: the L0 world's `fd_limit`, and L1's `exhausted` state (the listener isn't polled until a close frees an fd, which fixes the spin); the moonshot's launch-time `fds_ok` | design/36 §4 (`fd_limit`), §5.1 (accept row), R1-live's connection half under [F3] (D14); design/45 §4.2 (`fds_ok`) | model and wrapper **built** (`exhausted_quiet`); liveness for new connections **in progress** |
| **errors and resets** (ECONNRESET, EPIPE; transient EINTR/ENOBUFS/ENOMEM) | L3: L1 absorbs them (a reset reads as EOF and marks the fd `gone`; transient failures retry). The specs move to the raw trace, so errors stay visible | design/36 §5.1, D16 (live data unless a hard error was observed, plus a corollary with no spurious hard errors), [F1] (D11, weak fairness on transient failures) | R1-safe **proved**; D16 **in progress**; the broken-fd-error gap is **decided**: [F1] restated on observed outcomes (D11′, design/36 §9; for poll, any failure counts) |
| **clients that are not open loop** (reactive peers, the environment reacting to what the server sends) | the moonshot's client, proxy and system theorems (the client never pauses its reads, so it is the sink that makes the waits well-founded) | design/45 §2.5 (the client), §3 (the shared kernel `l0sys`), §4 (system safety; liveness under fairness) | statements **drafted**; not proved |
| **filling the fd space** (`nonsat1`: fewer than 2^64 − reserved − 4 connections in all) | not covered, by design: a model bound far above any real `fd_limit`, which is the real constraint (row 3) | — | permanent idealisation (harmless) |

## The claims

| claim | program | status |
|---|---|---|
| `peer_echo_episodes_claim` | L1's `echo_episodes_prog` | **provable now**, in one step: the converse of `echo_episodes_peer_equiv_thm` (under `nonsat`, implied by `nonsat1`) plus L1's `echo_episodes_prog_spec` |
| `peer_echo_prog_claim` | L0's `echo_prog` | ⏳ needs the version-1 converse (close-v2, spike/v1-conv) and `v1_disciplined 3w echo_prog` |
| `peer_http_prog_claim demo_files http_prog` | L0's `http_prog` | ⏳ the same; `v1_disciplined` still to redo for the series' program |
| `peer_kv_prog_claim kv_prog` | L0's `kv_prog` | ⏳ the same |

**The opening (linking) theorems of L2**, all proved on the spike branches:
- `v2_instance_thm`: the lifetimes world is an exact instance of the peer world;
- `echo_episodes_peer_equiv_thm`: both directions; ⇒ needs `nonsat`;
- `echo_spec_of_peer_disc`, `http_spec_of_peer_disc`, `kv_spec_of_peer_disc`: the core specs from the peer-world forms, for fd-disciplined programs with boundedly many connects (#136).

The file typechecks under its spike names against `spike/echo-sym-disc`
(80d9ca976). It has no Holmakefile here, because the peer theories enter the
final tree only when L2 is folded.
