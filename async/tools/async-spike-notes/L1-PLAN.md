# L1 (lifetimes) fold plan — base: m4-server's RENAMED final/11-it-runs
Branches final/L1-NN-…, each on the previous; sparse worktree; genhm INCLUDES; rename via final-tools (new theory names already final where new).

| layer | branch | dirs (final names) | from |
|---|---|---|---|
| 1.1 trusted surface | final/L1-01-trusted-surface | lifetimes/spec: EchoEpisodesSpec, EchoEpisodesSpecBite; lifetimes/world: lifetimeWorld, lifetimeFair, lifetimePart | review-v2/13: spec-v2, world/sockets-v2 |
| 1.2 the link (opening theorem) | final/L1-02-link | lifetimes/link: lifetimeCore (lifetime_core_link: core run ⇔ lifetimes run, for runs that never close and touch only accepted fds) | spike/lifetime-core (statement 36e948078; proof after user review) |
| 1.3 the echo program | final/L1-03-echo-episodes | lifetimes/world-cf: lifetimeDiv/Prog/Proof; lifetimes/loop: loopHandlesModel/Prog/Spec; lifetimes/echo: echoEpisodes*, lifetimeSim*, lifetimeFairShape; headline/echoEpisodesHeadline | review-v2/13: world/sockets-v2-cf, loop/handles, programs/echo-v2, headline |
| 1.4 HTTP with lifetimes | final/L1-04-http | (close-v2's HTTP-v2 program, #105) | placeholder until it lands |
Notes: link needs only L0 (+ quiet/ffi's ffiAgreeUpto, final/10) and 1.1. Old names in review-v2/13 → apply rename.py before placing.
