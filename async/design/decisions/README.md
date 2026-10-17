# Decisions (one file per decision)

The decision log that used to live in design/36 §9, split so that concurrent additions never
conflict. It lives on branch `shared/base` (owner: devex); every line merges that branch forward.

Guiding rule (the user's): **for every L0 decision, do the honest thing, even if it is more work.**

- **New decision:** the author writes `Dnn.md` (title line, `Status:`, the decision text) on a branch cut
  from `shared/base`, and sends it to the owner, who merges it. Don't add rows to design/36 §9: that
  table is frozen as of this split (its copies on the lines differ; these files are the reference).
- **Amendment:** edit the decision's file, keep the old wording under "Superseded" if it was approved.
- Ids are permanent. Open questions get Q-ids in work/orchestrator/DECISIONS.md and become Dnn here
  once ruled.

| id | decision | status |
|---|---|---|
| [D1](D1.md) | Honesty criterion: the model is a sound over-approximation (every real behaviour | **agreed** |
| [D2](D2.md) | `sys_listen` is made by the program (straight-line, restricted). The constructor | **decided** |
| [D3](D3.md) | Time is fixed in the model | **decided** |
| [D4](D4.md) | Buffered outboxes with read pausing (no server proof changes) | taken on the agents' recommendation; **revisable** |
| [D5](D5.md) | Retire the v1 runnables in favour of v2, and move HTTP onto the v2 handle layer | **approved** (see D5′) |
| [D5′](D5-prime.md) | (D5 approved later the same day) the v1 runnables are retired; L1 and the refine | **approved** |
| [D6](D6.md) | `«sock_write»` stays model-only (for the v1/v2 instance theorems); the honest C  | **agreed** |
| [D7](D7.md) | Chat: drop a slow client at a hard outbox limit | taken on the agents' recommendation; **revisable** |
| [D8](D8.md) | Point (c) of §3.5 | **decided** |
| [D9](D9.md) | The L0 model is anchored on the standards (POSIX.1-2024, RFC 9293/1122), with ci | **decided** |
| [D10](D10.md) | L1 prefetches (§6, option (A)): it fetches input into its own buffers in the rou | **approved** |
| [D11](D11.md) | [F1] | **approved (weak form); restated by D11′** |
| [D11′](D11-prime.md) | [F1] restated on observed outcomes | **approved (user, via coordinator)** |
| [D12](D12.md) | [F2] | **approved** |
| [D13](D13.md) | The L0 connect model is trusted surface: the `connecting` state; the world choic | **approved** |
| [D14](D14.md) | The R1-live statement (§6), with hypotheses [F1] (weak), [F2], S1, S2, D(c) and  | **approved** |
| [D15](D15.md) | R1-live gains S3 (the server reads what it is shown) and S4 (if the peer drains, | **approved** |
| [D16](D16.md) | Spurious hard errors (the L0 model allows any error but EAGAIN as a transient fa | **approved** |
| [D17](D17.md) | Running out of fds at accept. **ENFILE is retried** (only EMFILE pauses). **Whil | **decided (user, via coordinator)** |
| [D18](D18.md) | Spurious accept errors (the analogue of D16 for the listener). **live-conn, main | **decided (user, via coordinator)** |
| [D19](D19.md) | Hung-up fds (user decision, option 2; via async-spike's L3-00 Q-L3-1). On POLLHU | **decided (user, via coordinator)** |
| [D20](D20.md) | sys_poll on CakeML's `struct pollfd` buffer | **decided (user, via coordinator)** |
| [D21](D21.md) | Reset after the peer's EOF | **decided (user, via coordinator)** |
| [D22](D22.md) | shutdown of a pending connect | **decided (user, via coordinator)** |
| [D23](D23.md) | Write timeout | **decided (user, via coordinator)** |
| [D24](D24.md) | counts below 2^64 | **decided (user, via coordinator)** |
| [D25](D25.md) | Handle-room guard counts only Accept actions | **decided (user, via coordinator)** |
| [D25′](D25-prime.md) | Serve-on at the handle cut-off | **approved (user, via coordinator); scheduled after D26 + echo liveness** |
| [D26](D26.md) | Live interest lists | **decided (user, via coordinator)** |
| [D27](D27.md) | Interrupted close | **decided (user, via coordinator)** |
| [D28](D28.md) | Silent input loss is an excuse | **decided (user, via coordinator)** |
| [D29](D29.md) | Handle cut-off in the quiescence claim | **decided (user, via coordinator)** |
| [D30](D30.md) | Strong claim: no transient failure right after the drain | **decided (user, via coordinator)** |
| [D31](D31.md) | `echo_safe_l0` loses its handle guard | **decided (user, via coordinator)** |
| [D32](D32.md) | D28 narrowed: flushed only while the episode is open | **decided (user, via coordinator)** |
| [D33](D33.md) | Stdio checked by the program | **approved (user, via coordinator)** |
| [D34](D34.md) | Strong claim: excused where the channel broke while open | **decided (user, via coordinator)** |
| [D35](D35.md) | Write timeout in time | **approved (user, via coordinator); not implemented yet** |
| [D36](D36.md) | Strong claim: no transient failure of the first poll after the drain | **decided (user, via coordinator)** |
