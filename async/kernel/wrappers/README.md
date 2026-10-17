# L3-03: the wrappers (L1 over the L0 world)

The verified wrapper layer over the honest L0 FFI (design/36 §5). Source:
`spike/d20-poll` @e282d1996 (`honest-l1`), verbatim apart from the
final-series renames (`design/names.tsv`). The theory names are the spike
names, provisionally.

| theory | what |
|---|---|
| `honestL1Model` | the lazy L1: its state, `l1do` (accept, read, write), the poll, flush and reap, one round |
| `honestL1Props` | L1's bookkeeping facts (outboxes, the forget, after a send) |
| `honestL1Simple` | R3: in simple worlds (`simple0`), `write`, `read` and `accept` behave as the plain model's |
| `honestL1Inv` | L1 never fails: every call it makes is well-formed and returns (`lrun_ok`) |
| `honestL1PFModel` | the prefetching L1 (D10), with D19's bounded flush (`hup_step`) and D20's one poll per round |
| `honestL1PFInv` | the PF L1 never fails (`psmall`: its fds stay small) |

The link to the handle layer (R1-safe) is layer 04; R1-live is 05; R2′ is 06.
