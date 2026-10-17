# L3-03: the wrappers (L1 over the L0 world)

The verified wrapper layer over the honest L0 FFI (design/36 §5). Source:
`spike/d20-poll` @e282d1996 (`honest-l1`), verbatim apart from the
final-series renames (`design/names.tsv`). The theory names are the spike
names, provisionally.

| theory | what |
|---|---|
| `honestL1Model` | the lazy L1: its state, `l1do` (accept, read, write), the poll, flush and reap, one round |
| `honestL1Props` | what L1 guarantees round by round (§5.1): the round discipline (`read_no_syscall`), `recv_found_empty`, `gone_is_eof`, `stall_local`, `write_buffered`, … |
| `honestL1Simple` | the simple L0 world (`simple0`) and R3: in it L1's wrappers are today's calls (`write_simple`, …) |
| `honestL1Inv` | the lazy L1 never makes a failing L0 call (`l1round_ok`); its fds stay below 2^31 (`small_fds`) |
| `honestL1PFModel` | the prefetching L1 (D10), with D19's bounded flush (`hup_step`) and D20's one poll per round |
| `honestL1PFInv` | the PF L1 never makes a failing L0 call, so its run is total given the handle layer's `hrun_ok` (`psmall`: its fds stay below 2^31) |

The link to the handle layer (R1-safe) is layer 04; R1-live is 05; R2′ is 06.
