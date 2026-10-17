# L3-05: R1-live, and the output-side link

R1-live for the prefetching L1 (design/36 §6, D14–D18): what the kernel has
pending reaches L1, and through it the version-2 world `psk`. Source:
`spike/d20-poll` @e282d1996 (`honest-l1`). The files are verbatim apart
from the final-series renames (`design/names.tsv`). The theory names are
still the spike's, for now.

| theory | what |
|---|---|
| `honestL1PFRound` | one round seen from one fd: input pending and wanted ⇒ the round polls the fd; a poll that is not retried ⇒ a recv; a recv that is not retried is logged (`pround_f`); the world invariant `winv` |
| `honestL1PFLive` | the fetch half: L1 eventually fetches on an open handle's fd with input pending (`fetch_progress`), given [F1] (D11′), S1, S3 and S4 |
| `honestL1PFStream` | live-data (A): the bytes in an fd's kernel inbox are eventually fetched, in order, unless the episode ends (`live_data_kernel`) |
| `honestL1PFClient` | live-data (B): what L1 fetches on f is client j's data in `psk`; (A) and (B) together (`live_data`) |
| `honestL1PFConn` | live-conn at L0: a listener's queue grows only at the back, and only an accept on it takes from the front (`pround_lfd`) |
| `honestL1PFConnRun` | live-conn along the run (D18): a queued connection is eventually accepted or dropped, or accepts on the listener fail infinitely often (`live_conn_psk`); the corollary under H1 and H3 (`live_conn_cor`) |
| `honestL1PFD16` | the D16 corollary: under HD16 every byte of f's kernel inbox reaches the fetch log, and so `psk`, unless the connection really broke and the kernel discarded unread data (`live_data_d16`, `live_data_psk_d16`) |
| `honestL1PFOut` | R1-safe, the output side: what the kernel took on a connection is what the server wrote to it in `psk`, up to L1's outbox, and a prefix of it once the outbox was dropped (`out_rel`, `l1pf_refines_hl_out`, `l1pf_refines_hl_out_upto`); round by round, `sent` grows by exactly what that round's sends took (`l1pf_round_sent_upto`) |

`honestL1PFOut` is the output-side counterpart of layer 04's
`l1pf_refines_hl`. It sits here, last, because it builds on the R1-live
theories (`PFConnRun`, `PFConn`, `PFClient`, `PFLive`, `PFRound`).

Next is R2′, layer 06.
