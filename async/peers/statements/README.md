# L2 (peers): the headline statements, drafted for review

`peerStatementsScript.sml` states each server's peer-world headline over the
**simple class** of peer worlds: no backpressure, open loop, not filling the
fd space (`nonsat`). Over all peer worlds these specs are false for our
servers, because a full write under backpressure is a misuse; backpressure,
fd limits and errors are L3's job.

| claim | program | status |
|---|---|---|
| `peer_echo_episodes_claim` | L1's `echo_episodes_prog` | **provable now**, in one step: the converse of `echo_episodes_peer_equiv_thm` (under `nonsat`) plus L1's `echo_episodes_prog_spec` |
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
