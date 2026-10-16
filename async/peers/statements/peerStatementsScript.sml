(*
  L2 (peers) headline STATEMENTS, for review: typecheck only, no proofs.

  Each server's peer-world spec, over the SIMPLE CLASS of peer worlds:
  server worlds offering the calls cs on listener 3w, without backpressure
  (no_backpressure), open loop (open_loop), and not filling the fd space
  (nonsat; user-approved).  Over all peer worlds they are false for our
  servers (a full «sock_write» under backpressure is a misuse); backpressure,
  fd limits and errors are L3's job.

  Status:
  - peer_echo_episodes_claim: provable now, in one step, from
    echo_episodes_peer_equiv_thm's converse (nonsat) and L1's echo_episodes_prog_spec.
  - peer_echo_prog_claim, peer_http_prog_claim, peer_kv_prog_claim (v1 calls):
    PENDING the converse direction for version 1 (close-v2, spike/v1-conv)
    and v1_disciplined for each program (fd discipline; proved for the old
    echo/http copies on spike/fd-discipline, to redo for the series'
    programs).  The other direction is proved: *_spec_of_peer_disc (spike: *_of_endpoint_disc, #136).

  Final names (design/names.tsv; the peer rows are proposals): endpoint* →
  peer*, *_sym_equiv → *_peer_equiv, ep_* constants kept.  TYPECHECKED under
  the spike names against spike/echo-sym-disc 80d9ca976 (l2Statements; green).
  The peer theories are not in the final tree yet (L2 fold pending), so this
  file has no Holmakefile here.
*)
Theory peerStatements
Ancestors
  llist ffi semantics ml_prog EchoSpec EchoEpisodesSpec HttpSpec KvSpec
  peerWorld peerFair peerSpecForms peerServers
  peerInstances peerEchoEpisodesConv echoMain echoEpisodesMain
Libs
  preamble

(* The simple class, for version 1's or version 2's calls *)
Definition simple_class_def:
  simple_class cs lfd a w ⇔
    ep_server_world cs lfd a w ∧ no_backpressure w ∧ open_loop w ∧ nonsat lfd a w
End

(* The echo server (L0's echo_prog), in the peer world *)
Definition peer_echo_prog_claim_def:
  peer_echo_prog_claim ⇔ ∀a. rg_spec (simple_class v1_calls 3w a) ep_echo_guar echo_prog
End

(* The HTTP server; the series' instance is (demo_files, http_prog) *)
Definition peer_http_prog_claim_def:
  peer_http_prog_claim files prog ⇔
    ∀a. rg_spec (simple_class v1_calls 3w a) (ep_http_guar files) prog
End

(* The key-value server; the series' instance is kv_prog *)
Definition peer_kv_prog_claim_def:
  peer_kv_prog_claim prog ⇔ ∀a. rg_spec (simple_class v1_calls 3w a) ep_kv_guar prog
End

(* The echo server with close and fd reuse (L1's echo_episodes_prog) *)
Definition peer_echo_episodes_claim_def:
  peer_echo_episodes_claim ⇔
    ∀a. rg_spec (simple_class v2_calls 3w a) ep_echo2_guar echo_episodes_prog
End
