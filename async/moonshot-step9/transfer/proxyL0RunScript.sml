(*
  Moonshot step 9, item 5: the proxy's run on the raw L0 trace, and the
  pairing by trace position, shared by the safety part (m4-server,
  proxy_safe_l0) and the liveness parts (honest-ffi, proxy_live_l0 /
  proxy_pairs_l0 / conn_live_l0 / proxy_asks_l0) of l0_proxy_claim.

  - proxy_start a w0 pre w4 k: the start, as e1-driver's proxy_div_n_semantics
    has it (spike/proxy-sem): from a proxy world w0, the three sys_fdok calls
    find fds 0-2 open, the listen on a returns listener k, in world w4; pre is
    those four events.
  - proxy_run_io b hw k w4 pre: the program's whole trace then, pre and E1's
    rounds forever.
  - proxy_pr a b hw k w4 io: position p (an event that got an fd, ev_new) is
    episode io_ep_idx io p = E1's channel j; j is bound to handle hd on the
    handle layer (e1TraceChan.ehbinds), in the world built from the run (pew,
    calls = []); hd's backend is ppair … hd = SOME c; and c's channel is
    episode q.
*)
Theory proxyL0Run
Ancestors
  proxyL0Stmts proxyL1Claim e1DriverLoop e1TraceChan l0sysInv l0sysEpisodes honestL1Model honestL1EPModel
Libs
  preamble

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Definition proxy_start_def:
  proxy_start a w0 pre w4 k ⇔
    l0_proxy_world w0 ∧
    ∃w1 w2 w3 e0 e1 e2 out ev.
      l0_do «sys_fdok» [0w] 1 w0 = SOME ([1w], w1, e0) ∧
      l0_do «sys_fdok» [1w] 1 w1 = SOME ([1w], w2, e1) ∧
      l0_do «sys_fdok» [2w] 1 w2 = SOME ([1w], w3, e2) ∧
      l0_do «sys_listen» (port_bytes a) 13 w3 = SOME (out, w4, ev) ∧
      l0_res_of out = Ok k ∧
      pre = [e0; e1; e2; ev]
End

(* The proxy's E1 parameters, listener k *)
Overload plfd = “λk : num. (n2w k : word64)”
Overload pifds_k = “λb hw k. pifds (n2w k : word64) b hw”
Overload pprog_k = “λb hw k. pprog (n2w k : word64) b hw”

Definition proxy_run_io_def:
  proxy_run_io b hw k w4 pre =
    LAPPEND (fromList pre) (LFLATTEN (LGENLIST
      (λi. fromList (eround_evs (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) i))
      NONE))
End

(* The handle layer's world built from the run *)
Definition proxy_pew_def:
  proxy_pew a b hw k w4 = pew (plfd k) a pol_never (pifds_k b hw k) (pprog_k b hw k) w4 []
End

Definition proxy_lv_def:
  proxy_lv b hw k w4 = elv (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4
End

(* Channel j's handle (bound once, kept: e1TraceChan.ehbinds_lookup_mono) *)
Definition proxy_chan_hdl_def:
  proxy_chan_hdl a b hw k w4 j =
    some hd. ∃n. ALOOKUP (ehbinds (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                                  (proxy_pew a b hw k w4) n) j = SOME hd
End

(* ------------------------------------------------------------------------
   Positions and episode numbers, on the whole (infinite) trace
   ------------------------------------------------------------------------ *)

Definition io_ep_at_def:
  io_ep_at (io : io_event llist) p ⇔ ∃e. LNTH p io = SOME e ∧ ev_new e ≠ NONE
End

Definition io_ep_idx_def:
  io_ep_idx (io : io_event llist) p =
    case LTAKE p io of SOME evs => LENGTH (ep_fds evs) | NONE => 0
End

(* The pairing by position: front p's backend q *)
Definition proxy_pr_def:
  proxy_pr a b hw k w4 io p =
    if io_ep_at io p then
      case proxy_chan_hdl a b hw k w4 (io_ep_idx io p) of
      | NONE => NONE
      | SOME hd =>
          case ppair (plfd k) b hw (proxy_lv b hw k w4) (proxy_pew a b hw k w4) hd of
          | NONE => NONE
          | SOME c => some q. io_ep_at io q ∧ proxy_chan_hdl a b hw k w4 (io_ep_idx io q) = SOME c
    else NONE
End
