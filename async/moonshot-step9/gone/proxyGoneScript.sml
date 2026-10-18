(*
  L-D for the proxy (m4-server's buffer bound): after the proxy's start,
  an fd L1 has marked gone at the end of n rounds has every open episode
  excused on the raw trace (a hard error, or the write timeout).
  ldGone.erounds_gone_excuse at the proxy's program.
*)
Theory proxyGone
Ancestors
  ldGone proxyClaim proxyStart proxyL0Run proxyL0Stmts
Libs
  preamble

Theorem proxy_gone_excuse:
  proxy_start a w0 pre w4 k ∧ b < 65536 ∧
  erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n = SOME (h, ws, E, logs) ∧
  MEM f (SND ws).p.b.gone ∧
  proxyL0Stmts$pos_open q (pre ++ E) ∧ proxyL0Stmts$pos_fd q (pre ++ E) = SOME f ⇒
  proxyL0Stmts$pos_hard_err q (fromList (pre ++ E)) ∨ proxyL0Stmts$pos_timed_out pf_sendwait q (fromList (pre ++ E))
Proof
  strip_tac >>
  qspecl_then [‘a’, ‘w0’, ‘pre’, ‘w4’, ‘k’, ‘b’, ‘hw’] mp_tac
    (Q.GENL [‘a’, ‘w0’, ‘pre’, ‘w4’, ‘k’, ‘b’, ‘hw’] proxy_ptot) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  drule proxy_start_facts >> strip_tac >>
  qspecl_then [‘w4’, ‘plfd k’, ‘pol_never’, ‘pifds_k b hw k’, ‘pprog_k b hw k’]
    mp_tac (Q.GENL [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’] erounds_gone_excuse) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[]
QED
