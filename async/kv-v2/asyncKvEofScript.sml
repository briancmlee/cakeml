(*
  The key-value server does nothing on a connection after reading its EOF
  (kv_server_eof_last : srv_eof_last (kv_server lfd)): what the handle
  layer, which closes a connection as soon as a read returns EOF, needs of
  a server (asyncProtoEof's srv_eof_last).

  The handler returns at Eof (kv_handler_eof_last, on its socket entries:
  untag drops the store's).  Through with_store (trans_with_store) and
  server_with_k (server_with_k_isolates), the server's entries on an fd
  are one handler's.
*)
Theory asyncKvEof
Ancestors
  pair list rich_list asyncCore asyncLevel1 asyncTranscript asyncServer
  asyncServerSafety asyncProgress asyncWithStore asyncServerWithK
  asyncKvHandler asyncKvModel asyncHLEof asyncProtoEof
Libs
  preamble

Theorem untag_FILTER_on_fdk[local]:
  ∀tr. untag (FILTER (on_fdk fd) tr) = FILTER (on_fd fd) (untag tr)
Proof
  Induct >> simp[untag_def] >> PairCases >> Cases_on ‘h0’ >>
  rw[on_fdk_def] >> gvs[GSYM untag_def, on_fd_def] >> simp[untag_def] >>
  gvs[on_fd_def]
QED

Theorem untag_nil[local,simp]:
  untag [] = []
Proof
  simp[untag_def]
QED

Theorem untag_CONS_Sock[local]:
  untag ((Sock x, r) :: tr) =
    (x, case r of SOME (SockR y) => SOME y | _ => NONE) :: untag tr ∧
  untag ((Kv q, r) :: tr) = untag tr
Proof
  simp[untag_def]
QED

(* MAIN: the key-value handler's socket transcript ends at its EOF *)
Theorem kv_handler_eof_last:
  ∀h buf. eof_last fd (untag (trans (kv_handler (fd, buf)) h))
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[kv_handler_unfold]
  >> Cases_on ‘parse_brequest buf’ >> simp[trans_return, untag_nil, eof_last_def]
  (* a complete request: ask the store, answer, continue *)
  >- (rename1 ‘BComplete req rest’
      >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, req))) K0) h’
      >> qspecl_then [‘emit (Kv (fd, req))’, ‘K0’, ‘h’] mp_tac
           (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
      >> simp[wf_emit, settled_emit] >> strip_tac
      >- simp[trans_emit, untag_nil, untag_CONS_Sock, eof_last_def]
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, untag_CONS_Sock]
      >> rename1 ‘oHD s.results = SOME res’
      >> simp[Abbr ‘K0’]
      >> Cases_on ‘res’ >> simp[trans_return, untag_nil, eof_last_def]
      >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Sock (Write fd w))) K1) h2’
      >> qspecl_then [‘emit (Sock (Write fd w))’, ‘K1’, ‘h2’] mp_tac
           (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
      >> simp[wf_emit, settled_emit] >> strip_tac
      >- simp[trans_emit, untag_nil, untag_CONS_Sock, eof_last_def]
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, untag_CONS_Sock, eof_last_def]
      >> simp[Abbr ‘K1’]
      >> qpat_x_assum ‘∀y. _ ⇒ _’ (qspec_then ‘h2'’ mp_tac) >> simp[])
  (* incomplete: wait until fd is readable, read it *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) h’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >> simp[untag_nil, eof_last_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Sock (Read fd))) K1) h2’
  >> qspecl_then [‘emit (Sock (Read fd))’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit, untag_nil, untag_CONS_Sock] >> rw[eof_last_def])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit, untag_CONS_Sock]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, eof_last_def]
  >> Cases_on ‘res’ >> simp[trans_return, untag_nil, eof_last_def]
  >> TRY (rename1 ‘SockR rr’ >> Cases_on ‘rr’ >> simp[trans_return, untag_nil, eof_last_def])
QED

(* MAIN: the key-value server, per accepted connection *)
Theorem kv_server_eof_last:
  srv_eof_last (kv_server lfd)
Proof
  rw[srv_eof_last_def, kv_server_def, trans_with_store, wf_kv_inner] >>
  qmatch_goalsub_abbrev_tac ‘untag (trans _ H)’ >>
  REWRITE_TAC[GSYM untag_FILTER_on_fdk] >>
  ‘freshk (trans (kv_inner lfd) H)’ by fs[freshk_untag] >>
  qspecl_then [‘λfd. kv_handler (fd, "")’, ‘lfd’] mp_tac
    (Q.GENL [‘h’, ‘lfd’] server_with_k_isolates) >>
  impl_tac >- simp[kv_handler_serves] >>
  disch_then (qspec_then ‘H’ mp_tac) >> simp[GSYM kv_inner_def] >> strip_tac >>
  qpat_x_assum ‘∀fd'. _ ∨ _’ (qspec_then ‘fd’ strip_assume_tac) >>
  ASM_REWRITE_TAC[kv_handler_eof_last] >> simp[untag_nil, eof_last_def]
QED
