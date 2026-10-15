(*
  The header-tolerant HTTP server's select set: the listener and the live
  connections (as asyncM4LiveEcho does for echo).

  The HTTP handler meets asyncSWLiveServer's side conditions:
  - its transcript only reads and writes its own fd, so it counts no
    accept and no EOF of another fd (from http_handler_serves_h);
  - it counts at most one EOF of its fd, and none while it is running
    (http_handler_eofs): it stops when a read returns EOF;
  - it waits for nothing but its fd being readable (http_handler_interest).
  So the live fds after the server's transcript cover what it waits for
  (sel_covers_http), and the blocking loop may select on them.

  Note: the handler can also stop without an EOF (an invalid request).
  Its fd then stays in the live list, which still covers the server's
  interest (sel_covers only needs ⊇), but select may then return at once
  for an fd nobody reads: see design note 28 §4.

  MAIN: http_handler_eofs, http_live_ok, quiet_shttp, sel_covers_http.
*)
Theory asyncHttpLiveSel
Ancestors
  pair list rich_list arithmetic option pred_set words
  asyncCore asyncLevel1 asyncLevel2 asyncLoop2 asyncTranscript asyncServer
  asyncServerSafety asyncServer2 asyncServerWith HttpSpec HttpSpecHeaders
  asyncHttpParseH asyncHttpServerH asyncHttpServer2H asyncM4LiveServer
  asyncSWLiveServer asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  asyncM3World asyncM4BlkSelWorld asyncM4LiveEcho
Libs
  preamble

(* ------------------------------------------------------------------------
   The handler at Level 1 and 2
   ------------------------------------------------------------------------ *)

Theorem http_handler2_h_unfold:
  http_handler2_h files p = http_body2_h files (http_handler2_h files) p
Proof
  simp[http_handler2_h_def, Once (MATCH_MP fix2_unfold http_body2_h_contractive)]
QED

Theorem http_handler2_h_run[simp]:
  (http_handler2_h files p).run = http_handler_h files p
Proof
  simp[GSYM erase_http_handler2_h, erase_def]
QED

Theorem http_handler_counts:
  (∀g. accs g (trans (http_handler_h files (fd, buf)) h) = 0) ∧
  (∀g. g ≠ fd ⇒ eofs g (trans (http_handler_h files (fd, buf)) h) = 0)
Proof
  mp_tac (Q.SPECL [‘h’, ‘buf’] http_handler_serves_h) >> strip_tac
  >> simp[accs_def, eofs_def, LENGTH_NIL, FILTER_EQ_NIL]
  >> fs[EVERY_MEM] >> rpt strip_tac >> PairCases_on ‘x’ >> first_x_assum drule
  >> gvs[on_fd_def, is_acc_def, is_eof_def]
QED

(* MAIN: the handler counts at most one EOF of its fd, and none while it is
   running *)
Theorem http_handler_eofs:
  ∀h buf. eofs fd (trans (http_handler_h files (fd, buf)) h) ≤
          if (http_handler_h files (fd, buf) h).result = NONE then 0 else 1
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[http_handler_h_unfold]
  >> Cases_on ‘parse_hrequest buf’ >> simp[]
  (* an invalid request stops: closed by simp *)
  (* a complete request: answer it, then continue *)
  >~ [‘emit (Write fd _)’]
  >- (qmatch_goalsub_abbrev_tac ‘bind (emit WA) KW’
      >> qspecl_then [‘emit WA’, ‘KW’, ‘h’] mp_tac
           (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
      >> simp[wf_emit, settled_emit] >> strip_tac
      >- (gvs[trans_emit, Abbr ‘WA’] >> rw[is_eof_def])
      >> rename1 ‘first_done (emit WA) hw xw’
      >> ‘(bind (emit WA) KW (hw ++ h2)).result = (KW xw h2).result’
           by (irule bind_result_continues >> simp[settled_emit])
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘WA’, Abbr ‘KW’]
      >> simp[is_eof_def])
  (* an incomplete request: wait, read, continue *)
  >> qmatch_goalsub_abbrev_tac ‘bind (readable fd) K0’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- gvs[readable_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> ‘(bind (readable fd) K0 (h1 ++ h2)).result = (K0 () h2).result’
       by (irule bind_result_continues >> simp[readable_def, settled_wait])
  >> gvs[readable_def] >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘bind (emit (Read fd)) K1’
  >> qspecl_then [‘emit (Read fd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (‘(bind (emit (Read fd)) K1 h2).result = NONE’
        by (irule bind_result_running >> simp[]) >>
      gvs[trans_emit] >> Cases_on ‘h2’ >> simp[is_eof_def] >>
      first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def] >>
      Cases_on ‘oHD h.results’ >> simp[])
  >> ‘(bind (emit (Read fd)) K1 (h1' ++ h2')).result = (K1 x h2').result’
       by (irule bind_result_continues >> simp[settled_emit])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> Cases_on ‘res’ >> simp[is_eof_def, return_def, trans_return]
QED

(* The handler waits for nothing but its fd being readable *)
Theorem http_handler_interest:
  ∀h buf. (http_handler2_h files (fd, buf)).interest h ⊆ {Readable fd}
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[http_handler2_h_unfold] >> REWRITE_TAC[http_body2_h_def]
  >> simp[]
  >> Cases_on ‘parse_hrequest buf’ >> simp[return2_def]
  >~ [‘emit2 (Write fd _)’]
  >- (simp[bind2_def]
      >> qmatch_goalsub_abbrev_tac ‘bind_interest C2 K2 h’
      >> qspecl_then [‘C2’, ‘K2’, ‘h’] mp_tac
           (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_cases)
      >> impl_tac >- simp[Abbr ‘C2’, emit2_def, wf_emit, settled_emit]
      >> strip_tac >> simp[]
      >- simp[Abbr ‘C2’, emit2_def]
      >> gvs[Abbr ‘C2’, Abbr ‘K2’, emit2_def]
      >> drule first_done_emit >> strip_tac >> gvs[]
      >> first_x_assum irule >> simp[])
  >> simp[bind2_def]
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C0 K0 h’
  >> qspecl_then [‘C0’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_cases)
  >> impl_tac >- simp[Abbr ‘C0’, wait_on_def, wf_wait, settled_wait]
  >> strip_tac >> simp[]
  >- simp[Abbr ‘C0’, wait_on_def]
  >> ‘h1 ≠ []’ by (gvs[Abbr ‘C0’, wait_on_def] >> metis_tac[first_done_wait_nonempty])
  >> simp[Abbr ‘K0’, bind2_def]
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C1 K1 h2’
  >> qspecl_then [‘C1’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_cases)
  >> impl_tac >- simp[Abbr ‘C1’, emit2_def, wf_emit, settled_emit]
  >> strip_tac >> simp[]
  >- simp[Abbr ‘C1’, emit2_def]
  >> gvs[Abbr ‘C1’, emit2_def]
  >> drule first_done_emit >> strip_tac >> gvs[]
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> Cases_on ‘x'’ >> simp[return2_def]
  >> first_x_assum irule >> simp[]
QED

(* MAIN: the HTTP handler meets the generic server's side conditions *)
Theorem http_live_ok:
  handler_live_ok (λfd. http_handler_h files (fd, ""))
                  (λfd. http_handler2_h files (fd, ""))
Proof
  rw[handler_live_ok_def, http_handler_counts, http_handler_interest]
  >> qspecl_then [‘h’, ‘""’] mp_tac (Q.GEN ‘fd’ http_handler_eofs |> SPEC_ALL
                                     |> Q.GENL [‘h’, ‘buf’])
  >> rw[]
QED

(* ------------------------------------------------------------------------
   The server in the socket vocabulary, and its select set
   ------------------------------------------------------------------------ *)

(* The HTTP server relabelled to sockets, with the Level 2 server's
   declared interest *)
Definition shttp_def:
  shttp files lfd =
    <| run := srelabel (http_server_h files lfd);
       interest := λh. { w : word64 |
                         Readable (w2n w) ∈ (http_server2_h files lfd).interest (MAP sfs h) } |>
End

Definition sel_http_def:
  sel_http files lfd h = live_of [n2w lfd] (trans (srelabel (http_server_h files lfd)) h)
End

Theorem shttp_run:
  (shttp files lfd).run = srelabel (http_server_h files lfd)
Proof
  simp[shttp_def]
QED

Theorem http_server2_h_run:
  (http_server2_h files lfd).run = http_server_h files lfd
Proof
  simp[GSYM erase_http_server2_h, erase_def]
QED

(* MAIN: the HTTP server, relabelled, is quiet for its declared interest *)
Theorem quiet_shttp:
  quiet (shttp files lfd)
Proof
  ‘quiet (http_server2_h files lfd)’ by metis_tac[wf2_http_server2_h, wf2_def] >>
  fs[quiet_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [‘MAP sfs h’, ‘sfs s’, ‘MAP sfs h'’] mp_tac) >>
  impl_tac
  >- (gvs[shttp_def, relabel_def, new_actions_relabel, snap_map_def, sfe_def,
          IN_DISJOINT, http_server2_h_run] >> metis_tac[])
  >> strip_tac >> fs[shttp_def, relabel_def, http_server2_h_run]
QED

Theorem wf_shttp:
  wf (shttp files lfd).run
Proof
  simp[shttp_run] >> irule wf_relabel >> simp[wf_http_server_h]
QED

(* MAIN: the live fds cover what the server waits for *)
Theorem sel_covers_http:
  lfd < dimword(:64) ⇒ sel_covers (shttp files lfd) (sel_http files lfd)
Proof
  rw[sel_covers_def, SUBSET_DEF] >> rename1 ‘w ∈ _’ >>
  gvs[shttp_def, sel_http_def] >>
  qabbrev_tac ‘U = trans (srelabel (http_server_h files lfd)) h’ >>
  ‘TRELS (trans (http_server_h files lfd) (MAP sfs h)) U’
    by (simp[Abbr ‘U’] >> irule trans_relabel >> simp[snap_map_def]) >>
  qspecl_then [‘λfd. http_handler2_h files (fd, "")’,
               ‘λfd. http_handler_h files (fd, "")’, ‘lfd’] mp_tac
    (Q.GENL [‘h2’, ‘hf’, ‘lfd’] sw_live) >>
  simp[http_live_ok, GSYM http_server_h_def, GSYM http_server2_h_def] >>
  disch_then (qspec_then ‘MAP sfs h’ strip_assume_tac) >>
  ‘∀fd. dimword(:64) ≤ fd ⇒ accs fd (trans (http_server_h files lfd) (MAP sfs h)) = 0’
    by (rpt strip_tac >> irule TRELS_accs_big >> simp[] >> metis_tac[]) >>
  drule TRELS_counts >> disch_then (qspec_then ‘w’ strip_assume_tac) >>
  ‘LENGTH (FILTER (is_eof_alias w) (trans (http_server_h files lfd) (MAP sfs h))) =
   eofs (w2n w) (trans (http_server_h files lfd) (MAP sfs h))’
    by (irule eof_alias_eofs >> simp[]) >>
  qspecl_then [‘U’, ‘[n2w lfd]’] mp_tac live_of_occ >> simp[] >> strip_tac >>
  irule occ_MEM >>
  qpat_x_assum ‘∀x. Readable x ∈ _ ⇒ _’ drule >> strip_tac
  >- (‘w = n2w lfd’ by metis_tac[n2w_w2n] >> pop_assum SUBST_ALL_TAC >>
      qpat_x_assum ‘∀g. eofs g _ ≤ _’ (qspec_then ‘lfd’ mp_tac) >>
      gvs[occ_def])
  >> gvs[occ_def]
QED
