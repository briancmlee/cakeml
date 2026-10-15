(*
  What the generic server waits for, in terms of its transcript (model).

  asyncM4LiveServer's server_live, for the accept/fork skeleton at Level 2
  (server_with2 h2, asyncHttpServer2H) with any handler h2 that
  - counts no accept, and no EOF of another fd;
  - counts at most one EOF of its own fd, and none while it is running;
  - waits for nothing but its fd being readable.
  Then every event the server waits for is Readable lfd, or Readable fd
  for a connection accepted more often than a read of it returned EOF:
  the "live" fds the blocking loop selects on.

  MAIN: sw_live.
*)
Theory asyncSWLiveServer
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLevel2 asyncLoop2 asyncTranscript asyncServer
  asyncServerSafety asyncServer2 asyncServerWith asyncHttpServer2H
  asyncM4LiveServer
Libs
  preamble

(* The handler's side conditions, on its Level 1 run hf and its Level 2
   interest *)
Definition handler_live_ok_def:
  handler_live_ok hf h2 ⇔
    ∀fd h. (∀g. accs g (trans (hf fd) h) = 0) ∧
           (∀g. g ≠ fd ⇒ eofs g (trans (hf fd) h) = 0) ∧
           eofs fd (trans (hf fd) h) ≤ 1 ∧
           ((hf fd h).result = NONE ⇒ eofs fd (trans (hf fd) h) = 0) ∧
           (h2 fd).interest h ⊆ {Readable fd}
End

Theorem server_with2_unfold:
  server_with2 h2 lfd = server_with_body2 h2 (server_with2 h2) lfd
Proof
  simp[server_with2_def, Once (MATCH_MP fix2_unfold server_with_body2_contractive)]
QED

Theorem server_with2_run:
  (∀fd. (h2 fd).run = hf fd) ⇒ (server_with2 h2 lfd).run = server_with hf lfd
Proof
  strip_tac >>
  ‘∀fd. erase (h2 fd) = hf fd’ by simp[erase_def] >>
  drule erase_server_with2 >> simp[erase_def]
QED

(* MAIN: the generic server's counts, and what it waits for *)
Theorem sw_live:
  (∀fd. (h2 fd).run = hf fd) ∧ handler_live_ok hf h2 ⇒
  ∀h. (∀g. eofs g (trans (server_with hf lfd) h) ≤ accs g (trans (server_with hf lfd) h)) ∧
      (∀x. Readable x ∈ (server_with2 h2 lfd).interest h ⇒
           x = lfd ∨ eofs x (trans (server_with hf lfd) h) <
                     accs x (trans (server_with hf lfd) h))
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’
  >> ‘trans (server_with hf lfd) h = trans (server_with2 h2 lfd).run h’
       by (drule server_with2_run >> simp[])
  >> pop_assum SUBST1_TAC
  >> ONCE_REWRITE_TAC[server_with2_unfold] >> REWRITE_TAC[server_with_body2_def]
  >> simp[bind2_def]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C0 K0 h’
  >> qmatch_goalsub_abbrev_tac ‘trans (bind C0.run F0) h’
  >> ‘wf C0.run ∧ settled C0.run’ by simp[Abbr ‘C0’, wait_on_def, wf_wait, settled_wait]
  >> qspecl_then [‘C0.run’, ‘h’] strip_assume_tac history_split
  >- (qspecl_then [‘C0.run’, ‘F0’, ‘h’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_running) >>
      qspecl_then [‘C0’, ‘K0’, ‘h’] mp_tac
        (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_running) >>
      simp[] >> rpt strip_tac >> gvs[Abbr ‘C0’, wait_on_def])
  >> gvs[]
  >> ‘h1 ≠ []’ by (gvs[Abbr ‘C0’, wait_on_def] >> metis_tac[first_done_wait_nonempty])
  >> ‘trans (bind C0.run F0) (h1 ++ h2') = trans C0.run h1 ++ trans (F0 ()) h2'’
       by (MATCH_MP_TAC trans_bind_continues >> gvs[])
  >> ‘bind_interest C0 K0 (h1 ++ h2') = (K0 ()).interest h2'’
       by (MATCH_MP_TAC bind_interest_settled >> gvs[])
  >> simp[]
  >> ‘trans C0.run h1 = []’ by simp[Abbr ‘C0’, wait_on_def]
  >> simp[Abbr ‘K0’, Abbr ‘F0’, bind2_def]
  (* accept *)
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C1 K1 h2'’
  >> qmatch_goalsub_abbrev_tac ‘trans (bind C1.run F1) h2'’
  >> ‘wf C1.run ∧ settled C1.run’ by simp[Abbr ‘C1’, emit2_def, wf_emit, settled_emit]
  >> qspecl_then [‘C1.run’, ‘h2'’] strip_assume_tac history_split
  >- (qspecl_then [‘C1.run’, ‘F1’, ‘h2'’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_running) >>
      qspecl_then [‘C1’, ‘K1’, ‘h2'’] mp_tac
        (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_running) >>
      simp[] >> rpt strip_tac >>
      gvs[Abbr ‘C1’, emit2_def, trans_emit] >> rw[is_acc_def, is_eof_def])
  >> rename1 ‘first_done C1.run hA xA’
  >> rename1 ‘h2' = hA ++ hB’
  >> ‘trans (bind C1.run F1) (hA ++ hB) = trans C1.run hA ++ trans (F1 xA) hB’
       by (MATCH_MP_TAC trans_bind_continues >> gvs[])
  >> ‘bind_interest C1 K1 (hA ++ hB) = (K1 xA).interest hB’
       by (MATCH_MP_TAC bind_interest_settled >> gvs[])
  >> gvs[]
  >> gvs[Abbr ‘C1’, emit2_def]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH hB < LENGTH h1 + (LENGTH hB + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, Abbr ‘F1’]
  >> ‘(server_with2 h2 lfd).run = server_with hf lfd’ by (drule server_with2_run >> simp[])
  >> reverse (Cases_on ‘res’) >> simp[is_acc_def, is_eof_def]
  (* no new connection: the rest of the server *)
  >> TRY (qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘hB’ mp_tac) >> simp[] >> NO_TAC)
  (* a new connection fd: its handler, alongside the rest of the server *)
  >> rename1 ‘Accepted fd’
  >> simp[map2_def, both2_def, trans_both_counts]
  >> qabbrev_tac ‘L = left_view (hf fd) (server_with hf lfd) hB’
  >> qabbrev_tac ‘R = right_view (hf fd) (server_with hf lfd) hB’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH hB + 1)’ by simp[Abbr ‘R’]
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[] >> strip_tac
  >> gvs[handler_live_ok_def]
  >> first_assum (qspecl_then [‘fd’, ‘L’] strip_assume_tac)
  >> conj_tac
  >- (gen_tac >>
      qpat_x_assum ‘∀g. eofs g (trans (server_with hf lfd) R) ≤ _’
        (qspec_then ‘g’ assume_tac) >>
      Cases_on ‘fd = g’ >> simp[]
      >- (qpat_x_assum ‘fd = g’ SUBST_ALL_TAC >>
          qpat_x_assum ‘eofs g (trans (hf g) L) ≤ 1’ mp_tac >>
          qpat_x_assum ‘eofs g (trans (server_with hf lfd) R) ≤ _’ mp_tac >>
          rpt (pop_assum kall_tac) >> decide_tac)
      >> qpat_assum ‘∀g. g ≠ fd ⇒ _’ (qspec_then ‘g’ mp_tac) >> simp[])
  >> rpt strip_tac
  >- ((* the handler waits for it: x = fd, and no EOF of fd yet *)
      drule waiting_on_interest >> strip_tac >>
      ‘Readable x ∈ {Readable fd}’ by metis_tac[SUBSET_DEF] >>
      ‘x = fd’ by gvs[] >> pop_assum SUBST_ALL_TAC >>
      ‘(hf fd L).result = NONE’ by gvs[] >>
      qpat_x_assum ‘(hf fd L).result = NONE ⇒ _’ drule >>
      qpat_x_assum ‘∀g. eofs g (trans (server_with hf lfd) R) ≤ _’
        (qspec_then ‘fd’ mp_tac) >> simp[])
  (* the rest of the server waits for it *)
  >> drule waiting_on_interest >> strip_tac
  >> qpat_x_assum ‘∀x. Readable x ∈ (server_with2 h2 lfd).interest R ⇒ _’ drule
  >> strip_tac >> simp[]
  >> Cases_on ‘fd = x’ >> simp[]
  >- (qpat_x_assum ‘fd = x’ SUBST_ALL_TAC >>
      qpat_x_assum ‘eofs x (trans (hf x) L) ≤ 1’ mp_tac >>
      qpat_x_assum ‘eofs x (trans (server_with hf lfd) R) < _’ mp_tac >>
      rpt (pop_assum kall_tac) >> decide_tac)
  >> qpat_assum ‘∀g. g ≠ fd ⇒ _’ (qspec_then ‘x’ mp_tac) >> simp[]
QED
