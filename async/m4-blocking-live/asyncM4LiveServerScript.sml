(*
  What the echo server waits for, in terms of its transcript (model).

  The Level 2 server (asyncServer2) declares the events it waits for.
  Here: they are all on the listener, or on a connection that has been
  accepted more often than a read on it has returned EOF.  (A handler
  finishes exactly when its read returns EOF, and then declares nothing.)

     accs fd tt: the accepts in the transcript tt that handed out fd
     eofs fd tt: the reads of fd in tt that returned EOF

  MAIN:
  - handler_eofs: a handler's transcript has one EOF read of its fd once
    it has finished, none before, and nothing else counted;
  - server_counts: in the server's transcript, eofs fd ≤ accs fd;
  - server_interest_live: every event the server waits for is
    Readable lfd, or Readable fd with eofs fd < accs fd.
  No assumption on the history (in particular, no freshness of fds).
*)
Theory asyncM4LiveServer
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncLoop2 asyncChoose asyncTranscript
  asyncServer asyncServer2 asyncServerSafety
Libs
  preamble

(* ------------------------------------------------------------------------
   Counting accepts and EOFs
   ------------------------------------------------------------------------ *)

Definition is_acc_def:
  is_acc fd (p : action # response option) ⇔
    (∃l. FST p = Accept l) ∧ SND p = SOME (Accepted fd)
End

Definition is_eof_def:
  is_eof fd (p : action # response option) ⇔ FST p = Read fd ∧ SND p = SOME Eof
End

Definition accs_def:
  accs fd tt = LENGTH (FILTER (is_acc fd) tt)
End

Definition eofs_def:
  eofs fd tt = LENGTH (FILTER (is_eof fd) tt)
End

Theorem counts_APPEND[simp]:
  accs fd (xs ++ ys) = accs fd xs + accs fd ys ∧
  eofs fd (xs ++ ys) = eofs fd xs + eofs fd ys
Proof
  simp[accs_def, eofs_def, FILTER_APPEND]
QED

Theorem counts_NIL[simp]:
  accs fd [] = 0 ∧ eofs fd [] = 0
Proof
  simp[accs_def, eofs_def]
QED

Theorem counts_CONS[simp]:
  accs fd (p :: tt) = (if is_acc fd p then 1 else 0) + accs fd tt ∧
  eofs fd (p :: tt) = (if is_eof fd p then 1 else 0) + eofs fd tt
Proof
  simp[accs_def, eofs_def] >> rw[]
QED

Theorem LENGTH_FILTER_FLAT_GENLIST_APPEND[local]:
  ∀k. LENGTH (FILTER P (FLAT (GENLIST (λn. f n ++ g n) k))) =
      LENGTH (FILTER P (FLAT (GENLIST f k))) +
      LENGTH (FILTER P (FLAT (GENLIST g k)))
Proof
  Induct >> simp[GENLIST, SNOC_APPEND, FLAT_APPEND, FILTER_APPEND]
QED

(* Counting over both's transcript: the two sides' counts add up *)
Theorem trans_both_count:
  LENGTH (FILTER P (trans (both m1 m2) h)) =
  LENGTH (FILTER P (trans m1 (left_view m1 m2 h))) +
  LENGTH (FILTER P (trans m2 (right_view m1 m2 h)))
Proof
  simp[trans_def] >>
  ‘GENLIST (round_trans (both m1 m2) h) (SUC (LENGTH h)) =
   GENLIST (λn. round_trans m1 (left_view m1 m2 h) n ++
                round_trans m2 (right_view m1 m2 h) n) (SUC (LENGTH h))’
    by simp[GENLIST_FUN_EQ, round_trans_both] >>
  simp[LENGTH_FILTER_FLAT_GENLIST_APPEND] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem trans_both_counts:
  accs fd (trans (both m1 m2) h) =
    accs fd (trans m1 (left_view m1 m2 h)) + accs fd (trans m2 (right_view m1 m2 h)) ∧
  eofs fd (trans (both m1 m2) h) =
    eofs fd (trans m1 (left_view m1 m2 h)) + eofs fd (trans m2 (right_view m1 m2 h))
Proof
  simp[accs_def, eofs_def, trans_both_count]
QED

(* ------------------------------------------------------------------------
   bind at Level 2: the interest, before and after the first computation
   finishes
   ------------------------------------------------------------------------ *)

Theorem bind_interest_settled:
  settled c.run ∧ first_done c.run h1 x ⇒
  bind_interest c f (h1 ++ h2) = (f x).interest h2
Proof
  rw[bind_interest_def] >>
  drule first_prefix_done_APPEND >> disch_then (qspec_then ‘h2’ assume_tac) >>
  simp[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  ‘new_actions (log_of c.run) h1 = []’ by gvs[settled_def, first_done_def] >>
  gvs[first_done_def]
QED

Theorem bind_result_running:
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒
  (bind m f h).result = NONE
Proof
  strip_tac >> drule bind_running >> simp[]
QED

Theorem bind_result_continues:
  settled m ∧ first_done m h1 x ⇒
  (bind m f (h1 ++ h2)).result = (f x h2).result
Proof
  strip_tac >> drule bind_continues_result >> simp[] >>
  ‘new_actions (log_of m) h1 = []’ by gvs[settled_def, first_done_def] >>
  simp[]
QED

(* ------------------------------------------------------------------------
   One connection
   ------------------------------------------------------------------------ *)

Theorem handler2_unfold:
  handler2 fd = handler_body2 handler2 fd
Proof
  simp[handler2_def, Once (MATCH_MP fix2_unfold handler_body2_contractive)]
QED

Theorem server2_unfold:
  server2 lfd = server_body2 server2 lfd
Proof
  simp[server2_def, Once (MATCH_MP fix2_unfold server_body2_contractive)]
QED

Theorem handler2_run[simp]:
  (handler2 fd).run = handler fd
Proof
  simp[GSYM erase_handler2, erase_def]
QED

Theorem server2_run[simp]:
  (server2 lfd).run = server lfd
Proof
  simp[GSYM erase_server2, erase_def]
QED

(* MAIN: a handler counts no accept, no EOF of another fd, and exactly one
   EOF of its fd once it has finished (none before) *)
Theorem handler_eofs:
  ∀h. accs g (trans (handler fd) h) = 0 ∧
      (g ≠ fd ⇒ eofs g (trans (handler fd) h) = 0) ∧
      eofs fd (trans (handler fd) h) =
        if (handler fd h).result = NONE then 0 else 1
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ONCE_REWRITE_TAC[handler_unfold] >> REWRITE_TAC[handler_body_def]
  >> qmatch_goalsub_abbrev_tac ‘bind (readable fd) K0’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- (‘(bind (readable fd) K0 h).result = NONE’
        by (irule bind_result_running >> gvs[readable_def]) >>
      gvs[readable_def])
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
      gvs[trans_emit] >> Cases_on ‘h2’ >> simp[is_acc_def, is_eof_def] >>
      first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def] >>
      Cases_on ‘oHD h.results’ >> simp[])
  >> ‘(bind (emit (Read fd)) K1 (h1' ++ h2')).result = (K1 x h2').result’
       by (irule bind_result_continues >> simp[settled_emit])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> Cases_on ‘res’ >> simp[is_acc_def, is_eof_def, return_def]
  >> TRY (rename1 ‘Write fd d’
          >> qspecl_then [‘emit (Write fd d)’, ‘λw. handler fd’, ‘h2'’] mp_tac
               (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
          >> simp[wf_emit, settled_emit] >> strip_tac
          >- (‘(bind (emit (Write fd d)) (λw. handler fd) h2').result = NONE’
                by (irule bind_result_running >> simp[]) >>
              gvs[trans_emit, is_acc_def, is_eof_def])
          >> rename1 ‘first_done (emit (Write fd d)) hw xw’
          >> rename1 ‘h2' = hw ++ hr’
          >> ‘(bind (emit (Write fd d)) (λw. handler fd) (hw ++ hr)).result =
              (handler fd hr).result’
               by (qspecl_then [‘emit (Write fd d)’, ‘hw’, ‘xw’, ‘λw. handler fd’, ‘hr’]
                     mp_tac (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] bind_result_continues) >>
                   simp[settled_emit])
          >> drule first_done_emit >> strip_tac
          >> gvs[trans_emit, is_acc_def, is_eof_def]
          >> qpat_x_assum ‘∀y. _’ (qspec_then ‘hr’ mp_tac) >> simp[] >> NO_TAC)
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED

(* Splitting a Level 2 bind's interest: before / after the first part
   finishes (instantiated by the abbreviations of the goal) *)
Theorem bind_interest_cases:
  wf c.run ∧ settled c.run ⇒
  (∀n. n ≤ LENGTH h ⇒ (c.run (TAKE n h)).result = NONE) ∧
  bind_interest c f h = c.interest h ∨
  ∃h1 h2 x. h = h1 ++ h2 ∧ first_done c.run h1 x ∧
            bind_interest c f h = (f x).interest h2
Proof
  strip_tac >>
  qspecl_then [‘c.run’, ‘h’] strip_assume_tac history_split
  >- (disj1_tac >> simp[] >> irule bind_interest_running >> simp[])
  >> disj2_tac >> qexistsl [‘h1’, ‘h2’, ‘x’] >> simp[] >>
  irule bind_interest_settled >> simp[]
QED

(* A handler waits for nothing but its fd being readable *)
Theorem handler_interest:
  ∀h. (handler2 fd).interest h ⊆ {Readable fd}
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ONCE_REWRITE_TAC[handler2_unfold] >> REWRITE_TAC[handler_body2_def]
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
  >> TRY (qmatch_goalsub_abbrev_tac ‘bind_interest C2 K2 h2'’
          >> qspecl_then [‘C2’, ‘K2’, ‘h2'’] mp_tac
               (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_cases)
          >> impl_tac >- simp[Abbr ‘C2’, wf_emit, settled_emit]
          >> strip_tac >> simp[]
          >- simp[Abbr ‘C2’]
          >> gvs[Abbr ‘C2’, Abbr ‘K2’]
          >> drule first_done_emit >> strip_tac >> gvs[]
          >> first_x_assum irule >> simp[] >> NO_TAC)
  >> first_x_assum irule >> simp[]
QED

(* ------------------------------------------------------------------------
   The whole server
   ------------------------------------------------------------------------ *)

Theorem waiting_on_interest:
  x ∈ waiting_on c h ⇒ x ∈ c.interest h ∧ (c.run h).result = NONE
Proof
  rw[waiting_on_def] >> gvs[]
QED

(* MAIN: the server's counts, and what it waits for *)
Theorem server_live:
  ∀h. (∀g. eofs g (trans (server lfd) h) ≤ accs g (trans (server lfd) h)) ∧
      (∀x. Readable x ∈ (server2 lfd).interest h ⇒
           x = lfd ∨ eofs x (trans (server lfd) h) < accs x (trans (server lfd) h))
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ‘trans (server lfd) h = trans (server2 lfd).run h’ by simp[]
  >> pop_assum SUBST1_TAC
  >> ONCE_REWRITE_TAC[server2_unfold] >> REWRITE_TAC[server_body2_def]
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
  >> ‘trans (bind C0.run F0) (h1 ++ h2) = trans C0.run h1 ++ trans (F0 ()) h2’
       by (MATCH_MP_TAC trans_bind_continues >> gvs[])
  >> ‘bind_interest C0 K0 (h1 ++ h2) = (K0 ()).interest h2’
       by (MATCH_MP_TAC bind_interest_settled >> gvs[])
  >> simp[]
  >> ‘trans C0.run h1 = []’ by simp[Abbr ‘C0’, wait_on_def]
  >> simp[Abbr ‘K0’, Abbr ‘F0’, bind2_def]
  (* accept *)
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C1 K1 h2’
  >> qmatch_goalsub_abbrev_tac ‘trans (bind C1.run F1) h2’
  >> ‘wf C1.run ∧ settled C1.run’ by simp[Abbr ‘C1’, emit2_def, wf_emit, settled_emit]
  >> qspecl_then [‘C1.run’, ‘h2’] strip_assume_tac history_split
  >- (qspecl_then [‘C1.run’, ‘F1’, ‘h2’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_running) >>
      qspecl_then [‘C1’, ‘K1’, ‘h2’] mp_tac
        (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_running) >>
      simp[] >> rpt strip_tac >>
      gvs[Abbr ‘C1’, emit2_def, trans_emit] >> rw[is_acc_def, is_eof_def])
  >> rename1 ‘first_done C1.run hA xA’
  >> rename1 ‘h2 = hA ++ hB’
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
  >> reverse (Cases_on ‘res’) >> simp[is_acc_def, is_eof_def]
  (* no new connection: the rest of the server *)
  >> TRY (first_x_assum (qspec_then ‘hB’ mp_tac) >> simp[] >> NO_TAC)
  (* a new connection fd: its handler, alongside the rest of the server *)
  >> rename1 ‘Accepted fd’
  >> simp[map2_def, both2_def, trans_both_counts]
  >> qabbrev_tac ‘L = left_view (handler fd) (server lfd) hB’
  >> qabbrev_tac ‘R = right_view (handler fd) (server lfd) hB’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH hB + 1)’ by simp[Abbr ‘R’]
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[] >> strip_tac
  >> ‘∀g. accs g (trans (handler fd) L) = 0’ by metis_tac[handler_eofs]
  >> ‘∀g. g ≠ fd ⇒ eofs g (trans (handler fd) L) = 0’ by metis_tac[handler_eofs]
  >> ‘eofs fd (trans (handler fd) L) ≤ 1’
       by (mp_tac (Q.SPEC ‘L’ handler_eofs) >> rw[])
  >> conj_tac
  >- (gen_tac >>
      qpat_x_assum ‘∀g. eofs g (trans (server lfd) R) ≤ _’
        (qspec_then ‘g’ assume_tac) >>
      Cases_on ‘g = fd’ >> gvs[] >>
      qpat_x_assum ‘∀g. g ≠ fd ⇒ _’ (qspec_then ‘g’ mp_tac) >> simp[])
  >> rpt strip_tac
  >- ((* the handler waits for it: then x = fd and the handler has not
         finished, so no EOF of fd in its transcript *)
      drule waiting_on_interest >> strip_tac >>
      ‘Readable x ∈ {Readable fd}’ by metis_tac[handler_interest, SUBSET_DEF] >>
      ‘x = fd’ by gvs[] >> pop_assum SUBST_ALL_TAC >>
      ‘eofs fd (trans (handler fd) L) = 0’
        by (mp_tac (Q.SPEC ‘L’ handler_eofs) >> rw[] >> gvs[]) >>
      qpat_x_assum ‘∀g. eofs g (trans (server lfd) R) ≤ _’
        (qspec_then ‘fd’ assume_tac) >> simp[])
  (* the rest of the server waits for it *)
  >> drule waiting_on_interest >> strip_tac
  >> qpat_x_assum ‘∀x. Readable x ∈ (server2 lfd).interest R ⇒ _’ drule
  >> strip_tac >> simp[]
  >> Cases_on ‘x = fd’ >> gvs[]
  >> qpat_x_assum ‘∀g. g ≠ fd ⇒ _’ (qspec_then ‘x’ mp_tac) >> simp[]
QED
