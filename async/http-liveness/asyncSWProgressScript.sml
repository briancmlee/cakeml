(*
  Progress of the generic server  server_with hf lfd  (asyncServerWith), for
  any handler hf that is well-formed, settled and only touches its own fd
  (hok).  This is asyncProgress's server part (server_handler_view,
  server_accept_progress), with the echo handler replaced by hf; the proofs
  are those of asyncProgress, with handler_echoes replaced by hok.  The HTTP
  server is the instance hf = λfd. http_handler files (fd, "").
*)
Theory asyncSWProgress
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncServerWith
Libs
  BasicProvers

(* The handler is well-formed, settled, and only reads and writes its own fd *)
Definition hok_def:
  hok hf ⇔
    ∀fd. wf (hf fd) ∧ settled (hf fd) ∧ ∀g. EVERY (on_fd fd) (trans (hf fd) g)
End

Theorem hok_own:
  hok hf ⇒ ∀fd g. EVERY (on_fd fd) (trans (hf fd) g)
Proof
  simp[hok_def]
QED

Theorem hok_wf:
  hok hf ⇒ ∀fd. wf (hf fd)
Proof
  simp[hok_def]
QED

Theorem hok_wf_server_with:
  hok hf ⇒ wf (server_with hf lfd)
Proof
  metis_tac[hok_wf, wf_server_with]
QED

Theorem TAKE_after[local]:
  LENGTH h1 ≤ i ⇒ TAKE i (h1 ++ h2) = h1 ++ TAKE (i - LENGTH h1) h2
Proof
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem TAKE_before[local]:
  i ≤ LENGTH h1 ⇒ TAKE i (h1 ++ h2) = TAKE i h1
Proof
  simp[TAKE_APPEND1]
QED

(* A connection's handler only acts on its own fd, and never accepts *)
Theorem hf_actions_own:
  hok hf ⇒
  MEM a (hf fd h).actions ⇒ a = Read fd ∨ ∃d. a = Write fd d
Proof
  rpt strip_tac >> drule_then (qspecl_then [‘fd’, ‘h’] mp_tac) hok_own
  >> ‘MAP FST (trans (hf fd) h) = (hf fd h).actions’
       by metis_tac[MAP_FST_trans, hok_wf]
  >> rw[EVERY_MEM]
  >> qpat_x_assum ‘MEM a _’ mp_tac
  >> qpat_x_assum ‘MAP FST _ = _’ (SUBST1_TAC o GSYM) >> rw[MEM_MAP]
  >> first_x_assum drule >> PairCases_on ‘y’ >> simp[on_fd_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The server, step by step
   ------------------------------------------------------------------------ *)

(* What the server does with the response to its accept *)
Definition sw_after_accept_def:
  sw_after_accept hf lfd res =
    case res of
      Accepted fd => map (λp. ()) (both (hf fd) (server_with hf lfd))
    | _ => server_with hf lfd
End

Theorem sw_steps:
  server_with hf lfd = bind (readable lfd) (λu. bind (emit (Accept lfd)) (sw_after_accept hf lfd))
Proof
  simp[Once server_with_unfold]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC
  >> simp[FUN_EQ_THM] >> Cases >> simp[sw_after_accept_def]
QED

(* Until the listener is readable, the server has accepted nothing *)
Theorem sw_waiting:
  first_readable lfd h1 ∧ m ≤ LENGTH h1 ⇒
  accepted (trans (server_with hf lfd) (TAKE m h1)) = []
Proof
  rw[] >> ONCE_REWRITE_TAC[sw_steps] >> Cases_on ‘m < LENGTH h1’
  >- (qmatch_goalsub_abbrev_tac ‘trans (bind _ K0) _’
      >> ‘trans (bind (readable lfd) K0) (TAKE m h1) = trans (readable lfd) (TAKE m h1)’
           by (irule trans_bind_running >> gvs[first_readable_def, first_done_def]
               >> rw[] >> ‘TAKE n (TAKE m h1) = TAKE n h1’
                            by (rw[TAKE_TAKE_MIN] >> ‘MIN n m = n’ by simp[MIN_DEF]
                                >> simp[])
               >> simp[])
      >> simp[readable_def])
  >> ‘m = LENGTH h1’ by simp[] >> gvs[TAKE_LENGTH_ID]
  >> qspecl_then [‘readable lfd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Accept lfd)) (sw_after_accept hf lfd)’, ‘[]’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[readable_def]
  >> ‘trans (bind (emit (Accept lfd)) (sw_after_accept hf lfd)) [] =
      trans (emit (Accept lfd)) ([] : (event, response) snapshot list)’
       by (irule trans_bind_running >> simp[emit_def])
  >> simp[trans_emit]
QED

(* Once the listener is readable, the server accepts *)
Theorem sw_accepts:
  first_readable lfd h1 ⇒
  server_with hf lfd (h1 ++ q) = bind (emit (Accept lfd)) (sw_after_accept hf lfd) q
Proof
  rw[first_readable_def] >> ONCE_REWRITE_TAC[sw_steps]
  >> drule_then (qspecl_then [‘λu. bind (emit (Accept lfd)) (sw_after_accept hf lfd)’, ‘q’]
                 mp_tac) bind_continues
  >> simp[new_actions_def, log_of_def, readable_def, wait_def]
  >> simp[outcome_component_equality]
QED

Theorem sw_waiting_actions:
  first_readable lfd h1 ∧ n < LENGTH h1 ⇒
  (server_with hf lfd (TAKE n h1)).actions = []
Proof
  rw[] >> ONCE_REWRITE_TAC[sw_steps]
  >> ‘bind (readable lfd) (λu. bind (emit (Accept lfd)) (sw_after_accept hf lfd)) (TAKE n h1) =
      <|actions := (readable lfd (TAKE n h1)).actions; result := NONE|>’
       by (irule bind_before_first_done >> gvs[first_readable_def] >> metis_tac[])
  >> simp[readable_def, wait_def]
QED

Theorem sw_new_accept:
  first_readable lfd h1 ⇒
  new_actions (log_of (server_with hf lfd)) h1 = [Accept lfd]
Proof
  rw[] >> drule first_readable_nonempty >> strip_tac
  >> ‘(server_with hf lfd h1).actions = [Accept lfd]’
       by (drule_then (qspec_then ‘[]’ mp_tac) sw_accepts >> simp[bind_emit_NIL])
  >> ‘(server_with hf lfd (FRONT h1)).actions = []’
       by (‘FRONT h1 = TAKE (LENGTH h1 - 1) h1’ by simp[FRONT_BY_TAKE]
           >> simp[] >> irule sw_waiting_actions >> simp[]
           >> Cases_on ‘h1’ >> gvs[])
  >> simp[new_actions_def, log_of_def]
QED

(* The accept's response r arrives in s: the server continues with r *)
Theorem sw_after_accept_actions:
  first_readable lfd h1 ∧ oHD s.results = SOME r ⇒
  (server_with hf lfd (h1 ++ [s] ++ q)).actions = Accept lfd :: (sw_after_accept hf lfd r q).actions
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >> drule_then (qspecl_then [‘s :: q’, ‘hf’] SUBST1_TAC) sw_accepts
  >> qspecl_then [‘s’, ‘r’, ‘Accept lfd’, ‘sw_after_accept hf lfd’, ‘q’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS)
  >> simp[]
QED

Theorem sw_trans_accept:
  first_readable lfd h1 ∧ oHD s.results = SOME r ⇒
  trans (server_with hf lfd) (h1 ++ [s] ++ q) =
    (Accept lfd, SOME r) :: trans (sw_after_accept hf lfd r) q
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >> ONCE_REWRITE_TAC[sw_steps]
  >> qspecl_then [‘readable lfd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Accept lfd)) (sw_after_accept hf lfd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> disch_then kall_tac
  >> qspecl_then [‘emit (Accept lfd)’, ‘[s]’, ‘r’, ‘sw_after_accept hf lfd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME, trans_emit, readable_def]
QED

Theorem prompt_sw_after_accept:
  prompt (server_with hf lfd) (h1 ++ [s] ++ q) ∧ first_readable lfd h1 ∧
  oHD s.results = SOME r ⇒
  prompt (sw_after_accept hf lfd r) q
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac
  >> qpat_x_assum ‘prompt _ _’ (mp_tac o ONCE_REWRITE_RULE[sw_steps])
  >> strip_tac
  >> qspecl_then [‘readable lfd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Accept lfd)) (sw_after_accept hf lfd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> strip_tac
  >> qspecl_then [‘emit (Accept lfd)’, ‘[s]’, ‘r’, ‘sw_after_accept hf lfd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME]
QED

Theorem sw_prompt_accept_answered:
  prompt (server_with hf lfd) (h1 ++ [s] ++ q) ∧ first_readable lfd h1 ⇒
  ∃r. oHD s.results = SOME r
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rw[prompt_def] >> first_x_assum (qspec_then ‘LENGTH h1’ mp_tac)
  >> simp[TAKE_LENGTH_APPEND, responses_at_def, EL_APPEND2]
  >> drule sw_new_accept >> simp[]
  >> Cases_on ‘s.results’ >> simp[]
QED

(* ------------------------------------------------------------------------
   A new connection's handler, alongside the rest of the server
   ------------------------------------------------------------------------ *)

Theorem TAKE_after_cons[local]:
  LENGTH h1 + 1 ≤ m ⇒
  TAKE m (h1 ++ [s] ++ h3) = h1 ++ [s] ++ TAKE (m − LENGTH h1 − 1) h3
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rw[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
  >> Cases_on ‘m − LENGTH h1’ >> gvs[]
QED

(* Both sides see the ready sets of the whole history *)
Theorem sw_views_ready:
  i < LENGTH q ⇒
  (EL i (left_view (hf c) (server_with hf lfd) q)).ready = (EL i q).ready ∧
  (EL i (right_view (hf c) (server_with hf lfd) q)).ready = (EL i q).ready
Proof
  strip_tac
  >> qspecl_then [‘log_of (hf c)’, ‘log_of (server_with hf lfd)’, ‘q’] mp_tac
       (Q.GENL [‘a1’, ‘a2’] par_views_world)
  >> rw[left_view_def, right_view_def]
  >> qpat_x_assum ‘MAP _ (FST _) = _’ (mp_tac o Q.AP_TERM ‘EL i’)
  >> qpat_x_assum ‘MAP _ (SND _) = _’ (mp_tac o Q.AP_TERM ‘EL i’)
  >> simp[EL_MAP, LENGTH_par_views]
QED

Theorem LENGTH_views_sw[local]:
  LENGTH (left_view m1 m2 q) = LENGTH q ∧ LENGTH (right_view m1 m2 q) = LENGTH q
Proof
  simp[left_view_def, right_view_def, LENGTH_par_views]
QED

Theorem hf_no_accepts[local]:
  hok hf ⇒
  FILTER is_accept (trans (hf c) h) = []
Proof
  strip_tac >> drule_then (qspecl_then [‘c’, ‘h’] mp_tac) hok_own
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> PairCases_on ‘x’ >> gvs[on_fd_def, is_accept_def]
QED

(* The connections accepted alongside a handler are the rest of the server's *)
Theorem sw_accepted_both:
  hok hf ⇒
  accepted (trans (both (hf c) (server_with hf lfd)) q) =
  accepted (trans (server_with hf lfd) (right_view (hf c) (server_with hf lfd) q))
Proof
  strip_tac >> ONCE_REWRITE_TAC[GSYM accepted_FILTER] >> AP_TERM_TAC
  >> irule trans_both_filter_right >> gs[hf_no_accepts]
QED

(* Another connection's actions alongside a handler are the rest of the
   server's *)
Theorem sw_filter_both_other:
  hok hf ⇒
  fd ≠ c ⇒
  FILTER (on_fd fd) (trans (both (hf c) (server_with hf lfd)) q) =
  FILTER (on_fd fd) (trans (server_with hf lfd) (right_view (hf c) (server_with hf lfd) q))
Proof
  rpt strip_tac >> irule trans_both_filter_right
  >> drule_then (qspecl_then [‘c’, ‘left_view (hf c) (server_with hf lfd) q’] mp_tac)
       hok_own
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> PairCases_on ‘x’ >> gvs[on_fd_def] >> metis_tac[]
QED

(* The connection's own actions alongside its handler are the handler's,
   if the rest of the server never touches it *)
Theorem sw_filter_both_own:
  hok hf ⇒
  FILTER (on_fd c) (trans (server_with hf lfd) (right_view (hf c) (server_with hf lfd) q)) = [] ⇒
  FILTER (on_fd c) (trans (both (hf c) (server_with hf lfd)) q) =
  trans (hf c) (left_view (hf c) (server_with hf lfd) q)
Proof
  rpt strip_tac >> drule trans_both_filter_left >> simp[]
  >> disch_then kall_tac >> simp[FILTER_EQ_ID]
  >> drule_then (qspecl_then [‘c’, ‘left_view (hf c) (server_with hf lfd) q’] mp_tac)
       hok_own
  >> simp[]
QED

Theorem sw_nreads_both:
  hok hf ⇒
  nreads fd (both (hf c) (server_with hf lfd) q).actions =
  nreads fd (hf c (left_view (hf c) (server_with hf lfd) q)).actions +
  nreads fd (server_with hf lfd (right_view (hf c) (server_with hf lfd) q)).actions
Proof
  strip_tac >> simp[nreads_count] >> irule count_both >>
  metis_tac[hok_wf, hok_wf_server_with]
QED

Theorem nreads_hf_other:
  hok hf ⇒
  fd ≠ c ⇒ nreads fd (hf c h).actions = 0
Proof
  rw[nreads_def, FILTER_EQ_NIL, EVERY_MEM] >> strip_tac
  >> drule_all hf_actions_own >> simp[]
QED

(* If the server never touches c, none of its prefixes reads c *)
Theorem nreads_sw_untouched:
  hok hf ⇒
  ¬EXISTS (on_fd c) (trans (server_with hf lfd) R) ⇒
  nreads c (server_with hf lfd (TAKE j R)).actions = 0
Proof
  rw[nreads_count] >> irule count_prefix
  >> qexists_tac ‘(server_with hf lfd R).actions’
  >> reverse conj_tac
  >- (irule wf_actions_grow >> gs[hok_wf_server_with, IS_PREFIX_APPEND] >>
      metis_tac[TAKE_DROP])
  >> ‘MAP FST (trans (server_with hf lfd) R) = (server_with hf lfd R).actions’
       by metis_tac[MAP_FST_trans, hok_wf_server_with]
  >> pop_assum (SUBST1_TAC o GSYM)
  >> gvs[count_def, FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, EXISTS_MEM]
  >> rpt strip_tac >> first_x_assum drule >> PairCases_on ‘y’ >> gvs[on_fd_def]
QED

(* If the server has accepted something, it waited for the listener (h1),
   accepted, and got the response r (in s) *)
Theorem sw_split:
  prompt (server_with hf lfd) h ∧ accepted (trans (server_with hf lfd) h) ≠ [] ⇒
  ∃h1 s h3 r. h = h1 ++ [s] ++ h3 ∧ first_readable lfd h1 ∧ oHD s.results = SOME r
Proof
  strip_tac
  >> qspecl_then [‘readable lfd : (event, response) snapshot list ->
                                  (action, unit option) outcome’, ‘h’]
       strip_assume_tac history_split
  >- (‘trans (server_with hf lfd) h = trans (readable lfd) h’
        by (ONCE_REWRITE_TAC[sw_steps] >> irule trans_bind_running >> simp[])
      >> qpat_x_assum ‘trans _ _ = trans _ _’ mp_tac
      >> simp[readable_def] >> strip_tac >> gvs[])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[]
  >> ‘first_readable lfd h1’ by simp[first_readable_def]
  >> Cases_on ‘h2’
  >- (drule_then (qspecl_then [‘LENGTH h1’, ‘hf’] mp_tac) sw_waiting >> gvs[])
  >> qspecl_then [‘lfd’, ‘h1’, ‘h’, ‘t’] mp_tac
       (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘q’] sw_prompt_accept_answered)
  >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[] >> strip_tac
  >> qexistsl_tac [‘h1’, ‘h’, ‘t’, ‘r’] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
  >> simp[]
QED

(* MAIN: inside the server, each accepted connection fd is served by its own
   handler, running on a view g of the server's history from the round a in
   which fd was accepted: g has the same ready sets, the world answers the
   handler promptly, the handler's transcript is the server's transcript
   restricted to fd, and the server's reads of fd are the handler's. *)
Theorem sw_handler_view:
  ∀h. hok hf ∧ fresh (trans (server_with hf lfd) h) ∧ prompt (server_with hf lfd) h ∧
      MEM fd (accepted (trans (server_with hf lfd) h)) ⇒
      ∃a g. LENGTH g + a = LENGTH h ∧
            (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) h).ready) ∧
            prompt (hf fd) g ∧
            FILTER (on_fd fd) (trans (server_with hf lfd) h) = trans (hf fd) g ∧
            (∀j. j ≤ LENGTH g ⇒
                 nreads fd (server_with hf lfd (TAKE (a + j) h)).actions =
                 nreads fd (hf fd (TAKE j g)).actions) ∧
            (∀m. m ≤ LENGTH h ∧ MEM fd (accepted (trans (server_with hf lfd) (TAKE m h))) ⇒
                 a ≤ m)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt strip_tac
  (* the server waited (h1), accepted, and got the response r (in s) *)
  >> ‘accepted (trans (server_with hf lfd) h) ≠ []’ by (strip_tac >> gvs[])
  >> drule_all sw_split >> strip_tac >> gvs[]
  >> ‘∀m. LENGTH h1 + 1 ≤ m ⇒
          trans (server_with hf lfd) (TAKE m (h1 ++ [s] ++ h3)) =
            (Accept lfd, SOME r) ::
            trans (sw_after_accept hf lfd r) (TAKE (m − LENGTH h1 − 1) h3) ∧
          (server_with hf lfd (TAKE m (h1 ++ [s] ++ h3))).actions =
            Accept lfd :: (sw_after_accept hf lfd r (TAKE (m − LENGTH h1 − 1) h3)).actions’
       by (rpt strip_tac >> simp[TAKE_after_cons]
           >> qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘TAKE (m − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sw_trans_accept)
           >> qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘TAKE (m − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sw_after_accept_actions)
           >> simp[])
  >> ‘trans (server_with hf lfd) (h1 ++ [s] ++ h3) =
      (Accept lfd, SOME r) :: trans (sw_after_accept hf lfd r) h3’
       by (qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘h3’] mp_tac
             (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sw_trans_accept) >> simp[])
  >> ‘∀m. m ≤ LENGTH h1 ⇒ accepted (trans (server_with hf lfd) (TAKE m (h1 ++ [s] ++ h3))) = []’
       by (rpt strip_tac >> ‘TAKE m (h1 ++ [s] ++ h3) = TAKE m h1’ by simp[TAKE_APPEND1]
           >> simp[] >> irule sw_waiting >> simp[])
  >> drule_all prompt_sw_after_accept >> strip_tac
  >> Cases_on ‘∃c. r = Accepted c’
  (* a new connection c: its handler runs on L, the rest of the server on R *)
  >- (pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC
      >> qabbrev_tac ‘L = left_view (hf c) (server_with hf lfd) h3’
      >> qabbrev_tac ‘R = right_view (hf c) (server_with hf lfd) h3’
      >> ‘∀q. trans (sw_after_accept hf lfd (Accepted c)) q =
              trans (both (hf c) (server_with hf lfd)) q ∧
              (sw_after_accept hf lfd (Accepted c) q).actions =
              (both (hf c) (server_with hf lfd) q).actions’
           by simp[sw_after_accept_def, map_def]
      >> ‘accepted (trans (server_with hf lfd) (h1 ++ [s] ++ h3)) =
          c :: accepted (trans (server_with hf lfd) R)’
           by simp[sw_accepted_both, Abbr ‘R’]
      >> ‘¬MEM c (accepted (trans (server_with hf lfd) R)) ∧ fresh (trans (server_with hf lfd) R)’
           by gvs[fresh_def]
      >> ‘prompt (hf c) L ∧ prompt (server_with hf lfd) R’
           by (gvs[sw_after_accept_def] >> drule prompt_both >> simp[Abbr ‘L’, Abbr ‘R’])
      (* the rest of the server never touches c *)
      >> ‘¬EXISTS (on_fd c) (trans (server_with hf lfd) R)’
           by (strip_tac >>
               ‘∀fd hh. EVERY (on_fd fd) (trans (hf fd) hh)’ by metis_tac[hok_own] >>
               drule server_with_isolates >> disch_then drule >> metis_tac[])
      >> Cases_on ‘fd = c’
      (* fd is this connection: it is served by its handler, on L *)
      >- (rpt BasicProvers.VAR_EQ_TAC >> qexistsl_tac [‘LENGTH h1 + 1’, ‘L’]
          >> rpt conj_tac
          >- simp[Abbr ‘L’]
          >- (rpt strip_tac >> gvs[Abbr ‘L’, sw_views_ready]
              >> simp[EL_APPEND2, EL_CONS, PRE_SUB1, sw_views_ready])
          >- simp[]
          >- (simp[] >> simp[Abbr ‘L’] >> irule sw_filter_both_own
              >> gvs[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM, Abbr ‘R’])
          >- (rpt strip_tac
              >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
                   (qspec_then ‘LENGTH h1 + 1 + j’ mp_tac)
              >> simp[sw_nreads_both, views_TAKE]
              >> strip_tac >> irule nreads_sw_untouched >> fs[])
          >> rpt strip_tac >> spose_not_then assume_tac
          >> qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
          >> impl_tac >- simp[] >> strip_tac
          >> qpat_x_assum ‘MEM c (accepted (trans _ (TAKE _ _)))’ mp_tac
          >> ASM_REWRITE_TAC[MEM])
      (* fd is another connection: it is served inside the rest of the server *)
      >> ‘LENGTH R = LENGTH h3 ∧ ∀i. i < LENGTH h3 ⇒ (EL i R).ready = (EL i h3).ready’
           by simp[Abbr ‘R’, sw_views_ready]
      >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘R’ mp_tac)
      >> impl_tac >- simp[] >> impl_tac >- gvs[] >> strip_tac
      >> rename1 ‘a1 + LENGTH g1 = LENGTH R’
      >> qexistsl_tac [‘LENGTH h1 + 1 + a1’, ‘g1’] >> rpt conj_tac
      >- simp[]
      >- (rpt strip_tac >> ‘a1 + i < LENGTH h3’ by simp[]
          >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
      >- simp[]
      >- (‘FILTER (on_fd fd) (trans (both (hf c) (server_with hf lfd)) h3) =
           FILTER (on_fd fd) (trans (server_with hf lfd) R)’
            by simp[sw_filter_both_other, Abbr ‘R’]
          >> simp[])
      >- (rpt strip_tac
          >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
               (qspec_then ‘LENGTH h1 + 1 + a1 + j’ mp_tac)
          >> simp[sw_nreads_both, views_TAKE, nreads_hf_other])
      >> rpt strip_tac >> Cases_on ‘m ≤ LENGTH h1’
      >- (qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
          >> impl_tac >- simp[] >> strip_tac
          >> qpat_x_assum ‘MEM fd (accepted (trans _ (TAKE _ _)))’ mp_tac
          >> ASM_REWRITE_TAC[MEM])
      >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’ (qspec_then ‘m’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac
      >> ‘MEM fd (accepted (trans (server_with hf lfd) (TAKE (m − LENGTH h1 − 1) R)))’
           by (qpat_x_assum ‘MEM fd (accepted (trans _ (TAKE m _)))’ mp_tac
               >> simp[sw_accepted_both, views_TAKE, Abbr ‘R’])
      >> qpat_x_assum ‘∀m. m ≤ LENGTH R ∧ _ ⇒ _’ (qspec_then ‘m − LENGTH h1 − 1’ mp_tac)
      >> simp[])
  (* no new connection: the server starts again *)
  >> ‘sw_after_accept hf lfd r = server_with hf lfd’ by (Cases_on ‘r’ >> gvs[sw_after_accept_def])
  >> ‘∀tr. accepted ((Accept lfd, SOME r) :: tr) = accepted tr’ by (Cases_on ‘r’ >> gvs[])
  >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘h3’ mp_tac)
  >> impl_tac >- simp[]
  >> impl_tac
  >- (qpat_x_assum ‘fresh _’ mp_tac >> qpat_x_assum ‘MEM fd _’ mp_tac
      >> qpat_x_assum ‘prompt (sw_after_accept _ _ _) _’ mp_tac >> simp[fresh_def])
  >> strip_tac
  >> rename1 ‘a1 + LENGTH g1 = LENGTH h3’
  >> qexistsl_tac [‘LENGTH h1 + 1 + a1’, ‘g1’] >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
  >- simp[]
  >- simp[]
  >- (rpt strip_tac
      >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
           (qspec_then ‘LENGTH h1 + 1 + a1 + j’ mp_tac)
      >> simp[])
  >> rpt strip_tac >> Cases_on ‘m ≤ LENGTH h1’
  >- (qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac
      >> qpat_x_assum ‘MEM fd (accepted (trans _ (TAKE _ _)))’ mp_tac
      >> ASM_REWRITE_TAC[MEM])
  >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’ (qspec_then ‘m’ mp_tac)
  >> impl_tac >- simp[] >> strip_tac
  >> qpat_x_assum ‘∀m. m ≤ LENGTH h3 ∧ _ ⇒ _’ (qspec_then ‘m − LENGTH h1 − 1’ mp_tac)
  >> gvs[]
QED

(* ------------------------------------------------------------------------
   The listener: the server keeps accepting
   ------------------------------------------------------------------------ *)

Definition naccepts_def:
  naccepts lfd acts = count (λa. a = Accept lfd) acts
End

Theorem naccepts_simps[simp]:
  naccepts lfd [] = 0 ∧
  naccepts lfd (a :: as) = (if a = Accept lfd then 1 else 0) + naccepts lfd as
Proof
  rw[naccepts_def, count_def]
QED

(* A fresh server, on a history whose first snapshot has the listener
   readable, accepts straight away *)
Theorem sw_fresh_accepts:
  q ≠ [] ∧ Readable lfd ∈ (HD q).ready ∧ 1 ≤ i ⇒
  1 ≤ naccepts lfd (server_with hf lfd (TAKE i q)).actions
Proof
  Cases_on ‘q’ >> rw[]
  >> drule readable_now >> strip_tac
  >> ‘TAKE i (h::t) = [h] ++ TAKE (i - 1) t’ by (Cases_on ‘i’ >> gvs[])
  >> drule_then (qspecl_then [‘TAKE (i - 1) t’, ‘hf’] mp_tac) sw_accepts
  >> simp[] >> strip_tac
  >> qspecl_then [‘Accept lfd’, ‘sw_after_accept hf lfd’, ‘TAKE (i - 1) t’] strip_assume_tac
       (Q.GENL [‘a’, ‘f’, ‘q’] bind_emit_starts)
  >> simp[]
QED

(* After an accept, the server runs on a view V of the rest of the history
   (the right side of both, if a connection was accepted): V has the same
   ready sets, and the accepts are V's *)
Theorem sw_after_accept_view:
  hok hf ⇒
  prompt (sw_after_accept hf lfd r) q ⇒
  ∃V. LENGTH V = LENGTH q ∧
      (∀i. i < LENGTH q ⇒ (EL i V).ready = (EL i q).ready) ∧
      prompt (server_with hf lfd) V ∧
      ∀j. naccepts lfd (sw_after_accept hf lfd r (TAKE j q)).actions =
          naccepts lfd (server_with hf lfd (TAKE j V)).actions
Proof
  Cases_on ‘∃c. r = Accepted c’
  >- (gvs[sw_after_accept_def] >> rpt strip_tac
      >> qexists_tac ‘right_view (hf c) (server_with hf lfd) q’
      >> drule prompt_both >> simp[sw_views_ready, map_def] >> rpt strip_tac
      >> simp[naccepts_def]
      >> qspecl_then [‘hf c’, ‘server_with hf lfd’, ‘λa. a = Accept lfd’, ‘TAKE j q’] mp_tac
           (Q.GENL [‘m1’, ‘m2’, ‘P’, ‘h’] count_both)
      >> impl_tac >- metis_tac[hok_wf, hok_wf_server_with]
      >> simp[views_TAKE]
      >> rw[count_def, FILTER_EQ_NIL, EVERY_MEM] >> strip_tac
      >> drule_all hf_actions_own >> simp[])
  >> ‘sw_after_accept hf lfd r = server_with hf lfd’ by (Cases_on ‘r’ >> gvs[sw_after_accept_def])
  >> rw[] >> qexists_tac ‘q’ >> simp[]
QED

(* MAIN: progress of the listener.  If the listener is readable in two
   snapshots in a row (k, k+1), and the world answers promptly, then the
   server accepts during those rounds.  Two, because one cycle of the
   server is: wait, accept (one round for the response). *)
Theorem sw_accept_progress:
  ∀h k. hok hf ∧ prompt (server_with hf lfd) h ∧ k + 2 ≤ LENGTH h ∧
        (∀j. k ≤ j ∧ j < k + 2 ⇒ Readable lfd ∈ (EL j h).ready) ⇒
        naccepts lfd (server_with hf lfd (TAKE k h)).actions <
        naccepts lfd (server_with hf lfd (TAKE (k + 2) h)).actions
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt strip_tac
  (* the server's first wait ends at the latest in snapshot k *)
  >> qspecl_then [‘k’, ‘h’, ‘lfd’] mp_tac (Q.GENL [‘j’, ‘h’, ‘fd’] readable_split)
  >> simp[] >> strip_tac >> gvs[]
  >> Cases_on ‘LENGTH h1 = k + 1’
  (* it ends in snapshot k: the first accept is in round k *)
  >- (‘(server_with hf lfd (TAKE k (h1 ++ h2))).actions = []’
        by simp[TAKE_before, sw_waiting_actions]
      >> simp[TAKE_after] >> drule_then (qspecl_then [‘TAKE 1 h2’, ‘hf’] SUBST1_TAC) sw_accepts
      >> qspecl_then [‘Accept lfd’, ‘sw_after_accept hf lfd’, ‘TAKE 1 h2’] strip_assume_tac
           (Q.GENL [‘a’, ‘f’, ‘q’] bind_emit_starts)
      >> simp[])
  (* it ends earlier: the server accepts, the response r arrives in s1, and
     the server continues on a view V of the rest *)
  >> ‘LENGTH h1 ≤ k’ by simp[] >> Cases_on ‘h2’ >- gvs[] >> rename1 ‘h1 ++ s1 :: h3’
  >> ‘h1 ++ s1 :: h3 = h1 ++ [s1] ++ h3’ by simp[] >> pop_assum SUBST_ALL_TAC
  >> drule_all sw_prompt_accept_answered >> strip_tac
  >> ‘∀i. LENGTH h1 + 1 ≤ i ⇒
          naccepts lfd (server_with hf lfd (TAKE i (h1 ++ [s1] ++ h3))).actions =
          1 + naccepts lfd (sw_after_accept hf lfd r (TAKE (i − LENGTH h1 − 1) h3)).actions’
       by (rpt strip_tac >> simp[TAKE_after_cons]
           >> qspecl_then [‘lfd’, ‘h1’, ‘s1’, ‘r’, ‘TAKE (i − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sw_after_accept_actions)
           >> simp[])
  >> ‘naccepts lfd (server_with hf lfd (TAKE (LENGTH h1) (h1 ++ [s1] ++ h3))).actions = 1’
       by (‘TAKE (LENGTH h1) (h1 ++ [s1] ++ h3) = h1 ++ []’ by simp[TAKE_APPEND1]
           >> pop_assum SUBST1_TAC >> drule sw_accepts >> simp[bind_emit_NIL])
  >> drule_all prompt_sw_after_accept >> strip_tac >> drule_all sw_after_accept_view >> strip_tac
  >> Cases_on ‘LENGTH h1 + 1 ≤ k’
  (* the window starts after the restart: by induction *)
  >- (qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘V’ mp_tac) >> simp[]
      >> disch_then (qspec_then ‘k − LENGTH h1 − 1’ mp_tac)
      >> impl_tac
      >- (conj_tac >- fs[]
          >> rpt strip_tac >> ‘j < LENGTH h3’ by fs[] >> simp[]
          >> qpat_x_assum ‘∀j. k ≤ j ∧ _ ⇒ _’ (qspec_then ‘j + LENGTH h1 + 1’ mp_tac)
          >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
      >> ‘k − LENGTH h1 − 1 + 2 = k + 1 − LENGTH h1 ∧
          k − LENGTH h1 − 1 = k − (LENGTH h1 + 1)’ by simp[]
      >> simp[])
  (* the restart is in the window: the restarted server accepts at once *)
  >> ‘k = LENGTH h1’ by simp[] >> gvs[]
  >> ‘V ≠ [] ∧ Readable lfd ∈ (HD V).ready’
       by (Cases_on ‘V’ >> gvs[] >> Cases_on ‘h3’ >> gvs[]
           >> qpat_x_assum ‘∀j. _ ≤ j ∧ _ ⇒ _’ (qspec_then ‘LENGTH h1 + 1’ mp_tac)
           >> qpat_x_assum ‘∀i. _ ⇒ _’ (qspec_then ‘0’ mp_tac)
           >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
  >> qspecl_then [‘V’, ‘lfd’, ‘1’] mp_tac (Q.GENL [‘q’, ‘lfd’, ‘i’] sw_fresh_accepts)
  >> simp[]
QED