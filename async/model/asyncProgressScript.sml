(*
  Progress of the echo server, in the model: what the server does next,
  given what the world shows it.  These are facts about the program alone;
  asyncLivenessScript.sml combines them with the closed-loop world.

  The one assumption on the history is that the world answers promptly:
  every action gets its response in the next snapshot (`prompt`).  The
  closed-loop world does (perform_all answers every action).

   - handler_progress: if a connection stays readable for three snapshots
     in a row, its handler reads it during those rounds (unless it has seen
     end-of-file).  Three, because one cycle of the handler is: wait, read
     (one round for the response), write (one round for the response).
   - server_accept_progress: if the listener stays readable for two
     snapshots in a row, the server accepts during those rounds.
   - server_handler_view: inside the server, each accepted connection's
     handler runs on a view of the server's history that has the same
     ready sets from the round it was accepted, and the server's reads of
     that connection are exactly its handler's.
*)
Theory asyncProgress
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer asyncServerSafety
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The world answers promptly
   ------------------------------------------------------------------------ *)

(* Every action m emits is answered in the next snapshot *)
Definition prompt_def:
  prompt m h ⇔
    ∀i. i < LENGTH h ⇒
        LENGTH (new_actions (log_of m) (TAKE i h)) ≤ LENGTH (responses_at h i)
End

Theorem responses_at_APPEND[local]:
  responses_at (h1 ++ h2) (i + LENGTH h1) = responses_at h2 i
Proof
  rw[responses_at_def, EL_APPEND2]
QED

Theorem responses_at_TAKE[local]:
  i < n ⇒ responses_at (TAKE n h) i = responses_at h i
Proof
  rw[responses_at_def, EL_TAKE] >> gvs[LENGTH_TAKE_EQ] >> rw[] >> gvs[]
QED

Theorem prompt_TAKE:
  prompt m h ⇒ prompt m (TAKE n h)
Proof
  rw[prompt_def] >> gvs[LENGTH_TAKE_EQ]
  >> ‘i < n ∧ i < LENGTH h’ by (Cases_on ‘n ≤ LENGTH h’ >> gvs[])
  >> simp[TAKE_TAKE_MIN, MIN_DEF, responses_at_TAKE]
QED

Theorem prompt_map[simp]:
  prompt (map f m) h ⇔ prompt m h
Proof
  simp[prompt_def]
QED

(* After a settled m has finished, the continuation sees a prompt world *)
Theorem prompt_bind:
  wf m ∧ settled m ∧ first_done m h1 x ∧ prompt (bind m f) (h1 ++ q) ⇒
  prompt (f x) q
Proof
  rw[prompt_def]
  >> ‘new_actions (log_of m) h1 = []’ by gvs[settled_def, first_done_def]
  >> first_x_assum (qspec_then ‘i + LENGTH h1’ mp_tac)
  >> simp[responses_at_APPEND]
  >> ‘TAKE (i + LENGTH h1) (h1 ++ q) = h1 ++ TAKE i q’
       by simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
  >> simp[] >> Cases_on ‘i = 0’
  >- (gvs[] >> drule_all new_actions_bind_at
      >> disch_then (qspec_then ‘f’ SUBST1_TAC)
      >> simp[new_actions_NIL, log_of_def])
  >> ‘TAKE i q ≠ []’ by (Cases_on ‘q’ >> gvs[])
  >> qspecl_then [‘m’, ‘h1’, ‘x’, ‘TAKE i q’, ‘f’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘q’, ‘f’] new_actions_bind_after)
  >> simp[]
QED

(* Each side of both sees a prompt world *)
Theorem prompt_both:
  prompt (both m1 m2) h ⇒
  prompt m1 (left_view m1 m2 h) ∧ prompt m2 (right_view m1 m2 h)
Proof
  rw[prompt_def]
  >> gvs[left_view_def, right_view_def, LENGTH_par_views]
  >> first_x_assum drule
  >> simp[new_actions_both, GSYM left_view_def, GSYM right_view_def,
          responses_at_views, views_TAKE]
QED

(* ------------------------------------------------------------------------
   Counting reads
   ------------------------------------------------------------------------ *)

Definition nreads_def:
  nreads fd acts = LENGTH (FILTER (λa. a = Read fd) acts)
End

Theorem nreads_simps[simp]:
  nreads fd [] = 0 ∧
  nreads fd (a :: as) = (if a = Read fd then 1 else 0) + nreads fd as ∧
  nreads fd (as ++ bs) = nreads fd as + nreads fd bs
Proof
  rw[nreads_def, FILTER_APPEND_DISTRIB]
QED

Theorem nreads_prefix:
  as ≼ bs ⇒ nreads fd as ≤ nreads fd bs
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem TAKE_prefix_TAKE:
  i ≤ j ⇒ TAKE i h ≼ TAKE j h
Proof
  rw[] >> ‘TAKE i h = TAKE i (TAKE j h)’
            by (rw[TAKE_TAKE_MIN] >> ‘MIN i j = i’ by simp[MIN_DEF] >> simp[])
  >> pop_assum SUBST1_TAC >> simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]
QED

(* A well-formed computation's reads only grow along the history *)
Theorem nreads_mono:
  wf m ∧ i ≤ j ⇒ nreads fd (m (TAKE i h)).actions ≤ nreads fd (m (TAKE j h)).actions
Proof
  rw[] >> irule nreads_prefix >> irule wf_actions_grow >> simp[TAKE_prefix_TAKE]
QED

(* ------------------------------------------------------------------------
   Waiting, and emitting
   ------------------------------------------------------------------------ *)

(* h ends with the first snapshot in which fd is readable: waiting for fd
   finishes exactly after h.  (Stated at the server's types, so that the
   type of actions is fixed.) *)
Definition first_readable_def:
  first_readable fd h ⇔
    first_done (readable fd : (event, response) snapshot list ->
                              (action, unit option) outcome) h ()
End

Theorem first_readable_nonempty:
  first_readable fd h1 ⇒ h1 ≠ []
Proof
  rw[first_readable_def, first_done_def, readable_def, wait_def]
  >> strip_tac >> gvs[first_some_def]
QED

Theorem readable_not_before:
  first_readable fd h1 ∧ j + 1 < LENGTH h1 ⇒
  Readable fd ∉ (EL j h1).ready
Proof
  rw[first_readable_def, first_done_def] >> first_x_assum (qspec_then ‘j + 1’ mp_tac)
  >> simp[readable_def, wait_def] >> strip_tac
  >> ‘∀l : (event, response) snapshot list.
        first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) l = NONE ⇒
          ∀j. j < LENGTH l ⇒ Readable fd ∉ (EL j l).ready’
       by (Induct >> simp[first_some_def] >> rw[] >> Cases_on ‘j'’ >> gvs[])
  >> first_x_assum drule >> disch_then (qspec_then ‘j’ mp_tac)
  >> simp[EL_TAKE]
QED

Theorem readable_now:
  Readable fd ∈ s.ready ⇒ first_readable fd [s]
Proof
  rw[first_readable_def, first_done_def, readable_def, wait_def, first_some_def]
QED

(* If fd is readable somewhere in h, waiting for it finishes in h *)
Theorem readable_split:
  j < LENGTH h ∧ Readable fd ∈ (EL j h).ready ⇒
  ∃h1 h2. h = h1 ++ h2 ∧ first_readable fd h1 ∧ LENGTH h1 ≤ j + 1
Proof
  strip_tac
  >> qspecl_then [‘readable fd : (event, response) snapshot list ->
                                 (action, unit option) outcome’, ‘h’]
       strip_assume_tac history_split
  >- (first_x_assum (qspec_then ‘j + 1’ mp_tac)
      >> simp[readable_def, wait_def]
      >> ‘∀(l : (event, response) snapshot list) j.
            j < LENGTH l ∧ Readable fd ∈ (EL j l).ready ⇒
                first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) l ≠ NONE’
           by (Induct >> simp[first_some_def] >> rw[] >> Cases_on ‘j'’ >> gvs[]
               >> metis_tac[])
      >> strip_tac >> first_x_assum (qspecl_then [‘TAKE (j + 1) h’, ‘j’] mp_tac)
      >> simp[EL_TAKE])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[]
  >> qexistsl_tac [‘h1’, ‘h2’] >> simp[first_readable_def]
  >> CCONTR_TAC >> gvs[NOT_LESS_EQUAL]
  >> ‘first_readable fd h1’ by simp[first_readable_def]
  >> drule readable_not_before >> disch_then (qspec_then ‘j’ mp_tac)
  >> gvs[EL_APPEND1]
QED

(* bind (emit a) f: emits a first, then (with the response r) runs f r *)
Theorem bind_emit_NIL:
  bind (emit a) f [] = <| actions := [a]; result := NONE |>
Proof
  simp[bind_def, first_prefix_def, emit_def]
QED

Theorem bind_emit_CONS:
  oHD s.results = SOME r ⇒
  bind (emit a) f (s :: q) = <| actions := a :: (f r q).actions; result := (f r q).result |>
Proof
  strip_tac
  >> ‘first_done (emit a) [s] r’ by simp[first_done_def, emit_def]
  >> drule_then (qspecl_then [‘f’, ‘q’] mp_tac) bind_continues
  >> simp[new_actions_def, log_of_def, emit_def]
QED

Theorem bind_emit_starts:
  ∃rest. (bind (emit a) f q).actions = a :: rest
Proof
  Cases_on ‘q’ >> simp[bind_emit_NIL] >> Cases_on ‘oHD h.results’
  >- (‘bind (emit a) f (h::t) =
       <|actions := (emit a (h::t)).actions; result := NONE|>’
        by (irule bind_running >> Cases >> simp[emit_def])
      >> simp[emit_def])
  (* (not via bind_emit_CONS: its type variables would clash with the goal's) *)
  >> ‘first_done (emit a) [h] x’ by simp[first_done_def, emit_def]
  >> drule_then (qspecl_then [‘f’, ‘t’] mp_tac) bind_continues
  >> simp[new_actions_def, log_of_def, emit_def]
QED

(* ------------------------------------------------------------------------
   One connection: the handler, step by step
   ------------------------------------------------------------------------ *)

(* What the handler does with the response to its read *)
Definition after_read_def:
  after_read fd res =
    case res of
      Data d => bind (emit (Write fd d)) (λw. handler fd)
    | Eof => return ()
    | _ => handler fd
End

Theorem handler_steps:
  handler fd = bind (readable fd) (λu. bind (emit (Read fd)) (after_read fd))
Proof
  simp[Once handler_unfold, handler_body_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC
  >> simp[FUN_EQ_THM] >> Cases >> simp[after_read_def]
QED

(* Until fd is readable, the handler does nothing *)
Theorem handler_waiting:
  first_readable fd h1 ∧ n < LENGTH h1 ⇒
  (handler fd (TAKE n h1)).actions = []
Proof
  rw[] >> ONCE_REWRITE_TAC[handler_steps]
  >> ‘bind (readable fd) (λu. bind (emit (Read fd)) (after_read fd)) (TAKE n h1) =
      <|actions := (readable fd (TAKE n h1)).actions; result := NONE|>’
       by (irule bind_before_first_done >> gvs[first_readable_def] >> metis_tac[])
  >> simp[readable_def, wait_def]
QED

(* Once fd is readable, the handler reads it *)
Theorem handler_reads:
  first_readable fd h1 ⇒
  handler fd (h1 ++ q) = bind (emit (Read fd)) (after_read fd) q
Proof
  rw[first_readable_def] >> ONCE_REWRITE_TAC[handler_steps]
  >> drule_then (qspecl_then [‘λu. bind (emit (Read fd)) (after_read fd)’, ‘q’]
                 mp_tac) bind_continues
  >> simp[new_actions_def, log_of_def, readable_def, wait_def]
  >> simp[outcome_component_equality]
QED

Theorem handler_new_read:
  first_readable fd h1 ⇒
  new_actions (log_of (handler fd)) h1 = [Read fd]
Proof
  rw[] >> drule first_readable_nonempty >> strip_tac
  >> ‘(handler fd h1).actions = [Read fd]’
       by (drule_then (qspec_then ‘[]’ mp_tac) handler_reads >> simp[bind_emit_NIL])
  >> ‘(handler fd (FRONT h1)).actions = []’
       by (‘FRONT h1 = TAKE (LENGTH h1 - 1) h1’ by simp[FRONT_BY_TAKE]
           >> simp[] >> irule handler_waiting >> simp[]
           >> Cases_on ‘h1’ >> gvs[])
  >> simp[new_actions_def, log_of_def]
QED

(* A fresh handler, on a history whose first snapshot has fd readable,
   reads fd straight away *)
Theorem handler_fresh_reads:
  q ≠ [] ∧ Readable fd ∈ (HD q).ready ∧ 1 ≤ i ⇒
  1 ≤ nreads fd (handler fd (TAKE i q)).actions
Proof
  Cases_on ‘q’ >> rw[]
  >> drule readable_now >> strip_tac
  >> ‘TAKE i (h::t) = [h] ++ TAKE (i - 1) t’ by (Cases_on ‘i’ >> gvs[])
  >> drule_then (qspec_then ‘TAKE (i - 1) t’ mp_tac) handler_reads
  >> simp[] >> strip_tac
  >> qspecl_then [‘Read fd’, ‘after_read fd’, ‘TAKE (i - 1) t’] strip_assume_tac
       (Q.GENL [‘a’, ‘f’, ‘q’] bind_emit_starts)
  >> simp[]
QED

Theorem first_done_emit_SOME:
  oHD s.results = SOME r ⇒ first_done (emit a) [s] r
Proof
  simp[first_done_def, emit_def]
QED

(* The read's response r arrives in s: the handler continues with r *)
Theorem handler_after_read:
  first_readable fd h1 ∧ oHD s.results = SOME r ⇒
  (handler fd (h1 ++ s :: q)).actions = Read fd :: (after_read fd r q).actions
Proof
  rpt strip_tac >> drule_then (qspec_then ‘s :: q’ SUBST1_TAC) handler_reads
  >> qspecl_then [‘s’, ‘r’, ‘Read fd’, ‘after_read fd’, ‘q’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS)
  >> simp[]
QED

Theorem after_read_data_NIL:
  (after_read fd (Data d) []).actions = [Write fd d]
Proof
  simp[after_read_def, bind_emit_NIL]
QED

Theorem after_read_data_CONS:
  oHD s.results = SOME r ⇒
  (after_read fd (Data d) (s :: q)).actions = Write fd d :: (handler fd q).actions
Proof
  strip_tac >> simp[after_read_def]
  >> qspecl_then [‘s’, ‘r’, ‘Write fd d’, ‘λw. handler fd’, ‘q’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS)
  >> simp[]
QED

Theorem after_read_other:
  r ≠ Eof ∧ (∀d. r ≠ Data d) ⇒ after_read fd r = handler fd
Proof
  Cases_on ‘r’ >> simp[after_read_def]
QED

(* The handler's transcript, step by step *)
Theorem handler_trans_read:
  first_readable fd h1 ∧ oHD s.results = SOME r ⇒
  trans (handler fd) (h1 ++ s :: q) =
    (Read fd, SOME r) :: trans (after_read fd r) q
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[handler_steps]
  >> qspecl_then [‘readable fd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Read fd)) (after_read fd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> disch_then kall_tac
  >> qspecl_then [‘emit (Read fd)’, ‘[s]’, ‘r’, ‘after_read fd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME, trans_emit, readable_def]
QED

Theorem after_read_trans_data:
  oHD s.results = SOME r ⇒
  trans (after_read fd (Data d)) (s :: q) =
    (Write fd d, SOME r) :: trans (handler fd) q
Proof
  strip_tac >> simp[after_read_def]
  >> qspecl_then [‘emit (Write fd d)’, ‘[s]’, ‘r’, ‘λw. handler fd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME, trans_emit]
QED

Theorem handler_new_write:
  first_readable fd h1 ∧ oHD s.results = SOME (Data d) ⇒
  new_actions (log_of (handler fd)) (h1 ++ [s]) = [Write fd d]
Proof
  strip_tac
  >> ‘(handler fd h1).actions = [Read fd]’
       by (drule_then (qspec_then ‘[]’ mp_tac) handler_reads >> simp[bind_emit_NIL])
  >> drule_all handler_after_read >> disch_then (qspec_then ‘[]’ mp_tac)
  >> simp[new_actions_SNOC, log_of_def, after_read_data_NIL]
QED

(* After each step, the rest of the handler still sees a prompt world *)
Theorem prompt_after_read:
  prompt (handler fd) (h1 ++ s :: q) ∧ first_readable fd h1 ∧
  oHD s.results = SOME r ⇒
  prompt (after_read fd r) q
Proof
  rpt strip_tac
  >> qpat_x_assum ‘prompt _ _’ (mp_tac o ONCE_REWRITE_RULE[handler_steps])
  >> strip_tac
  >> qspecl_then [‘readable fd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Read fd)) (after_read fd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> strip_tac
  >> qspecl_then [‘emit (Read fd)’, ‘[s]’, ‘r’, ‘after_read fd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME]
QED

Theorem prompt_after_write:
  prompt (after_read fd (Data d)) (s :: q) ∧ oHD s.results = SOME r ⇒
  prompt (handler fd) q
Proof
  rpt strip_tac
  >> qspecl_then [‘emit (Write fd d)’, ‘[s]’, ‘r’, ‘λw. handler fd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> gvs[wf_emit, settled_emit, first_done_emit_SOME, after_read_def]
QED

(* With a prompt world, the response to the read is there *)
Theorem prompt_read_answered:
  prompt (handler fd) (h1 ++ s :: q) ∧ first_readable fd h1 ⇒
  ∃r. oHD s.results = SOME r
Proof
  rw[prompt_def] >> first_x_assum (qspec_then ‘LENGTH h1’ mp_tac)
  >> simp[TAKE_LENGTH_APPEND, responses_at_def, EL_APPEND2]
  >> drule handler_new_read >> simp[]
  >> Cases_on ‘s.results’ >> simp[]
QED

Theorem prompt_write_answered:
  prompt (handler fd) (h1 ++ s :: s' :: q) ∧ first_readable fd h1 ∧
  oHD s.results = SOME (Data d) ⇒
  ∃r. oHD s'.results = SOME r
Proof
  rw[prompt_def] >> first_x_assum (qspec_then ‘LENGTH h1 + 1’ mp_tac)
  >> ‘TAKE (LENGTH h1 + 1) (h1 ++ s :: s' :: q) = h1 ++ [s]’
       by simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
  >> simp[responses_at_def, EL_APPEND2]
  >> drule_all handler_new_write >> simp[]
  >> Cases_on ‘s'.results’ >> simp[]
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

(* MAIN: progress of one connection.  If fd is readable in three snapshots
   in a row (k, k+1, k+2), and the world answers promptly, then the handler
   reads fd during those rounds, unless it has already seen end-of-file. *)
Theorem handler_progress:
  ∀g k. prompt (handler fd) g ∧ k + 3 ≤ LENGTH g ∧
        (∀j. k ≤ j ∧ j < k + 3 ⇒ Readable fd ∈ (EL j g).ready) ∧
        ¬MEM (Read fd, SOME Eof) (trans (handler fd) g) ⇒
        nreads fd (handler fd (TAKE k g)).actions <
        nreads fd (handler fd (TAKE (k + 3) g)).actions
Proof
  gen_tac >> measureInduct_on ‘LENGTH g’ >> rpt strip_tac
  (* the handler's first wait ends at the latest in snapshot k *)
  >> qspecl_then [‘k’, ‘g’, ‘fd’] mp_tac (Q.GENL [‘j’, ‘h’, ‘fd’] readable_split)
  >> simp[] >> strip_tac >> gvs[]
  >> Cases_on ‘LENGTH h1 = k + 1’
  (* it ends in snapshot k: the first read is in round k *)
  >- (‘(handler fd (TAKE k (h1 ++ h2))).actions = []’
        by simp[TAKE_before, handler_waiting]
      >> simp[TAKE_after] >> drule_then (qspec_then ‘TAKE 2 h2’ SUBST1_TAC) handler_reads
      >> qspecl_then [‘Read fd’, ‘after_read fd’, ‘TAKE 2 h2’] strip_assume_tac
           (Q.GENL [‘a’, ‘f’, ‘q’] bind_emit_starts)
      >> simp[])
  (* it ends earlier: the handler reads, and the response r arrives in s1 *)
  >> ‘LENGTH h1 ≤ k’ by simp[] >> Cases_on ‘h2’ >- gvs[] >> rename1 ‘h1 ++ s1 :: h3’
  >> drule_all prompt_read_answered >> strip_tac
  >> ‘∀i. LENGTH h1 + 1 ≤ i ⇒
          nreads fd (handler fd (TAKE i (h1 ++ s1 :: h3))).actions =
          1 + nreads fd (after_read fd r (TAKE (i - LENGTH h1 - 1) h3)).actions’
       by (rpt strip_tac >> simp[TAKE_after]
           >> ‘TAKE (i − LENGTH h1) (s1::h3) = s1 :: TAKE (i - LENGTH h1 - 1) h3’
                by (Cases_on ‘i - LENGTH h1’ >> gvs[])
           >> drule_all handler_after_read
           >> disch_then (qspec_then ‘TAKE (i − (LENGTH h1 + 1)) h3’
                (fn th => REWRITE_TAC[REWRITE_RULE[GSYM APPEND_ASSOC, APPEND] th]))
           >> simp[])
  >> ‘nreads fd (handler fd (TAKE (LENGTH h1) (h1 ++ s1 :: h3))).actions = 1’
       by (simp[TAKE_LENGTH_APPEND] >> ‘h1 = h1 ++ []’ by simp[]
           >> pop_assum SUBST1_TAC >> drule handler_reads >> simp[bind_emit_NIL])
  >> ‘r ≠ Eof’
       by (strip_tac >> gvs[] >> drule_all handler_trans_read
           >> disch_then (qspec_then ‘h3’
                (fn th => gvs[REWRITE_RULE[GSYM APPEND_ASSOC, APPEND] th])))
  >> ‘trans (handler fd) (h1 ++ s1 :: h3) =
      (Read fd, SOME r) :: trans (after_read fd r) h3’
       by (drule_all handler_trans_read
           >> disch_then (qspec_then ‘h3’
                (fn th => REWRITE_TAC[REWRITE_RULE[GSYM APPEND_ASSOC, APPEND] th])))
  >> Cases_on ‘∃d. r = Data d’
  (* data d: the handler writes it back (response r2 in s2), then starts again *)
  >- (pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC
      >> Cases_on ‘h3’ >- gvs[] >> rename1 ‘s1 :: s2 :: h4’
      >> drule_all prompt_write_answered >> strip_tac
      >> rename1 ‘oHD s2.results = SOME r2’
      >> ‘∀i. LENGTH h1 + 2 ≤ i ⇒
              nreads fd (handler fd (TAKE i (h1 ++ s1 :: s2 :: h4))).actions =
              1 + nreads fd (handler fd (TAKE (i - LENGTH h1 - 2) h4)).actions’
           by (rpt strip_tac >> qpat_x_assum ‘∀i. _ ≤ i ⇒ _’ (qspec_then ‘i’ mp_tac)
               >> simp[]
               >> qspecl_then [‘s2’, ‘r2’, ‘fd’, ‘d’, ‘TAKE (i − (LENGTH h1 + 2)) h4’]
                    mp_tac (Q.GENL [‘s’, ‘r’, ‘fd’, ‘d’, ‘q’] after_read_data_CONS)
               >> simp[])
      >> ‘nreads fd (handler fd (TAKE (LENGTH h1 + 1) (h1 ++ s1 :: s2 :: h4))).actions = 1’
           by (qpat_x_assum ‘∀i. LENGTH h1 + 1 ≤ i ⇒ _’ (qspec_then ‘LENGTH h1 + 1’ mp_tac)
               >> simp[after_read_data_NIL])
      >> ‘¬MEM (Read fd, SOME Eof) (trans (handler fd) h4)’
           by (qspecl_then [‘s2’, ‘r2’, ‘fd’, ‘d’, ‘h4’] mp_tac
                 (Q.GENL [‘s’, ‘r’, ‘fd’, ‘d’, ‘q’] after_read_trans_data)
               >> simp[] >> strip_tac >> gvs[])
      >> Cases_on ‘LENGTH h1 + 2 ≤ k’
      (* the window starts after the restart: by induction *)
      >- (first_x_assum (qspec_then ‘h4’ mp_tac) >> simp[]
          >> disch_then (qspec_then ‘k - LENGTH h1 - 2’ mp_tac)
          >> impl_tac
          >- (rpt conj_tac
              >- (drule_all prompt_after_read >> strip_tac
                  >> irule prompt_after_write >> metis_tac[])
              >- gvs[]
              >> rpt strip_tac
              >> qpat_x_assum ‘∀j. k ≤ j ∧ _ ⇒ _’ (qspec_then ‘j + LENGTH h1 + 2’ mp_tac)
              >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
          >> simp[])
      (* the restart is in the window: the restarted handler reads at once *)
      >> ‘nreads fd (handler fd (TAKE k (h1 ++ s1 :: s2 :: h4))).actions = 1’
           by (Cases_on ‘k = LENGTH h1’ >> gvs[] >> ‘k = LENGTH h1 + 1’ by simp[] >> gvs[])
      >> qpat_x_assum ‘∀i. LENGTH h1 + 2 ≤ i ⇒ _’ (qspec_then ‘k + 3’ mp_tac)
      >> simp[] >> strip_tac
      >> ‘h4 ≠ [] ∧ Readable fd ∈ (HD h4).ready’
           by (Cases_on ‘h4’ >> gvs[]
               >> qpat_x_assum ‘∀j. k ≤ j ∧ _ ⇒ _’ (qspec_then ‘LENGTH h1 + 2’ mp_tac)
               >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
      >> qspecl_then [‘h4’, ‘fd’, ‘k + 1 − LENGTH h1’] mp_tac
           (Q.GENL [‘q’, ‘fd’, ‘i’] handler_fresh_reads)
      >> simp[])
  (* any other response: the handler starts again at once *)
  >> ‘after_read fd r = handler fd’ by (irule after_read_other >> gvs[]) >> gvs[]
  >> Cases_on ‘LENGTH h1 + 1 ≤ k’
  (* the window starts after the restart: by induction *)
  >- (first_x_assum (qspec_then ‘h3’ mp_tac) >> simp[]
      >> disch_then (qspec_then ‘k - LENGTH h1 - 1’ mp_tac)
      >> impl_tac
      >- (rpt conj_tac
          >- (drule_all prompt_after_read >> simp[])
          >- simp[]
          >> rpt strip_tac
          >> ‘EL j h3 = EL (j + LENGTH h1 + 1) (h1 ++ s1 :: h3)’
               by simp[EL_APPEND2, EL_CONS, PRE_SUB1]
          >> simp[])
      >> ‘k − LENGTH h1 − 1 + 3 = k + 2 − LENGTH h1 ∧
          k − LENGTH h1 − 1 = k − (LENGTH h1 + 1)’ by simp[]
      >> simp[])
  (* the restart is in the window *)
  >> ‘k = LENGTH h1’ by simp[] >> gvs[]
  >> ‘h3 ≠ [] ∧ Readable fd ∈ (HD h3).ready’
       by (Cases_on ‘h3’ >> gvs[]
           >> qpat_x_assum ‘∀j. _ ≤ j ∧ _ ⇒ _’ (qspec_then ‘LENGTH h1 + 1’ mp_tac)
           >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
  >> qspecl_then [‘h3’, ‘fd’, ‘2’] mp_tac (Q.GENL [‘q’, ‘fd’, ‘i’] handler_fresh_reads)
  >> simp[]
QED

(* ------------------------------------------------------------------------
   Counting actions through both
   ------------------------------------------------------------------------ *)

(* How many actions satisfy P *)
Definition count_def:
  count P acts = LENGTH (FILTER P acts)
End

Theorem count_FLAT_GENLIST_APPEND[local]:
  ∀k. count P (FLAT (GENLIST (λn. f n ++ g n) k)) =
      count P (FLAT (GENLIST f k)) + count P (FLAT (GENLIST g k))
Proof
  Induct >> gvs[count_def, GENLIST, SNOC_APPEND, FILTER_APPEND_DISTRIB]
QED

Theorem count_MAP_FST[local]:
  count P (MAP FST l) = count (P o FST) l
Proof
  simp[count_def, rich_listTheory.FILTER_MAP]
QED

(* Each action of both is the left side's or the right side's *)
Theorem count_both:
  wf m1 ∧ wf m2 ⇒
  count P (both m1 m2 h).actions =
    count P (m1 (left_view m1 m2 h)).actions +
    count P (m2 (right_view m1 m2 h)).actions
Proof
  strip_tac
  >> ‘(both m1 m2 h).actions = MAP FST (trans (both m1 m2) h) ∧
      (m1 (left_view m1 m2 h)).actions = MAP FST (trans m1 (left_view m1 m2 h)) ∧
      (m2 (right_view m1 m2 h)).actions = MAP FST (trans m2 (right_view m1 m2 h))’
       by simp[MAP_FST_trans, wf_both]
  >> ASM_REWRITE_TAC[] >> simp[count_MAP_FST, trans_def]
  >> ‘GENLIST (round_trans (both m1 m2) h) (SUC (LENGTH h)) =
      GENLIST (λn. round_trans m1 (left_view m1 m2 h) n ++
                   round_trans m2 (right_view m1 m2 h) n) (SUC (LENGTH h))’
       by simp[GENLIST_FUN_EQ, round_trans_both]
  >> ASM_REWRITE_TAC[count_FLAT_GENLIST_APPEND] >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >> simp[left_view_def, right_view_def, LENGTH_par_views]
QED

Theorem nreads_count:
  nreads fd acts = count (λa. a = Read fd) acts
Proof
  simp[nreads_def, count_def]
QED

Theorem count_prefix:
  as ≼ bs ∧ count P bs = 0 ⇒ count P as = 0
Proof
  rw[IS_PREFIX_APPEND] >> gvs[count_def, FILTER_APPEND_DISTRIB]
QED

(* A connection's handler only acts on its own fd, and never accepts *)
Theorem handler_actions_own:
  MEM a (handler fd h).actions ⇒ a = Read fd ∨ ∃d. a = Write fd d
Proof
  qspecl_then [‘fd’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes)
  >> ‘MAP FST (trans (handler fd) h) = (handler fd h).actions’
       by simp[MAP_FST_trans, wf_handler]
  >> rw[EVERY_MEM]
  >> qpat_x_assum ‘MEM a _’ mp_tac
  >> qpat_x_assum ‘MAP FST _ = _’ (SUBST1_TAC o GSYM) >> rw[MEM_MAP]
  >> first_x_assum drule >> PairCases_on ‘y’ >> simp[on_fd_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The server, step by step
   ------------------------------------------------------------------------ *)

(* What the server does with the response to its accept *)
Definition after_accept_def:
  after_accept lfd res =
    case res of
      Accepted fd => map (λp. ()) (both (handler fd) (server lfd))
    | _ => server lfd
End

Theorem server_steps:
  server lfd = bind (readable lfd) (λu. bind (emit (Accept lfd)) (after_accept lfd))
Proof
  simp[Once server_unfold]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC
  >> simp[FUN_EQ_THM] >> Cases >> simp[after_accept_def]
QED

(* Until the listener is readable, the server has accepted nothing *)
Theorem server_waiting:
  first_readable lfd h1 ∧ m ≤ LENGTH h1 ⇒
  accepted (trans (server lfd) (TAKE m h1)) = []
Proof
  rw[] >> ONCE_REWRITE_TAC[server_steps] >> Cases_on ‘m < LENGTH h1’
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
                  ‘λu. bind (emit (Accept lfd)) (after_accept lfd)’, ‘[]’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[readable_def]
  >> ‘trans (bind (emit (Accept lfd)) (after_accept lfd)) [] =
      trans (emit (Accept lfd)) ([] : (event, response) snapshot list)’
       by (irule trans_bind_running >> simp[emit_def])
  >> simp[trans_emit]
QED

(* Once the listener is readable, the server accepts *)
Theorem server_accepts:
  first_readable lfd h1 ⇒
  server lfd (h1 ++ q) = bind (emit (Accept lfd)) (after_accept lfd) q
Proof
  rw[first_readable_def] >> ONCE_REWRITE_TAC[server_steps]
  >> drule_then (qspecl_then [‘λu. bind (emit (Accept lfd)) (after_accept lfd)’, ‘q’]
                 mp_tac) bind_continues
  >> simp[new_actions_def, log_of_def, readable_def, wait_def]
  >> simp[outcome_component_equality]
QED

Theorem server_waiting_actions:
  first_readable lfd h1 ∧ n < LENGTH h1 ⇒
  (server lfd (TAKE n h1)).actions = []
Proof
  rw[] >> ONCE_REWRITE_TAC[server_steps]
  >> ‘bind (readable lfd) (λu. bind (emit (Accept lfd)) (after_accept lfd)) (TAKE n h1) =
      <|actions := (readable lfd (TAKE n h1)).actions; result := NONE|>’
       by (irule bind_before_first_done >> gvs[first_readable_def] >> metis_tac[])
  >> simp[readable_def, wait_def]
QED

Theorem server_new_accept:
  first_readable lfd h1 ⇒
  new_actions (log_of (server lfd)) h1 = [Accept lfd]
Proof
  rw[] >> drule first_readable_nonempty >> strip_tac
  >> ‘(server lfd h1).actions = [Accept lfd]’
       by (drule_then (qspec_then ‘[]’ mp_tac) server_accepts >> simp[bind_emit_NIL])
  >> ‘(server lfd (FRONT h1)).actions = []’
       by (‘FRONT h1 = TAKE (LENGTH h1 - 1) h1’ by simp[FRONT_BY_TAKE]
           >> simp[] >> irule server_waiting_actions >> simp[]
           >> Cases_on ‘h1’ >> gvs[])
  >> simp[new_actions_def, log_of_def]
QED

(* The accept's response r arrives in s: the server continues with r *)
Theorem server_after_accept:
  first_readable lfd h1 ∧ oHD s.results = SOME r ⇒
  (server lfd (h1 ++ [s] ++ q)).actions = Accept lfd :: (after_accept lfd r q).actions
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >> drule_then (qspec_then ‘s :: q’ SUBST1_TAC) server_accepts
  >> qspecl_then [‘s’, ‘r’, ‘Accept lfd’, ‘after_accept lfd’, ‘q’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS)
  >> simp[]
QED

Theorem server_trans_accept:
  first_readable lfd h1 ∧ oHD s.results = SOME r ⇒
  trans (server lfd) (h1 ++ [s] ++ q) =
    (Accept lfd, SOME r) :: trans (after_accept lfd r) q
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >> ONCE_REWRITE_TAC[server_steps]
  >> qspecl_then [‘readable lfd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Accept lfd)) (after_accept lfd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> disch_then kall_tac
  >> qspecl_then [‘emit (Accept lfd)’, ‘[s]’, ‘r’, ‘after_accept lfd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME, trans_emit, readable_def]
QED

Theorem prompt_after_accept:
  prompt (server lfd) (h1 ++ [s] ++ q) ∧ first_readable lfd h1 ∧
  oHD s.results = SOME r ⇒
  prompt (after_accept lfd r) q
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac
  >> qpat_x_assum ‘prompt _ _’ (mp_tac o ONCE_REWRITE_RULE[server_steps])
  >> strip_tac
  >> qspecl_then [‘readable lfd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Accept lfd)) (after_accept lfd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> strip_tac
  >> qspecl_then [‘emit (Accept lfd)’, ‘[s]’, ‘r’, ‘after_accept lfd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME]
QED

Theorem prompt_accept_answered:
  prompt (server lfd) (h1 ++ [s] ++ q) ∧ first_readable lfd h1 ⇒
  ∃r. oHD s.results = SOME r
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rw[prompt_def] >> first_x_assum (qspec_then ‘LENGTH h1’ mp_tac)
  >> simp[TAKE_LENGTH_APPEND, responses_at_def, EL_APPEND2]
  >> drule server_new_accept >> simp[]
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
Theorem views_ready:
  i < LENGTH q ⇒
  (EL i (left_view (handler c) (server lfd) q)).ready = (EL i q).ready ∧
  (EL i (right_view (handler c) (server lfd) q)).ready = (EL i q).ready
Proof
  strip_tac
  >> qspecl_then [‘log_of (handler c)’, ‘log_of (server lfd)’, ‘q’] mp_tac
       (Q.GENL [‘a1’, ‘a2’] par_views_world)
  >> rw[left_view_def, right_view_def]
  >> qpat_x_assum ‘MAP _ (FST _) = _’ (mp_tac o Q.AP_TERM ‘EL i’)
  >> qpat_x_assum ‘MAP _ (SND _) = _’ (mp_tac o Q.AP_TERM ‘EL i’)
  >> simp[EL_MAP, LENGTH_par_views]
QED

Theorem LENGTH_views[simp]:
  LENGTH (left_view m1 m2 q) = LENGTH q ∧ LENGTH (right_view m1 m2 q) = LENGTH q
Proof
  simp[left_view_def, right_view_def, LENGTH_par_views]
QED

Theorem handler_no_accepts[local]:
  FILTER is_accept (trans (handler c) h) = []
Proof
  qspecl_then [‘c’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes)
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> PairCases_on ‘x’ >> gvs[on_fd_def, is_accept_def]
QED

(* The connections accepted alongside a handler are the rest of the server's *)
Theorem accepted_both:
  accepted (trans (both (handler c) (server lfd)) q) =
  accepted (trans (server lfd) (right_view (handler c) (server lfd) q))
Proof
  ONCE_REWRITE_TAC[GSYM accepted_FILTER] >> AP_TERM_TAC
  >> irule trans_both_filter_right >> simp[handler_no_accepts]
QED

(* Another connection's actions alongside a handler are the rest of the
   server's *)
Theorem filter_both_other:
  fd ≠ c ⇒
  FILTER (on_fd fd) (trans (both (handler c) (server lfd)) q) =
  FILTER (on_fd fd) (trans (server lfd) (right_view (handler c) (server lfd) q))
Proof
  strip_tac >> irule trans_both_filter_right
  >> qspecl_then [‘c’, ‘left_view (handler c) (server lfd) q’] mp_tac
       (Q.GEN ‘fd’ handler_echoes)
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> PairCases_on ‘x’ >> gvs[on_fd_def] >> metis_tac[]
QED

(* The connection's own actions alongside its handler are the handler's,
   if the rest of the server never touches it *)
Theorem filter_both_own:
  FILTER (on_fd c) (trans (server lfd) (right_view (handler c) (server lfd) q)) = [] ⇒
  FILTER (on_fd c) (trans (both (handler c) (server lfd)) q) =
  trans (handler c) (left_view (handler c) (server lfd) q)
Proof
  strip_tac >> drule trans_both_filter_left >> simp[]
  >> disch_then kall_tac >> simp[FILTER_EQ_ID]
  >> qspecl_then [‘c’, ‘left_view (handler c) (server lfd) q’] mp_tac
       (Q.GEN ‘fd’ handler_echoes)
  >> simp[]
QED

Theorem nreads_both:
  nreads fd (both (handler c) (server lfd) q).actions =
  nreads fd (handler c (left_view (handler c) (server lfd) q)).actions +
  nreads fd (server lfd (right_view (handler c) (server lfd) q)).actions
Proof
  simp[nreads_count] >> irule count_both >> simp[wf_handler, wf_server]
QED

Theorem nreads_handler_other:
  fd ≠ c ⇒ nreads fd (handler c h).actions = 0
Proof
  rw[nreads_def, FILTER_EQ_NIL, EVERY_MEM] >> strip_tac
  >> drule handler_actions_own >> simp[]
QED

(* If the server never touches c, none of its prefixes reads c *)
Theorem nreads_server_untouched:
  ¬EXISTS (on_fd c) (trans (server lfd) R) ⇒
  nreads c (server lfd (TAKE j R)).actions = 0
Proof
  rw[nreads_count] >> irule count_prefix
  >> qexists_tac ‘(server lfd R).actions’
  >> reverse conj_tac
  >- (irule wf_actions_grow >> simp[wf_server, IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP])
  >> ‘MAP FST (trans (server lfd) R) = (server lfd R).actions’
       by simp[MAP_FST_trans, wf_server]
  >> pop_assum (SUBST1_TAC o GSYM)
  >> gvs[count_def, FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, EXISTS_MEM]
  >> rpt strip_tac >> first_x_assum drule >> PairCases_on ‘y’ >> gvs[on_fd_def]
QED

(* If the server has accepted something, it waited for the listener (h1),
   accepted, and got the response r (in s) *)
Theorem server_split:
  prompt (server lfd) h ∧ accepted (trans (server lfd) h) ≠ [] ⇒
  ∃h1 s h3 r. h = h1 ++ [s] ++ h3 ∧ first_readable lfd h1 ∧ oHD s.results = SOME r
Proof
  strip_tac
  >> qspecl_then [‘readable lfd : (event, response) snapshot list ->
                                  (action, unit option) outcome’, ‘h’]
       strip_assume_tac history_split
  >- (‘trans (server lfd) h = trans (readable lfd) h’
        by (ONCE_REWRITE_TAC[server_steps] >> irule trans_bind_running >> simp[])
      >> qpat_x_assum ‘trans _ _ = trans _ _’ mp_tac
      >> simp[readable_def] >> strip_tac >> gvs[])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[]
  >> ‘first_readable lfd h1’ by simp[first_readable_def]
  >> Cases_on ‘h2’
  >- (drule_then (qspec_then ‘LENGTH h1’ mp_tac) server_waiting >> gvs[])
  >> qspecl_then [‘lfd’, ‘h1’, ‘h’, ‘t’] mp_tac
       (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘q’] prompt_accept_answered)
  >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[] >> strip_tac
  >> qexistsl_tac [‘h1’, ‘h’, ‘t’, ‘r’] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
  >> simp[]
QED

(* MAIN: inside the server, each accepted connection fd is served by its own
   handler, running on a view g of the server's history from the round a in
   which fd was accepted: g has the same ready sets, the world answers the
   handler promptly, the handler's transcript is the server's transcript
   restricted to fd, and the server's reads of fd are the handler's. *)
Theorem server_handler_view:
  ∀h. fresh (trans (server lfd) h) ∧ prompt (server lfd) h ∧
      MEM fd (accepted (trans (server lfd) h)) ⇒
      ∃a g. LENGTH g + a = LENGTH h ∧
            (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) h).ready) ∧
            prompt (handler fd) g ∧
            FILTER (on_fd fd) (trans (server lfd) h) = trans (handler fd) g ∧
            (∀j. j ≤ LENGTH g ⇒
                 nreads fd (server lfd (TAKE (a + j) h)).actions =
                 nreads fd (handler fd (TAKE j g)).actions) ∧
            (∀m. m ≤ LENGTH h ∧ MEM fd (accepted (trans (server lfd) (TAKE m h))) ⇒
                 a ≤ m)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt strip_tac
  (* the server waited (h1), accepted, and got the response r (in s) *)
  >> ‘accepted (trans (server lfd) h) ≠ []’ by (strip_tac >> gvs[])
  >> drule_all server_split >> strip_tac >> gvs[]
  >> ‘∀m. LENGTH h1 + 1 ≤ m ⇒
          trans (server lfd) (TAKE m (h1 ++ [s] ++ h3)) =
            (Accept lfd, SOME r) ::
            trans (after_accept lfd r) (TAKE (m − LENGTH h1 − 1) h3) ∧
          (server lfd (TAKE m (h1 ++ [s] ++ h3))).actions =
            Accept lfd :: (after_accept lfd r (TAKE (m − LENGTH h1 − 1) h3)).actions’
       by (rpt strip_tac >> simp[TAKE_after_cons]
           >> qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘TAKE (m − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] server_trans_accept)
           >> qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘TAKE (m − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] server_after_accept)
           >> simp[])
  >> ‘trans (server lfd) (h1 ++ [s] ++ h3) =
      (Accept lfd, SOME r) :: trans (after_accept lfd r) h3’
       by (qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘h3’] mp_tac
             (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] server_trans_accept) >> simp[])
  >> ‘∀m. m ≤ LENGTH h1 ⇒ accepted (trans (server lfd) (TAKE m (h1 ++ [s] ++ h3))) = []’
       by (rpt strip_tac >> ‘TAKE m (h1 ++ [s] ++ h3) = TAKE m h1’ by simp[TAKE_APPEND1]
           >> simp[] >> irule server_waiting >> simp[])
  >> drule_all prompt_after_accept >> strip_tac
  >> Cases_on ‘∃c. r = Accepted c’
  (* a new connection c: its handler runs on L, the rest of the server on R *)
  >- (pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC
      >> qabbrev_tac ‘L = left_view (handler c) (server lfd) h3’
      >> qabbrev_tac ‘R = right_view (handler c) (server lfd) h3’
      >> ‘∀q. trans (after_accept lfd (Accepted c)) q =
              trans (both (handler c) (server lfd)) q ∧
              (after_accept lfd (Accepted c) q).actions =
              (both (handler c) (server lfd) q).actions’
           by simp[after_accept_def, map_def]
      >> ‘accepted (trans (server lfd) (h1 ++ [s] ++ h3)) =
          c :: accepted (trans (server lfd) R)’
           by simp[accepted_both, Abbr ‘R’]
      >> ‘¬MEM c (accepted (trans (server lfd) R)) ∧ fresh (trans (server lfd) R)’
           by gvs[fresh_def]
      >> ‘prompt (handler c) L ∧ prompt (server lfd) R’
           by (gvs[after_accept_def] >> drule prompt_both >> simp[Abbr ‘L’, Abbr ‘R’])
      (* the rest of the server never touches c *)
      >> ‘¬EXISTS (on_fd c) (trans (server lfd) R)’
           by (strip_tac >> drule_all server_echoes >> metis_tac[])
      >> Cases_on ‘fd = c’
      (* fd is this connection: it is served by its handler, on L *)
      >- (rpt BasicProvers.VAR_EQ_TAC >> qexistsl_tac [‘LENGTH h1 + 1’, ‘L’]
          >> rpt conj_tac
          >- simp[Abbr ‘L’]
          >- (rpt strip_tac >> gvs[Abbr ‘L’, views_ready]
              >> simp[EL_APPEND2, EL_CONS, PRE_SUB1, views_ready])
          >- simp[]
          >- (simp[] >> simp[Abbr ‘L’] >> irule filter_both_own
              >> gvs[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM, Abbr ‘R’])
          >- (rpt strip_tac
              >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
                   (qspec_then ‘LENGTH h1 + 1 + j’ mp_tac)
              >> simp[nreads_both, views_TAKE]
              >> strip_tac >> irule nreads_server_untouched >> fs[])
          >> rpt strip_tac >> spose_not_then assume_tac
          >> qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
          >> impl_tac >- simp[] >> strip_tac
          >> qpat_x_assum ‘MEM c (accepted (trans _ (TAKE _ _)))’ mp_tac
          >> ASM_REWRITE_TAC[MEM])
      (* fd is another connection: it is served inside the rest of the server *)
      >> ‘LENGTH R = LENGTH h3 ∧ ∀i. i < LENGTH h3 ⇒ (EL i R).ready = (EL i h3).ready’
           by simp[Abbr ‘R’, views_ready]
      >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘R’ mp_tac)
      >> impl_tac >- simp[] >> impl_tac >- gvs[] >> strip_tac
      >> rename1 ‘a1 + LENGTH g1 = LENGTH R’
      >> qexistsl_tac [‘LENGTH h1 + 1 + a1’, ‘g1’] >> rpt conj_tac
      >- simp[]
      >- (rpt strip_tac >> ‘a1 + i < LENGTH h3’ by simp[]
          >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
      >- simp[]
      >- (‘FILTER (on_fd fd) (trans (both (handler c) (server lfd)) h3) =
           FILTER (on_fd fd) (trans (server lfd) R)’
            by simp[filter_both_other, Abbr ‘R’]
          >> simp[])
      >- (rpt strip_tac
          >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
               (qspec_then ‘LENGTH h1 + 1 + a1 + j’ mp_tac)
          >> simp[nreads_both, views_TAKE, nreads_handler_other])
      >> rpt strip_tac >> Cases_on ‘m ≤ LENGTH h1’
      >- (qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
          >> impl_tac >- simp[] >> strip_tac
          >> qpat_x_assum ‘MEM fd (accepted (trans _ (TAKE _ _)))’ mp_tac
          >> ASM_REWRITE_TAC[MEM])
      >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’ (qspec_then ‘m’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac
      >> ‘MEM fd (accepted (trans (server lfd) (TAKE (m − LENGTH h1 − 1) R)))’
           by (qpat_x_assum ‘MEM fd (accepted (trans _ (TAKE m _)))’ mp_tac
               >> simp[accepted_both, views_TAKE, Abbr ‘R’])
      >> qpat_x_assum ‘∀m. m ≤ LENGTH R ∧ _ ⇒ _’ (qspec_then ‘m − LENGTH h1 − 1’ mp_tac)
      >> simp[])
  (* no new connection: the server starts again *)
  >> ‘after_accept lfd r = server lfd’ by (Cases_on ‘r’ >> gvs[after_accept_def])
  >> ‘∀tr. accepted ((Accept lfd, SOME r) :: tr) = accepted tr’ by (Cases_on ‘r’ >> gvs[])
  >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘h3’ mp_tac)
  >> impl_tac >- simp[]
  >> impl_tac
  >- (qpat_x_assum ‘fresh _’ mp_tac >> qpat_x_assum ‘MEM fd _’ mp_tac
      >> qpat_x_assum ‘prompt (after_accept _ _) _’ mp_tac >> simp[fresh_def])
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
