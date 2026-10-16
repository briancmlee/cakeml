(*
  What the library's skeleton server_v needs for its actions (design/37
  §5, step B): skeletonActs's sw_new_actions for server_with, over any
  vocabulary V.  The socket action of an action is read through V.sact,
  and the counts of accepts and EOFs through the socket part of the
  transcript, sproj V.

  - an action that is an Accept, emitted with a new snapshot s, is on the
    listener, and the listener is readable in s;
  - an action that is a Read of g has g readable in s, and the server has
    accepted g more often than it has read g's EOF.

  MAIN: sv_counts, sv_new_actions.
*)
Theory skeletonVActs
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncTranscript echoServer
  echoServerSafety echoProgress skeleton echoBlockingWaits
  echoCause echoServerCause protoCause skeletonActs skeletonV
  skeletonVProgress
Libs
  preamble

(* The counts of the socket part of a transcript *)
Overload accs_v = “λV g tr. accs g (sproj V tr)”
Overload eofs_v = “λV g tr. eofs g (sproj V tr)”

Theorem accs_sproj[local]:
  ∀tr. accs g (sproj V tr) =
       LENGTH (FILTER (λp. case V.sact (FST p) of
                             SOME x => is_acc g (x, OPTION_BIND (SND p) V.sres)
                           | NONE => F) tr)
Proof
  Induct >> simp[sproj_def] >> PairCases >> simp[] >>
  Cases_on ‘V.sact h0’ >> simp[GSYM sproj_def] >> rw[]
QED

Theorem eofs_sproj[local]:
  ∀tr. eofs g (sproj V tr) =
       LENGTH (FILTER (λp. case V.sact (FST p) of
                             SOME x => is_eof g (x, OPTION_BIND (SND p) V.sres)
                           | NONE => F) tr)
Proof
  Induct >> simp[sproj_def] >> PairCases >> simp[] >>
  Cases_on ‘V.sact h0’ >> simp[GSYM sproj_def] >> rw[]
QED

(* Counting the socket part over both's transcript *)
Theorem sproj_both_counts:
  accs_v V g (trans (both m1 m2) h) =
    accs_v V g (trans m1 (left_view m1 m2 h)) + accs_v V g (trans m2 (right_view m1 m2 h)) ∧
  eofs_v V g (trans (both m1 m2) h) =
    eofs_v V g (trans m1 (left_view m1 m2 h)) + eofs_v V g (trans m2 (right_view m1 m2 h))
Proof
  simp[accs_sproj, eofs_sproj, trans_both_count]
QED

(* The accept's entry *)
Theorem counts_acc_entry[local]:
  vocab_ok V ⇒
  accs_v V g [(V.acc lfd, SOME r)] = (if vaccd V r = SOME g then 1 else 0) ∧
  eofs_v V g [(V.acc lfd, SOME r)] = 0 ∧
  accs_v V g [(V.acc lfd, NONE)] = 0 ∧ eofs_v V g [(V.acc lfd, NONE)] = 0
Proof
  strip_tac >> ‘V.sact (V.acc lfd) = SOME (Accept lfd)’ by fs[vocab_ok_def] >>
  simp[sproj_def, vaccd_def, is_acc_def, is_eof_def] >>
  every_case_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The skeleton
   ------------------------------------------------------------------------ *)

(* The handler facts: hf fd accepts nothing, reads EOF only on fd, at most
   once, and not while running (in the socket part); it starts without an
   accept or a read, and later emits no accept and reads only fd, when fd
   is readable in the new snapshot, and is then still running *)
Definition hcounts_v_def:
  hcounts_v V hf ⇔
    ∀fd h g. accs_v V g (trans (hf fd) h) = 0 ∧
             (g ≠ fd ⇒ eofs_v V g (trans (hf fd) h) = 0) ∧
             eofs_v V fd (trans (hf fd) h) ≤ 1 ∧
             ((hf fd h).result = NONE ⇒ eofs_v V fd (trans (hf fd) h) = 0)
End

Definition hacts_v_def:
  hacts_v V hf ⇔
    (∀fd. wf (hf fd)) ∧
    (∀fd a. MEM a (hf fd []).actions ⇒
            (∀l. V.sact a ≠ SOME (Accept l)) ∧ ∀g. V.sact a ≠ SOME (Read g)) ∧
    ∀fd q s a. MEM a (NA (hf fd) (q ++ [s])) ⇒
               (∀l. V.sact a ≠ SOME (Accept l)) ∧
               ∀g. V.sact a = SOME (Read g) ⇒
                   g = fd ∧ Readable fd ∈ s.ready ∧ (hf fd (q ++ [s])).result = NONE
End

(* ------------------------------------------------------------------------
   The building blocks, at any types (skeletonActs's emit_new and rdy_new
   are stated at the echo vocabulary's types)
   ------------------------------------------------------------------------ *)

Theorem emit_new_v:
  MEM a (NA (bind (emit a0) f) (q ++ [s])) ⇒
  (q = [] ∧ ∃r. oHD s.results = SOME r ∧ MEM a (f r []).actions) ∨
  ∃s1 q' r. q = s1 :: q' ∧ oHD s1.results = SOME r ∧ MEM a (NA (f r) (q' ++ [s]))
Proof
  simp[new_actions_SNOC, log_of_def] >> Cases_on ‘q’ >> simp[bind_emit_NIL]
  >- (Cases_on ‘oHD s.results’ >> simp[bind_emit_unanswered] >>
      rename1 ‘oHD s.results = SOME r’ >>
      ‘bind (emit a0) f [s] = <| actions := a0 :: (f r []).actions; result := (f r []).result |>’
        by (irule bind_emit_CONS >> simp[]) >>
      simp[])
  >> Cases_on ‘oHD h.results’ >> simp[bind_emit_unanswered]
  >> rename1 ‘oHD h.results = SOME r’
  >> ‘∀q. bind (emit a0) f (h :: q) =
         <| actions := a0 :: (f r q).actions; result := (f r q).result |>’
       by (gen_tac >> irule bind_emit_CONS >> simp[])
  >> simp[]
QED

Theorem readable_actions[local]:
  (readable fd h).actions = [] ∧ NA (readable fd) h = []
Proof
  simp[new_actions_def, log_of_def, readable_def, wait_def]
QED

Theorem bind_readable_running[local]:
  (∀n. n ≤ LENGTH h ⇒
       ((readable fd : (event, 'r) snapshot list -> ('a, unit option) asyncCore$outcome)
          (TAKE n h)).result = NONE) ⇒
  (bind (readable fd : (event, 'r) snapshot list -> ('a, unit option) asyncCore$outcome) g h).actions = []
Proof
  strip_tac >>
  ‘bind (readable fd) g h = <| actions := (readable fd h).actions; result := NONE |>’
    by (irule bind_running >> first_assum ACCEPT_TAC) >>
  simp[readable_actions]
QED

Theorem rd_continues[local]:
  first_rd fd h1 ⇒ (bind (readable fd) g (h1 ++ q)).actions = (g () q).actions
Proof
  rw[] >> ‘first_done (readable fd) h1 ()’ by simp[first_done_readable] >>
  drule_then (fn th => REWRITE_TAC[th]) bind_continues_actions >>
  simp[readable_actions]
QED

Theorem first_rd_last[local]:
  first_rd fd (q ++ [s]) ⇒ Readable fd ∈ s.ready
Proof
  rw[first_rd_def] >>
  first_x_assum (qspec_then ‘LENGTH q’ mp_tac) >> simp[TAKE_LENGTH_APPEND] >>
  strip_tac >> gvs[first_some_SNOC] >> pop_assum mp_tac >> rw[]
QED

Theorem rdy_new_v:
  MEM a (NA (bind (readable fd) g) (q ++ [s])) ⇒
  (first_rd fd (q ++ [s]) ∧ Readable fd ∈ s.ready ∧ MEM a (g () []).actions) ∨
  ∃h1 q2. q = h1 ++ q2 ∧ first_rd fd h1 ∧ MEM a (NA (g ()) (q2 ++ [s]))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘bind RD g’ >>
  qspecl_then [‘RD’, ‘q ++ [s]’] strip_assume_tac history_split
  >- (‘bind RD g (q ++ [s]) = <| actions := (RD (q ++ [s])).actions; result := NONE |>’
        by (irule bind_running >> simp[]) >>
      ‘bind RD g q = <| actions := (RD q).actions; result := NONE |>’
        by (irule bind_running >> rpt strip_tac >>
            ‘n ≤ LENGTH (q ++ [s])’ by simp[] >>
            first_x_assum drule >> simp[TAKE_APPEND1]) >>
      gvs[new_actions_SNOC, log_of_def, Abbr ‘RD’, readable_def, wait_def])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[] >>
  (* while RD is abbreviated, its type is the goal's *)
  drule_then (Q.ISPEC_THEN ‘g’ assume_tac) bind_continues_actions >>
  gvs[Abbr ‘RD’, first_done_readable, readable_actions] >>
  Cases_on ‘h2’ using SNOC_CASES
  >- (disj1_tac >> gvs[] >> conj_tac >- metis_tac[first_rd_last] >>
      ‘(bind (readable fd) g q).actions = []’
        by (irule bind_readable_running >> rpt strip_tac >>
            gvs[first_rd_def] >>
            first_x_assum (qspec_then ‘n’ mp_tac) >>
            simp[TAKE_APPEND1, readable_def, wait_def]) >>
      first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[skip_results_def] >>
      strip_tac >>
      qpat_x_assum ‘MEM _ (NA _ _)’ mp_tac >> simp[new_actions_SNOC, log_of_def])
  >> ‘s = x ∧ q = h1 ++ l’
       by (‘SNOC s q = SNOC x (h1 ++ l)’ by gvs[SNOC_APPEND] >> fs[SNOC_11])
  >> gvs[] >> disj2_tac >> qexistsl [‘h1’, ‘l’] >> simp[] >>
  qpat_x_assum ‘MEM _ _’ mp_tac >>
  simp[SNOC_APPEND] >> simp[new_actions_SNOC, log_of_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[skip_results_def]
QED

(* ------------------------------------------------------------------------
   The skeleton: m4-server's step lemmas (skeletonVProgress)
   ------------------------------------------------------------------------ *)

Theorem sv_after_accept_acc:
  vaccd V r = SOME fd ⇒
  sv_after_accept V hf lfd r = map (λp. ()) (both (hf fd) (server_v V hf lfd))
Proof
  simp[sv_after_accept_def]
QED

Theorem sv_after_accept_other:
  vaccd V r = NONE ⇒ sv_after_accept V hf lfd r = server_v V hf lfd
Proof
  simp[sv_after_accept_def]
QED

Theorem counts_CONS_entry[local]:
  accs_v V g (p :: tr) = accs_v V g [p] + accs_v V g tr ∧
  eofs_v V g (p :: tr) = eofs_v V g [p] + eofs_v V g tr
Proof
  simp[sproj_def]
QED

(* After the wait for the listener: the accept, then the rest *)
Theorem sv_after_wait:
  first_rd lfd h1 ⇒
  trans (server_v V hf lfd) (h1 ++ q) =
  trans (bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)) q
Proof
  strip_tac >> ONCE_REWRITE_TAC[sv_steps] >>
  ‘trans (bind (readable lfd) (λu. bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)))
         (h1 ++ q) =
   trans (readable lfd) h1 ++ trans ((λu. bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)) ()) q’
    by (irule trans_bind_continues >>
        simp[first_done_readable, readable_def, wf_wait, settled_wait]) >>
  simp[readable_def]
QED

(* Before the listener is readable, nothing; afterwards, the accept and
   the rest *)
Theorem sv_trans_cases:
  trans (server_v V hf lfd) h = [] ∨
  ∃h1 h2. h = h1 ++ h2 ∧ first_rd lfd h1 ∧
          trans (server_v V hf lfd) h =
          trans (bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)) h2
Proof
  ONCE_REWRITE_TAC[sv_steps] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind RD K0) h’ >>
  qspecl_then [‘RD’, ‘h’] strip_assume_tac history_split
  >- (disj1_tac >> DEP_REWRITE_TAC[trans_bind_running] >> simp[Abbr ‘RD’, readable_def])
  >> disj2_tac >> qexistsl [‘h1’, ‘h2’] >>
  ‘x = ()’ by simp[oneTheory.one] >> gvs[Abbr ‘RD’, first_done_readable] >>
  ‘trans (bind (readable lfd) K0) (h1 ++ h2) = trans (readable lfd) h1 ++ trans (K0 ()) h2’
    by (irule trans_bind_continues >>
        simp[first_done_readable, readable_def, wf_wait, settled_wait]) >>
  simp[Abbr ‘K0’, readable_def]
QED

(* An emit answered by the first snapshot *)
Theorem trans_emit_answered:
  oHD s1.results = SOME r ⇒
  trans (bind (emit a) f) (s1 :: q) = (a, SOME r) :: trans (f r) q
Proof
  strip_tac >>
  ‘trans (bind (emit a) f) ([s1] ++ q) = trans (emit a) [s1] ++ trans (f r) q’
    by (irule trans_bind_continues >> simp[wf_emit, settled_emit, first_done_def, emit_def]) >>
  fs[trans_emit]
QED

(* MAIN: the server never reads EOF of g more often than it accepted g *)
Theorem sv_counts:
  vocab_ok V ∧ hcounts_v V hf ⇒
  ∀h g. eofs_v V g (trans (server_v V hf lfd) h) ≤ accs_v V g (trans (server_v V hf lfd) h)
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ‘trans (server_v V hf lfd) h = [] ∨
      ∃h1 h2. h = h1 ++ h2 ∧ first_rd lfd h1 ∧
              trans (server_v V hf lfd) h =
              trans (bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)) h2’
       by MATCH_ACCEPT_TAC sv_trans_cases
  >- simp[sproj_def]
  >> gvs[]
  >> ‘h2 = [] ∨ (∃s1 q. h2 = s1 :: q ∧ oHD s1.results = NONE) ∨
      ∃s1 q r. h2 = s1 :: q ∧ oHD s1.results = SOME r’
       by (Cases_on ‘h2’ >> simp[] >> Cases_on ‘oHD h.results’ >> simp[])
  >- simp[trans_bind_emit_unans, counts_acc_entry]
  >- simp[trans_bind_emit_unans, counts_acc_entry]
  >> gvs[]
  >> ‘trans (bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)) (s1 :: q) =
      (V.acc lfd, SOME r) :: trans (sv_after_accept V hf lfd r) q’
       by (irule trans_emit_answered >> simp[])
  >> pop_assum (fn th => REWRITE_TAC[th])
  >> ONCE_REWRITE_TAC[counts_CONS_entry] >> simp[counts_acc_entry]
  >> ‘LENGTH q < LENGTH (h1 ++ s1 :: q)’ by simp[]
  >> Cases_on ‘vaccd V r’
  >- (‘sv_after_accept V hf lfd r = server_v V hf lfd’ by simp[sv_after_accept_def] >>
      pop_assum (fn th => REWRITE_TAC[th]) >>
      first_x_assum (qspec_then ‘q’ mp_tac) >> simp[])
  >> rename1 ‘vaccd V r = SOME fd’
  >> ‘sv_after_accept V hf lfd r = map (λp. ()) (both (hf fd) (server_v V hf lfd))’
       by simp[sv_after_accept_def]
  >> pop_assum (fn th => REWRITE_TAC[th])
  >> simp[sproj_both_counts]
  >> first_x_assum (qspec_then ‘right_view (hf fd) (server_v V hf lfd) q’ mp_tac)
  >> simp[] >> disch_then (qspec_then ‘g’ assume_tac)
  >> gvs[hcounts_v_def]
  >> first_x_assum (qspecl_then [‘fd’, ‘left_view (hf fd) (server_v V hf lfd) q’, ‘g’]
                      strip_assume_tac)
  >> Cases_on ‘g = fd’ >> gvs[]
QED

(* Started, the skeleton waits for the listener *)
Theorem sv_NIL_actions:
  (server_v V hf lfd []).actions = []
Proof
  ONCE_REWRITE_TAC[sv_steps] >>
  qmatch_goalsub_abbrev_tac ‘bind RD K0 []’ >>
  ‘bind RD K0 [] = <| actions := (RD []).actions; result := NONE |>’
    by (irule bind_running >> simp[Abbr ‘RD’, readable_def, wait_def, first_some_def]) >>
  simp[Abbr ‘RD’, readable_def, wait_def]
QED

(* The handler's share of a new snapshot: its reads, and its EOF count *)
Theorem sv_left_reads:
  hacts_v V hf ∧ hcounts_v V hf ∧ MEM a (NA (hf fd) (left_view (hf fd) m2 (q ++ [s]))) ⇒
  (∀l. V.sact a ≠ SOME (Accept l)) ∧
  ∀g. V.sact a = SOME (Read g) ⇒
      g = fd ∧ Readable fd ∈ s.ready ∧
      eofs_v V fd (trans (hf fd) (left_view (hf fd) m2 (q ++ [s]))) = 0
Proof
  strip_tac >>
  qabbrev_tac ‘L = left_view (hf fd) m2 q’ >>
  qabbrev_tac ‘s' = s with results := TAKE (LENGTH (NA (hf fd) L)) s.results’ >>
  ‘left_view (hf fd) m2 (q ++ [s]) = L ++ [s']’
    by simp[Abbr ‘L’, Abbr ‘s'’, left_view_SNOC_eq] >>
  ‘s'.ready = s.ready’ by simp[Abbr ‘s'’] >>
  gvs[hacts_v_def] >> first_x_assum drule >> strip_tac >> simp[] >>
  rpt strip_tac >> gvs[] >> gvs[hcounts_v_def]
QED

(* MAIN: the skeleton accepts only when the listener is readable, and
   reads g only when g is readable and its handler has not finished, even
   counting the responses the new snapshot brings *)
Theorem sv_new_actions:
  vocab_ok V ∧ hcounts_v V hf ∧ hacts_v V hf ⇒
  ∀q s a. MEM a (NA (server_v V hf lfd) (q ++ [s])) ⇒
    (∀l. V.sact a = SOME (Accept l) ⇒ l = lfd ∧ Readable lfd ∈ s.ready) ∧
    ∀g. V.sact a = SOME (Read g) ⇒
        Readable g ∈ s.ready ∧
        eofs_v V g (trans (server_v V hf lfd) (q ++ [s])) <
        accs_v V g (trans (server_v V hf lfd) (q ++ [s]))
Proof
  strip_tac >>
  ‘∀h g. eofs_v V g (trans (server_v V hf lfd) h) ≤ accs_v V g (trans (server_v V hf lfd) h)’
    by metis_tac[sv_counts] >>
  gen_tac >> completeInduct_on ‘LENGTH q’ >> rpt gen_tac >> strip_tac >>
  gvs[PULL_FORALL] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘MEM _ _’ (mp_tac o ONCE_REWRITE_RULE[sv_steps]) >>
  strip_tac >> drule rdy_new_v >> strip_tac
  (* the wait finished at s: the accept *)
  >- gvs[bind_emit_NIL, vocab_ok_def]
  >> pop_assum (assume_tac o BETA_RULE) >> drule emit_new_v >> strip_tac
  (* s answers the accept: the handler's first actions *)
  >- (‘(server_v V hf lfd []).actions = []’ by simp[sv_NIL_actions] >>
      gvs[] >> Cases_on ‘vaccd V r’
      >- (‘sv_after_accept V hf lfd r = server_v V hf lfd’ by simp[sv_after_accept_def] >>
          gvs[])
      >> ‘sv_after_accept V hf lfd r = map (λp. ()) (both (hf x) (server_v V hf lfd))’
           by simp[sv_after_accept_def]
      >> gvs[asyncLevel1Theory.map_def, both_NIL] >>
      fs[hacts_v_def] >> res_tac >> rw[] >> metis_tac[])
  (* later: the handler beside the rest of the server, or the server *)
  >> gvs[]
  >> ‘trans (server_v V hf lfd) (h1 ++ [s1] ++ q' ++ [s]) =
      (V.acc lfd, SOME r) :: trans (sv_after_accept V hf lfd r) (q' ++ [s])’
       by (drule_all_then (Q.ISPECL_THEN [‘q' ++ [s]’, ‘hf’, ‘V’] mp_tac)
             sv_trans_accept >>
           simp[])
  >> pop_assum (fn th => REWRITE_TAC[th])
  >> ONCE_REWRITE_TAC[counts_CONS_entry]
  >> drule_then (fn th => simp[th]) counts_acc_entry
  >> ‘LENGTH q' < LENGTH (h1 ++ s1 :: q')’ by simp[]
  >> Cases_on ‘vaccd V r’
  >- (‘sv_after_accept V hf lfd r = server_v V hf lfd’ by simp[sv_after_accept_def] >>
      gvs[] >>
      first_x_assum (qspecl_then [‘q'’, ‘s’, ‘a’] mp_tac) >> simp[])
  >> rename1 ‘vaccd V r = SOME fd’
  >> ‘sv_after_accept V hf lfd r = map (λp. ()) (both (hf fd) (server_v V hf lfd))’
       by simp[sv_after_accept_def]
  >> gvs[]
  >> simp[sproj_both_counts]
  >> qpat_x_assum ‘MEM _ (NA (both _ _) _)’
       (strip_assume_tac o SIMP_RULE (srw_ss()) [both_new_actions])
  (* the handler of fd *)
  >- (drule_all sv_left_reads >> strip_tac >> simp[] >> rpt strip_tac >> gvs[] >>
      ‘accs_v V fd (trans (hf fd) (left_view (hf fd) (server_v V hf lfd) (q' ++ [s]))) = 0’
        by gvs[hcounts_v_def] >>
      qpat_x_assum ‘∀h g. eofs _ _ ≤ _’
        (qspecl_then [‘right_view (hf fd) (server_v V hf lfd) (q' ++ [s])’, ‘fd’] mp_tac) >>
      simp[])
  (* the rest of the server *)
  >> drule sw_right_share >> strip_tac
  >> ‘LENGTH R < LENGTH h1 + SUC (LENGTH q')’ by simp[]
  >> qpat_x_assum ‘∀q'' s' a' l g. LENGTH q'' < _ ⇒ _’
       (qspecl_then [‘R’, ‘s2’, ‘a’] mp_tac)
  >> asm_simp_tac std_ss [] >> strip_tac >> simp[]
  >> rpt strip_tac >> gvs[]
  >> gvs[hcounts_v_def]
  >> first_x_assum (qspecl_then [‘fd’, ‘left_view (hf fd) (server_v V hf lfd) (q' ++ [s])’, ‘g’]
                      strip_assume_tac)
  >> Cases_on ‘g = fd’ >> gvs[]
QED
