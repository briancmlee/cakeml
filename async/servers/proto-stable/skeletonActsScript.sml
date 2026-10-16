(*
  What the generic server skeleton's actions need (model; option C,
  design/33 §2.5 (c)).  Per action, where protoCause's proto_cause
  says only that something changed:

  - an Accept emitted with a new snapshot s is on the listener, and the
    listener is readable in s;
  - a Read of g emitted with s has g readable in s, and the server has
    accepted g more often than a read of g has returned EOF (the handler
    of g has not finished).

  For server_with hf lfd, from the same facts about the handlers hf fd
  (sw_new_actions), and the EOF bookkeeping on the way (sw_counts, the
  Level 1 half of echoBlockingWaits's server_live).

  MAIN: sw_counts, sw_new_actions.
*)
Theory skeletonActs
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncTranscript echoServer
  echoServerSafety echoProgress skeleton echoBlockingWaits
  echoCause echoServerCause protoCause
Libs
  preamble

Overload NA = “λm h. new_actions (log_of m) h”

(* ------------------------------------------------------------------------
   The building blocks, per action
   ------------------------------------------------------------------------ *)

(* An emit's new actions with s: its continuation's first ones, if s
   answers it; later, the continuation's new ones *)
Theorem emit_new:
  MEM a (NA (bind (emit (a0 : echoServer$action))
                  (f : echoServer$response -> (event, echoServer$response) snapshot list ->
                       (echoServer$action, unit option) asyncCore$outcome))
            (q ++ [s : (event, echoServer$response) snapshot])) ⇒
  (q = [] ∧ ∃r. oHD s.results = SOME r ∧ MEM a (f r []).actions) ∨
  ∃s1 q' r. q = s1 :: q' ∧ oHD s1.results = SOME r ∧ MEM a (NA (f r) (q' ++ [s]))
Proof
  simp[new_actions_SNOC, log_of_def] >> Cases_on ‘q’ >> simp[bind_emit_NIL]
  >- (Cases_on ‘oHD s.results’ >> simp[bind_emit_unanswered] >>
      rename1 ‘oHD s.results = SOME r’ >>
      qspecl_then [‘s’, ‘r’, ‘a0’, ‘f’, ‘[]’] mp_tac
        (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS) >>
      simp[])
  >> Cases_on ‘oHD h.results’ >> simp[bind_emit_unanswered]
  >> rename1 ‘oHD h.results = SOME r’
  >> qspecl_then [‘h’, ‘r’, ‘a0’, ‘f’, ‘t ++ [s]’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS)
  >> qspecl_then [‘h’, ‘r’, ‘a0’, ‘f’, ‘t’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS)
  >> simp[]
QED

(* A wait for fd's new actions with s: its continuation's first ones, if
   fd is readable in s; later, the continuation's new ones *)
Theorem rdy_new:
  MEM a (NA (bind (rdy fd)
                  (g : unit -> (event, echoServer$response) snapshot list ->
                       (echoServer$action, unit option) asyncCore$outcome))
            (q ++ [s])) ⇒
  (first_readable fd (q ++ [s]) ∧ Readable fd ∈ s.ready ∧ MEM a (g () []).actions) ∨
  ∃h1 q2. q = h1 ++ q2 ∧ first_readable fd h1 ∧ MEM a (NA (g ()) (q2 ++ [s]))
Proof
  strip_tac >>
  ‘∀h. (∀n. n ≤ LENGTH h ⇒ ((rdy fd) (TAKE n h)).result = NONE) ⇒
       (bind (rdy fd) g h).actions = []’
    by (rpt strip_tac >>
        ‘bind (rdy fd) g h = <| actions := (rdy fd h).actions; result := NONE |>’
          by (irule bind_running >> first_assum ACCEPT_TAC) >>
        simp[readable_def, wait_def]) >>
  qspecl_then [‘rdy fd’, ‘q ++ [s]’] strip_assume_tac history_split
  (* still waiting after s: no actions *)
  >- (‘(bind (rdy fd) g (q ++ [s])).actions = []’ by simp[] >>
      gvs[new_actions_SNOC, log_of_def])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[] >>
  ‘first_readable fd h1’ by simp[first_readable_def] >>
  Cases_on ‘h2’ using SNOC_CASES
  (* the wait finished at s itself *)
  >- (disj1_tac >> gvs[] >> conj_tac >- metis_tac[first_readable_last] >>
      ‘(bind (rdy fd) g q).actions = []’
        by (first_x_assum irule >> rpt strip_tac >>
            gvs[first_readable_def, first_done_def] >>
            first_x_assum (qspec_then ‘n’ mp_tac) >> simp[TAKE_APPEND1]) >>
      qspecl_then [‘fd’, ‘q ++ [s]’, ‘g’, ‘[]’] mp_tac
        (Q.GENL [‘fd’, ‘h1’, ‘g’, ‘q’] readable_continues) >>
      simp[] >> strip_tac >>
      qpat_x_assum ‘MEM _ (NA _ _)’
        (mp_tac o SIMP_RULE std_ss [new_actions_SNOC, log_of_def]) >>
      qpat_x_assum ‘(bind _ _ q).actions = []’ (fn th => REWRITE_TAC[th]) >>
      qpat_x_assum ‘(bind _ _ (q ++ [s])).actions = _’ (fn th => REWRITE_TAC[th]) >>
      simp[])
  >> ‘s = x ∧ q = h1 ++ l’
       by (‘SNOC s q = SNOC x (h1 ++ l)’ by gvs[SNOC_APPEND] >> fs[SNOC_11])
  >> gvs[] >> disj2_tac >> qexistsl [‘h1’, ‘l’] >> simp[] >>
  qpat_x_assum ‘MEM _ _’ mp_tac >>
  simp[SNOC_APPEND] >> simp[new_actions_SNOC, log_of_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  qspecl_then [‘fd’, ‘h1’, ‘g’, ‘l ++ [s]’] mp_tac
    (Q.GENL [‘fd’, ‘h1’, ‘g’, ‘q’] readable_continues) >>
  qspecl_then [‘fd’, ‘h1’, ‘g’, ‘l’] mp_tac
    (Q.GENL [‘fd’, ‘h1’, ‘g’, ‘q’] readable_continues) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The skeleton
   ------------------------------------------------------------------------ *)

(* The handler facts sw_counts and sw_new_actions need: hf fd accepts
   nothing, reads EOF only on fd, at most once, and not while running;
   it starts without accepting or reading, and later accepts nothing and
   reads only fd, when fd is readable in the new snapshot, and is then
   still running *)
Definition hcounts_def:
  hcounts hf ⇔
    ∀fd h g. accs g (trans (hf fd) h) = 0 ∧
             (g ≠ fd ⇒ eofs g (trans (hf fd) h) = 0) ∧
             eofs fd (trans (hf fd) h) ≤ 1 ∧
             ((hf fd h).result = NONE ⇒ eofs fd (trans (hf fd) h) = 0)
End

Definition hacts_def:
  hacts (hf : num -> (event, echoServer$response) snapshot list ->
                     (echoServer$action, unit option) asyncCore$outcome) ⇔
    (∀fd. wf (hf fd)) ∧
    (∀fd a. MEM a (hf fd []).actions ⇒ (∀l. a ≠ Accept l) ∧ ∀g. a ≠ Read g) ∧
    ∀fd q s a. MEM a (NA (hf fd) (q ++ [s])) ⇒
               (∀l. a ≠ Accept l) ∧
               ∀g. a = Read g ⇒ g = fd ∧ Readable fd ∈ s.ready ∧
                                (hf fd (q ++ [s])).result = NONE
End

(* An emit whose first snapshot does not answer it: just the action *)
Theorem trans_bind_emit_unans:
  (h = [] ∨ ∃s q. h = s :: q ∧ oHD s.results = NONE) ⇒
  trans (bind (emit a) f) h = [(a, NONE)]
Proof
  rw[] >> DEP_REWRITE_TAC[trans_bind_running] >> simp[trans_emit, emit_def] >>
  Cases >> simp[]
QED

(* What the skeleton does with the accept's response (named, to keep the
   terms small) *)
Definition swk_def:
  swk hf lfd res =
    case res of
      Accepted fd => map (λp. ()) (both (hf fd) (server_with hf lfd))
    | _ => server_with hf lfd
End

Theorem sw_unfold_k:
  server_with hf lfd = bind (rdy lfd) (λu. bind (emit (Accept lfd)) (swk hf lfd))
Proof
  CONV_TAC (LAND_CONV (REWR_CONV server_with_unfold)) >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, swk_def]
QED

Theorem swk_acc:
  swk hf lfd (Accepted fd) = map (λp. ()) (both (hf fd) (server_with hf lfd))
Proof
  simp[swk_def]
QED

Theorem swk_other:
  (∀fd. r ≠ Accepted fd) ⇒ swk hf lfd r = server_with hf lfd
Proof
  Cases_on ‘r’ >> simp[swk_def]
QED

(* After the wait for the listener: the accept, then the rest *)
Theorem sw_after_wait:
  first_readable lfd h1 ⇒
  trans (server_with hf lfd) (h1 ++ q) = trans (bind (emit (Accept lfd)) (swk hf lfd)) q
Proof
  strip_tac >> ONCE_REWRITE_TAC[sw_unfold_k] >>
  qspecl_then [‘readable lfd’, ‘h1’, ‘()’, ‘λu. bind (emit (Accept lfd)) (swk hf lfd)’, ‘q’]
    mp_tac (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues) >>
  impl_tac >- gvs[first_readable_def, readable_def, wf_wait, settled_wait] >>
  simp[readable_def]
QED

(* ... and once the accept is answered with r *)
Theorem sw_wait_trans:
  first_readable lfd h1 ∧ oHD s1.results = SOME r ⇒
  trans (server_with hf lfd) (h1 ++ s1 :: q) = (Accept lfd, SOME r) :: trans (swk hf lfd r) q
Proof
  rpt strip_tac >> drule sw_after_wait >> disch_then (fn th => REWRITE_TAC[th]) >>
  qspecl_then [‘emit (Accept lfd)’, ‘[s1]’, ‘r’, ‘swk hf lfd’, ‘q’] mp_tac
    (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues) >>
  impl_tac >- simp[wf_emit, settled_emit, first_done_def, emit_def] >>
  simp[trans_emit]
QED

(* MAIN: the server never reads EOF of g more often than it accepted g *)
Theorem sw_counts:
  hcounts hf ⇒
  ∀h g. eofs g (trans (server_with hf lfd) h) ≤ accs g (trans (server_with hf lfd) h)
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> qspecl_then [‘rdy lfd’, ‘h’] strip_assume_tac history_split
  >- (‘trans (server_with hf lfd) h = []’
        by (ONCE_REWRITE_TAC[sw_unfold_k] >>
            DEP_REWRITE_TAC[trans_bind_running] >> simp[readable_def]) >>
      simp[])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[]
  >> ‘first_readable lfd h1’ by simp[first_readable_def]
  >> ‘h2 = [] ∨ (∃s1 q. h2 = s1 :: q ∧ oHD s1.results = NONE) ∨
      ∃s1 q r. h2 = s1 :: q ∧ oHD s1.results = SOME r’
       by (Cases_on ‘h2’ >> simp[] >> Cases_on ‘oHD h.results’ >> simp[])
  >- simp[sw_after_wait, trans_bind_emit_unans, is_acc_def, is_eof_def]
  >- simp[sw_after_wait, trans_bind_emit_unans, is_acc_def, is_eof_def]
  >> gvs[] >> drule_all sw_wait_trans >> disch_then (fn th => REWRITE_TAC[th])
  >> ‘LENGTH q < LENGTH (h1 ++ s1 :: q)’ by simp[]
  >> reverse (Cases_on ‘∃fd. r = Accepted fd’)
  >- (gvs[swk_other, is_acc_def, is_eof_def] >> metis_tac[])
  >> gvs[swk_acc, trans_both_counts, is_acc_def, is_eof_def]
  >> first_x_assum (qspec_then ‘right_view (hf fd) (server_with hf lfd) q’ mp_tac)
  >> simp[] >> disch_then (qspec_then ‘g’ assume_tac)
  >> gvs[hcounts_def]
  >> first_x_assum (qspecl_then [‘fd’, ‘left_view (hf fd) (server_with hf lfd) q’, ‘g’]
                      strip_assume_tac)
  >> Cases_on ‘g = fd’ >> gvs[]
QED

(* Started, the skeleton waits for the listener *)
Theorem sw_NIL_actions:
  (server_with hf lfd []).actions = []
Proof
  ONCE_REWRITE_TAC[sw_unfold_k] >>
  ‘bind (rdy lfd) (λu. bind (emit (Accept lfd)) (swk hf lfd)) [] =
   <| actions := (rdy lfd []).actions; result := NONE |>’
    by (irule bind_running >> simp[readable_def, wait_def, first_some_def]) >>
  simp[readable_def, wait_def]
QED

(* The handler's share of a new snapshot: its reads, and its EOF count *)
Theorem sw_left_reads:
  hacts hf ∧ hcounts hf ∧ MEM a (NA (hf fd) (left_view (hf fd) m2 (q ++ [s]))) ⇒
  (∀l. a ≠ Accept l) ∧
  ∀g. a = Read g ⇒ g = fd ∧ Readable fd ∈ s.ready ∧
                   eofs fd (trans (hf fd) (left_view (hf fd) m2 (q ++ [s]))) = 0
Proof
  strip_tac >>
  qabbrev_tac ‘L = left_view (hf fd) m2 q’ >>
  qabbrev_tac ‘s' = s with results := TAKE (LENGTH (NA (hf fd) L)) s.results’ >>
  ‘left_view (hf fd) m2 (q ++ [s]) = L ++ [s']’
    by simp[Abbr ‘L’, Abbr ‘s'’, left_view_SNOC_eq] >>
  ‘s'.ready = s.ready’ by simp[Abbr ‘s'’] >>
  gvs[hacts_def] >> first_x_assum drule >> strip_tac >> simp[] >>
  rpt strip_tac >> gvs[] >> gvs[hcounts_def]
QED

(* The rest of the server's share: a snapshot with the same ready set *)
Theorem sw_right_share:
  MEM a (NA m2 (right_view m1 m2 (q ++ [s]))) ⇒
  ∃R s2. right_view m1 m2 (q ++ [s]) = R ++ [s2] ∧ LENGTH R = LENGTH q ∧
         s2.ready = s.ready ∧ MEM a (NA m2 (R ++ [s2]))
Proof
  strip_tac >> qexistsl [‘right_view m1 m2 q’,
    ‘s with results := DROP (LENGTH (NA m1 (left_view m1 m2 q))) s.results’] >>
  gvs[right_view_SNOC_eq]
QED

(* MAIN: the skeleton accepts only when the listener is readable, and
   reads g only when g is readable and its handler has not finished, even
   counting the responses the new snapshot brings *)
Theorem sw_new_actions:
  hcounts hf ∧ hacts hf ⇒
  ∀q s a. MEM a (NA (server_with hf lfd) (q ++ [s])) ⇒
    (∀l. a = Accept l ⇒ l = lfd ∧ Readable lfd ∈ s.ready) ∧
    ∀g. a = Read g ⇒ Readable g ∈ s.ready ∧
                     eofs g (trans (server_with hf lfd) (q ++ [s])) <
                     accs g (trans (server_with hf lfd) (q ++ [s]))
Proof
  strip_tac >>
  ‘∀h g. eofs g (trans (server_with hf lfd) h) ≤ accs g (trans (server_with hf lfd) h)’
    by metis_tac[sw_counts] >>
  gen_tac >> completeInduct_on ‘LENGTH q’ >> rpt gen_tac >> strip_tac >>
  gvs[PULL_FORALL] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘MEM _ _’ (mp_tac o ONCE_REWRITE_RULE[sw_unfold_k]) >>
  strip_tac >> drule rdy_new >> strip_tac
  (* the wait finished at s: the accept *)
  >- gvs[bind_emit_NIL]
  >> pop_assum (assume_tac o BETA_RULE) >> drule emit_new >> strip_tac
  (* s answers the accept: the handler's first actions *)
  >- (‘(server_with hf lfd []).actions = []’ by simp[sw_NIL_actions] >>
      gvs[] >> reverse (Cases_on ‘∃fd. r = Accepted fd’)
      >- gvs[swk_other]
      >> gvs[swk_acc, asyncLevel1Theory.map_def, both_NIL] >>
      fs[hacts_def] >> res_tac >> rw[] >> metis_tac[])
  (* later: the handler beside the rest of the server, or the server *)
  >> gvs[]
  >> ‘trans (server_with hf lfd) (h1 ++ s1 :: (q' ++ [s])) =
      (Accept lfd, SOME r) :: trans (swk hf lfd r) (q' ++ [s])’
       by (irule sw_wait_trans >> simp[])
  >> simp[is_acc_def, is_eof_def]
  >> ‘LENGTH q' < LENGTH (h1 ++ s1 :: q')’ by simp[]
  >> reverse (Cases_on ‘∃fd. r = Accepted fd’)
  >- (gvs[swk_other] >>
      first_x_assum (qspecl_then [‘q'’, ‘s’, ‘a’] mp_tac) >> simp[] >>
      simp[is_acc_def, is_eof_def] >> metis_tac[])
  >> gvs[swk_acc]
  >> simp[trans_both_counts]
  >> qpat_x_assum ‘MEM _ (NA (both _ _) _)’
       (strip_assume_tac o SIMP_RULE (srw_ss()) [both_new_actions])
  (* the handler of fd *)
  >- (drule_all sw_left_reads >> strip_tac >> simp[] >> rpt strip_tac >> gvs[] >>
      ‘accs fd (trans (hf fd) (left_view (hf fd) (server_with hf lfd) (q' ++ [s]))) = 0’
        by gvs[hcounts_def] >>
      qpat_x_assum ‘∀h g. eofs _ _ ≤ _’
        (qspecl_then [‘right_view (hf fd) (server_with hf lfd) (q' ++ [s])’, ‘fd’] mp_tac) >>
      simp[is_acc_def, is_eof_def])
  (* the rest of the server *)
  >> drule sw_right_share >> strip_tac
  >> ‘LENGTH R < LENGTH h1 + SUC (LENGTH q')’ by simp[]
  >> qpat_x_assum ‘∀q'' s' a' l g. LENGTH q'' < _ ⇒ _’
       (qspecl_then [‘R’, ‘s2’, ‘a’] mp_tac)
  >> asm_simp_tac std_ss [] >> strip_tac >> simp[]
  >> rpt strip_tac >> gvs[]
  >> gvs[hcounts_def]
  >> first_x_assum (qspecl_then [‘fd’, ‘left_view (hf fd) (server_with hf lfd) (q' ++ [s])’, ‘g’]
                      strip_assume_tac)
  >> Cases_on ‘g = fd’ >> gvs[is_acc_def, is_eof_def]
QED
