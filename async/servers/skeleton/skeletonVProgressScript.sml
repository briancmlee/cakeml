(*
  Progress of the skeleton  server_v V hf lfd  (skeletonV), for any
  vocabulary V with vocab_ok V and any handler hf that is well-formed,
  settled and only acts on its own fd (hokv V).  This is skeletonProgress
  (sw_handler_view, sw_accept_progress) for server_v: the proofs are
  skeletonProgress's, with Accept, Accepted, on_fd, accepted and nreads read
  through V.

  For idV every notion here is skeletonProgress's (hokv_idV, acceptedv_idV,
  freshv_idV, nreadsv_idV, nacceptsv_idV); sw_handler_view_from_v and
  sw_accept_progress_from_v re-derive skeletonProgress's two main theorems,
  with their statements unchanged, as a check.
*)
Theory skeletonVProgress
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncTranscript echoServer echoServerSafety
  echoProgress skeleton skeletonProgress skeletonV
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Reading a transcript through V
   ------------------------------------------------------------------------ *)

(* The connections handed out in a transcript *)
Definition acceptedv_def:
  acceptedv V tr = accepted (sproj V tr)
End

(* World assumption: the connections handed out are distinct *)
Definition freshv_def:
  freshv V tr ⇔ ALL_DISTINCT (acceptedv V tr)
End

(* An entry is an accept *)
Definition is_acc_v_def:
  is_acc_v V (p : 'a # 'r option) ⇔ ∃l. V.sact (FST p) = SOME (Accept l)
End

(* The reads of fd, and the accepts on lfd, among some actions *)
Definition nreadsv_def:
  nreadsv V fd acts = count (λa. a = V.rd fd) acts
End

Definition nacceptsv_def:
  nacceptsv V lfd acts = count (λa. a = V.acc lfd) acts
End

(* The handler is well-formed, settled, and only acts on its own fd *)
Definition hokv_def:
  hokv V hf ⇔
    ∀fd. wf (hf fd) ∧ settled (hf fd) ∧ ∀g. EVERY (on_fd_v V fd) (trans (hf fd) g)
End

Theorem acceptedv_NIL[simp]:
  acceptedv V [] = []
Proof
  simp[acceptedv_def, sproj_def, accepted_def]
QED

Theorem acceptedv_APPEND[simp]:
  acceptedv V (t1 ++ t2) = acceptedv V t1 ++ acceptedv V t2
Proof
  simp[acceptedv_def]
QED

(* The accept's entry hands out the fd its response names, if any *)
Theorem acceptedv_acc_CONS:
  vocab_ok V ⇒
  acceptedv V ((V.acc l, SOME r) :: tr) =
    (case vaccd V r of SOME c => [c] | NONE => []) ++ acceptedv V tr
Proof
  rw[vocab_ok_def, acceptedv_def, sproj_def, vaccd_def] >>
  Cases_on ‘V.sres r’ >> simp[accepted_def] >>
  CASE_TAC >> simp[accepted_def]
QED

Theorem nreadsv_simps[simp]:
  nreadsv V fd [] = 0 ∧
  nreadsv V fd (a :: as) = (if a = V.rd fd then 1 else 0) + nreadsv V fd as ∧
  nreadsv V fd (as ++ bs) = nreadsv V fd as + nreadsv V fd bs
Proof
  rw[nreadsv_def, count_def, FILTER_APPEND_DISTRIB]
QED

Theorem nacceptsv_simps[simp]:
  nacceptsv V lfd [] = 0 ∧
  nacceptsv V lfd (a :: as) = (if a = V.acc lfd then 1 else 0) + nacceptsv V lfd as
Proof
  rw[nacceptsv_def, count_def]
QED

(* An accept is not a read *)
Theorem vocab_acc_rd[simp]:
  vocab_ok V ⇒ (V.acc l = V.rd fd ⇔ F)
Proof
  rw[vocab_ok_def] >> strip_tac >>
  qpat_x_assum ‘∀l. V.sact (V.acc l) = _’ (qspec_then ‘l’ mp_tac) >> simp[]
QED

Theorem acceptedv_acc_NONE:
  vocab_ok V ⇒ acceptedv V ((V.acc l, NONE) :: tr) = acceptedv V tr
Proof
  rw[vocab_ok_def, acceptedv_def, sproj_def, accepted_def]
QED

Theorem on_fd_v_acc[simp]:
  vocab_ok V ⇒ (on_fd_v V fd (V.acc l, x) ⇔ F)
Proof
  simp[vocab_ok_def, on_fd_v_def]
QED

(* An entry of connection fd is not an accept *)
Theorem on_fd_v_not_acc:
  vocab_ok V ∧ on_fd_v V fd p ⇒ ¬is_acc_v V p
Proof
  PairCases_on ‘p’ >> rw[vocab_ok_def, on_fd_v_def, is_acc_v_def] >>
  strip_tac >> ‘p0 = V.acc l’ by metis_tac[] >> gvs[]
QED

Theorem acceptedv_FILTER:
  ∀tr. acceptedv V (FILTER (is_acc_v V) tr) = acceptedv V tr
Proof
  Induct >> simp[] >> PairCases >> rw[is_acc_v_def] >>
  fs[acceptedv_def, sproj_def] >>
  Cases_on ‘V.sact h0’ >> fs[] >> Cases_on ‘x’ >> fs[accepted_def]
QED

Theorem hokv_own:
  hokv V hf ⇒ ∀fd g. EVERY (on_fd_v V fd) (trans (hf fd) g)
Proof
  simp[hokv_def]
QED

Theorem hokv_wf:
  hokv V hf ⇒ ∀fd. wf (hf fd)
Proof
  simp[hokv_def]
QED

Theorem hokv_wf_server_v:
  hokv V hf ⇒ wf (server_v V hf lfd)
Proof
  metis_tac[hokv_wf, wf_server_v]
QED

(* For the identity vocabulary, these are skeletonProgress's notions *)
Theorem hokv_idV:
  hokv idV hf ⇔ hok hf
Proof
  simp[hokv_def, hok_def, on_fd_v_idV]
QED

Theorem acceptedv_idV:
  acceptedv idV tr = accepted tr
Proof
  simp[acceptedv_def]
QED

Theorem freshv_idV:
  freshv idV tr ⇔ fresh tr
Proof
  simp[freshv_def, fresh_def, acceptedv_idV]
QED

Theorem nreadsv_idV:
  nreadsv idV fd acts = nreads fd acts
Proof
  simp[nreadsv_def, nreads_count, idV_def]
QED

Theorem nacceptsv_idV:
  nacceptsv idV lfd acts = naccepts lfd acts
Proof
  simp[nacceptsv_def, naccepts_def, idV_def]
QED

(* ------------------------------------------------------------------------
   Waiting for the listener, at any type of responses
   ------------------------------------------------------------------------ *)

(* readable fd finishes exactly after h (first_readable, at any response
   type) *)
Definition first_rd_def:
  first_rd fd (h : (event, 'res) snapshot list) ⇔
    first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) h = SOME () ∧
    ∀n. n < LENGTH h ⇒
        first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) (TAKE n h) = NONE
End

Theorem first_done_readable:
  first_done (readable fd) h (x : unit) ⇔ first_rd fd h
Proof
  ‘x = ()’ by simp[oneTheory.one] >>
  simp[first_done_def, first_rd_def, readable_def, wait_def]
QED

Theorem first_rd_readable:
  first_rd fd h ⇔ first_readable fd h
Proof
  simp[first_readable_def, first_done_readable]
QED

Theorem first_rd_nonempty:
  first_rd fd h1 ⇒ h1 ≠ []
Proof
  rw[first_rd_def] >> strip_tac >> gvs[first_some_def]
QED

Theorem first_some_rd_NONE[local]:
  ∀l. first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) l = NONE ⇒
      ∀j. j < LENGTH l ⇒ Readable fd ∉ (EL j l).ready
Proof
  Induct >> simp[first_some_def] >> rw[] >> Cases_on ‘j’ >> gvs[]
QED

Theorem first_some_rd_SOME[local]:
  ∀l j. j < LENGTH l ∧ Readable fd ∈ (EL j l).ready ⇒
        first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) l ≠ NONE
Proof
  Induct >> simp[first_some_def] >> rw[] >> Cases_on ‘j’ >> gvs[] >> metis_tac[]
QED

Theorem first_rd_not_before:
  first_rd fd h1 ∧ j + 1 < LENGTH h1 ⇒
  Readable fd ∉ (EL j h1).ready
Proof
  rw[first_rd_def] >> first_x_assum (qspec_then ‘j + 1’ mp_tac) >> simp[] >>
  strip_tac >> drule first_some_rd_NONE >> disch_then (qspec_then ‘j’ mp_tac) >>
  simp[EL_TAKE]
QED

Theorem first_rd_now:
  Readable fd ∈ s.ready ⇒ first_rd fd [s]
Proof
  rw[first_rd_def, first_some_def]
QED

(* If fd is readable somewhere in h, waiting for it finishes in h *)
Theorem first_rd_split:
  j < LENGTH h ∧ Readable fd ∈ (EL j h).ready ⇒
  ∃h1 h2. h = h1 ++ h2 ∧ first_rd fd h1 ∧ LENGTH h1 ≤ j + 1
Proof
  strip_tac
  >> qspecl_then [‘readable fd’, ‘h’] strip_assume_tac history_split
  >- (first_x_assum (qspec_then ‘j + 1’ mp_tac)
      >> simp[readable_def, wait_def]
      >> qspecl_then [‘TAKE (j + 1) h’, ‘j’] mp_tac first_some_rd_SOME
      >> simp[EL_TAKE])
  >> gvs[first_done_readable]
  >> qexistsl_tac [‘h1’, ‘h2’] >> simp[]
  >> CCONTR_TAC >> gvs[NOT_LESS_EQUAL]
  >> drule first_rd_not_before >> disch_then (qspec_then ‘j’ mp_tac)
  >> gvs[EL_APPEND1]
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

Theorem TAKE_after_cons[local]:
  LENGTH h1 + 1 ≤ m ⇒
  TAKE m (h1 ++ [s] ++ h3) = h1 ++ [s] ++ TAKE (m − LENGTH h1 − 1) h3
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rw[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
  >> Cases_on ‘m − LENGTH h1’ >> gvs[]
QED

Theorem EXISTS_FILTER[local]:
  ∀l. EXISTS P l ⇔ FILTER P l ≠ []
Proof
  Induct >> rw[]
QED

(* Polymorphic forms of the bind steps, for use by matching *)
Theorem bind_readable_continues[local]:
  first_rd lfd (h1 : (event, 'res) snapshot list) ⇒
  bind (readable lfd : (event, 'res) snapshot list -> ('act, unit option) outcome) f
       (h1 ++ q) = f () q
Proof
  strip_tac >>
  ‘first_done (readable lfd : (event, 'res) snapshot list -> ('act, unit option) outcome)
     h1 ()’ by simp[first_done_readable] >>
  drule_then (qspecl_then [‘f’, ‘q’] mp_tac) bind_continues >>
  simp[new_actions_def, log_of_def, readable_def, wait_def] >>
  simp[outcome_component_equality]
QED

Theorem trans_bind_emit_NIL[local]:
  trans (bind (emit a) f) [] = [(a, NONE)]
Proof
  ‘∀h. h = [] ⇒ trans (bind (emit a) f) h = trans (emit a) h’
    by (rw[] >> irule trans_bind_running >> simp[emit_def]) >>
  simp[trans_emit]
QED

(* A connection's handler only acts on its own fd *)
Theorem hv_actions_own:
  hokv V hf ⇒
  MEM a (hf fd h).actions ⇒ V.owner a = SOME fd
Proof
  rpt strip_tac >> drule_then (qspecl_then [‘fd’, ‘h’] mp_tac) hokv_own
  >> ‘MAP FST (trans (hf fd) h) = (hf fd h).actions’
       by metis_tac[MAP_FST_trans, hokv_wf]
  >> rw[EVERY_MEM]
  >> qpat_x_assum ‘MEM a _’ mp_tac
  >> qpat_x_assum ‘MAP FST _ = _’ (SUBST1_TAC o GSYM) >> rw[MEM_MAP]
  >> first_x_assum drule >> simp[on_fd_v_def]
QED

(* ------------------------------------------------------------------------
   The skeleton, step by step
   ------------------------------------------------------------------------ *)

(* What the skeleton does with the response to its accept *)
Definition sv_after_accept_def:
  sv_after_accept V hf lfd res =
    case vaccd V res of
      SOME fd => map (λp. ()) (both (hf fd) (server_v V hf lfd))
    | NONE => server_v V hf lfd
End

Theorem sv_steps:
  server_v V hf lfd =
    bind (readable lfd) (λu. bind (emit (V.acc lfd)) (sv_after_accept V hf lfd))
Proof
  simp[Once server_v_unfold]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC
  >> simp[FUN_EQ_THM, sv_after_accept_def] >> gen_tac >> CASE_TAC >> simp[]
QED

(* MAIN: the skeleton only touches connections it has accepted, if each
   handler only acts on its own fd and the connections are distinct
   (server_with_isolates' second half) *)
Theorem sv_isolates:
  vocab_ok (V : ('act, 'k, 'q, 'res) vocab) ∧ (∀fd hh. EVERY (on_fd_v V fd) (trans (h fd) hh)) ⇒
  ∀hh. freshv V (trans (server_v V h lfd) hh) ⇒
       ∀fd. EXISTS (on_fd_v V fd) (trans (server_v V h lfd) hh) ⇒
            MEM fd (acceptedv V (trans (server_v V h lfd) hh))
Proof
  strip_tac >>
  ‘∀g hh. FILTER (is_acc_v V) (trans (h g) hh) = []’
    by (rw[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >>
        metis_tac[on_fd_v_not_acc]) >>
  ‘∀g fd hh. g ≠ fd ⇒ FILTER (on_fd_v V g) (trans (h fd) hh) = []’
    by (rw[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >>
        res_tac >> gvs[on_fd_v_def]) >>
  gen_tac >> measureInduct_on ‘LENGTH hh’
  >> ONCE_REWRITE_TAC[sv_steps]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) hh’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  (* accept *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (V.acc lfd)) K1) h2’
  >> qspecl_then [‘emit (vocab_acc V lfd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- simp[trans_emit]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, acceptedv_acc_CONS, sv_after_accept_def]
  >> Cases_on ‘vaccd V res’ >> simp[]
  (* no new connection: the rest of the server *)
  >- (rpt strip_tac
      >> ‘acceptedv V ((V.acc lfd, SOME res) :: trans (server_v V h lfd) h2') =
          acceptedv V (trans (server_v V h lfd) h2')’ by simp[acceptedv_acc_CONS]
      >> fs[freshv_def]
      >> qpat_x_assum ‘∀y. _’ (qspec_then ‘h2'’ mp_tac) >> simp[freshv_def])
  (* a new connection c: its handler, alongside the rest of the server *)
  >> rename1 ‘vaccd V res = SOME c’
  >> qabbrev_tac ‘L = left_view (h c) (server_v V h lfd) h2'’
  >> qabbrev_tac ‘R = right_view (h c) (server_v V h lfd) h2'’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
  >> ‘acceptedv V (trans (both (h c) (server_v V h lfd)) h2') =
      acceptedv V (trans (server_v V h lfd) R)’
       by (ONCE_REWRITE_TAC[GSYM acceptedv_FILTER] >> AP_TERM_TAC
           >> simp[Abbr ‘R’] >> irule trans_both_filter_right >> simp[])
  >> ‘acceptedv V ((V.acc lfd, SOME res) :: trans (both (h c) (server_v V h lfd)) h2') =
      c :: acceptedv V (trans (server_v V h lfd) R)’ by simp[acceptedv_acc_CONS]
  >> simp[freshv_def] >> strip_tac
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[freshv_def] >> strip_tac
  >> rpt strip_tac >> Cases_on ‘fd = c’ >> simp[]
  >> ‘FILTER (on_fd_v V fd) (trans (both (h c) (server_v V h lfd)) h2') =
      FILTER (on_fd_v V fd) (trans (server_v V h lfd) R)’
       by (simp[Abbr ‘R’] >> irule trans_both_filter_right >> simp[])
  >> first_x_assum irule >> gvs[EXISTS_FILTER]
QED

(* Until the listener is readable, the skeleton has accepted nothing *)
Theorem sv_waiting:
  vocab_ok (V : ('act, 'k, 'q, 'res) vocab) ∧ first_rd lfd h1 ∧ m ≤ LENGTH h1 ⇒
  acceptedv V (trans (server_v V hf lfd) (TAKE m h1)) = []
Proof
  rw[] >> ONCE_REWRITE_TAC[sv_steps] >> Cases_on ‘m < LENGTH h1’
  >- (qmatch_goalsub_abbrev_tac ‘trans (bind _ K0) _’
      >> ‘trans (bind (readable lfd) K0) (TAKE m h1) = trans (readable lfd) (TAKE m h1)’
           by (irule trans_bind_running >> gvs[first_rd_def, readable_def, wait_def]
               >> rw[] >> ‘TAKE n (TAKE m h1) = TAKE n h1’
                            by (rw[TAKE_TAKE_MIN] >> ‘MIN n m = n’ by simp[MIN_DEF]
                                >> simp[])
               >> simp[])
      >> simp[readable_def])
  >> ‘m = LENGTH h1’ by simp[] >> gvs[TAKE_LENGTH_ID]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind _ K0) _’
  >> ‘trans (bind (readable lfd) K0) (h1 ++ []) = trans (readable lfd) h1 ++ trans (K0 ()) []’
       by (irule trans_bind_continues >>
           simp[first_done_readable, readable_def, wf_wait, settled_wait])
  >> fs[Abbr ‘K0’, readable_def, trans_bind_emit_NIL, acceptedv_acc_NONE]
QED

(* Once the listener is readable, the skeleton accepts *)
Theorem sv_accepts:
  first_rd lfd h1 ⇒
  server_v V hf lfd (h1 ++ q) = bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) q
Proof
  rw[] >> ONCE_REWRITE_TAC[sv_steps] >> simp[bind_readable_continues]
QED

Theorem sv_waiting_actions:
  first_rd lfd h1 ∧ n < LENGTH h1 ⇒
  (server_v V hf lfd (TAKE n h1)).actions = []
Proof
  rw[] >> ONCE_REWRITE_TAC[sv_steps]
  >> ‘bind (readable lfd) (λu. bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)) (TAKE n h1) =
      <|actions := (readable lfd (TAKE n h1)).actions; result := NONE|>’
       by (irule bind_before_first_done >> simp[first_done_readable] >> metis_tac[])
  >> simp[readable_def, wait_def]
QED

Theorem sv_new_accept:
  first_rd lfd h1 ⇒
  new_actions (log_of (server_v V hf lfd)) h1 = [V.acc lfd]
Proof
  rw[] >> drule first_rd_nonempty >> strip_tac
  >> ‘(server_v V hf lfd h1).actions = [V.acc lfd]’
       by (‘server_v V hf lfd (h1 ++ []) =
            bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) []’
             by (irule sv_accepts >> simp[])
           >> fs[bind_emit_NIL])
  >> ‘(server_v V hf lfd (FRONT h1)).actions = []’
       by (‘FRONT h1 = TAKE (LENGTH h1 - 1) h1’ by simp[FRONT_BY_TAKE]
           >> simp[] >> irule sv_waiting_actions >> simp[]
           >> Cases_on ‘h1’ >> gvs[])
  >> simp[new_actions_def, log_of_def]
QED

(* The accept's response r arrives in s: the skeleton continues with r *)
Theorem sv_after_accept_actions:
  first_rd lfd h1 ∧ oHD s.results = SOME r ⇒
  (server_v (V : ('act, 'k, 'q, 'res) vocab) (hf : num -> (event, 'res) snapshot list -> ('act, 'z option) outcome) lfd (h1 ++ [s] ++ q)).actions =
    V.acc lfd :: (sv_after_accept V hf lfd r q).actions
Proof
  rpt strip_tac
  >> ‘server_v V hf lfd (h1 ++ [s] ++ q) =
      bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) (s :: q)’
       by (REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> irule sv_accepts >> simp[])
  >> ‘bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) (s :: q) =
      <| actions := V.acc lfd :: (sv_after_accept V hf lfd r q).actions;
         result := (sv_after_accept V hf lfd r q).result |>’
       by (irule bind_emit_CONS >> simp[])
  >> asm_rewrite_tac[] >> simp[]
QED

Theorem sv_trans_accept:
  first_rd lfd (h1 : (event, 'res) snapshot list) ∧ oHD s.results = SOME r ⇒
  trans (server_v (V : ('act, 'k, 'q, 'res) vocab) (hf : num -> (event, 'res) snapshot list -> ('act, 'z option) outcome) lfd) (h1 ++ [s] ++ q) =
    (V.acc lfd, SOME r) :: trans (sv_after_accept V hf lfd r) q
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac >> ONCE_REWRITE_TAC[sv_steps]
  >> qspecl_then [‘readable lfd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> impl_tac >- gvs[first_done_readable, readable_def, wf_wait, settled_wait]
  >> simp[] >> disch_then kall_tac
  >> qspecl_then [‘emit (vocab_acc V lfd)’, ‘[s]’, ‘r’, ‘sv_after_accept V hf lfd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME, trans_emit, readable_def]
QED

Theorem prompt_sv_after_accept:
  prompt (server_v (V : ('act, 'k, 'q, 'res) vocab) hf lfd) (h1 ++ [s] ++ q) ∧ first_rd lfd h1 ∧
  oHD s.results = SOME r ⇒
  prompt (sv_after_accept V hf lfd r) q
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rpt strip_tac
  >> qpat_x_assum ‘prompt _ _’ (mp_tac o ONCE_REWRITE_RULE[sv_steps])
  >> strip_tac
  >> qspecl_then [‘readable lfd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (V.acc lfd)) (sv_after_accept V hf lfd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> impl_tac >- gvs[first_done_readable, readable_def, wf_wait, settled_wait]
  >> simp[] >> strip_tac
  >> qspecl_then [‘emit (vocab_acc V lfd)’, ‘[s]’, ‘r’, ‘sv_after_accept V hf lfd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME]
QED

Theorem sv_prompt_accept_answered:
  prompt (server_v V hf lfd) (h1 ++ [s] ++ q) ∧ first_rd lfd h1 ⇒
  ∃r. oHD s.results = SOME r
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  rw[prompt_def] >> first_x_assum (qspec_then ‘LENGTH h1’ mp_tac)
  >> simp[TAKE_LENGTH_APPEND, responses_at_def, EL_APPEND2]
  >> drule sv_new_accept >> simp[]
  >> Cases_on ‘s.results’ >> simp[]
QED

(* ------------------------------------------------------------------------
   A new connection's handler, alongside the rest of the skeleton
   ------------------------------------------------------------------------ *)

(* Both sides see the ready sets of the whole history *)
Theorem sv_views_ready:
  i < LENGTH q ⇒
  (EL i (left_view (m1 : ('e, 'res) snapshot list -> ('act, 'x) outcome)
                   (m2 : ('e, 'res) snapshot list -> ('act, 'y) outcome) q)).ready =
    (EL i q).ready ∧
  (EL i (right_view m1 m2 q)).ready = (EL i q).ready
Proof
  strip_tac
  >> qspecl_then [‘log_of m1’, ‘log_of m2’, ‘q’] mp_tac
       (Q.GENL [‘a1’, ‘a2’] par_views_world)
  >> rw[left_view_def, right_view_def]
  >> qpat_x_assum ‘MAP _ (FST _) = _’ (mp_tac o Q.AP_TERM ‘EL i’)
  >> qpat_x_assum ‘MAP _ (SND _) = _’ (mp_tac o Q.AP_TERM ‘EL i’)
  >> simp[EL_MAP, LENGTH_par_views]
QED

Theorem LENGTH_views[local]:
  LENGTH (left_view m1 m2 q) = LENGTH q ∧ LENGTH (right_view m1 m2 q) = LENGTH q
Proof
  simp[left_view_def, right_view_def, LENGTH_par_views]
QED

Theorem hv_no_accepts[local]:
  vocab_ok V ∧ hokv V hf ⇒
  FILTER (is_acc_v V) (trans (hf c) h) = []
Proof
  strip_tac >> drule_then (qspecl_then [‘c’, ‘h’] mp_tac) hokv_own
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[on_fd_v_not_acc]
QED

(* The connections accepted alongside a handler are the rest of the
   skeleton's *)
Theorem sv_accepted_both:
  vocab_ok V ∧ hokv V hf ⇒
  acceptedv V (trans (both (hf c) (server_v V hf lfd)) q) =
  acceptedv V (trans (server_v V hf lfd) (right_view (hf c) (server_v V hf lfd) q))
Proof
  strip_tac >> ONCE_REWRITE_TAC[GSYM acceptedv_FILTER] >> AP_TERM_TAC
  >> irule trans_both_filter_right >> gs[hv_no_accepts]
QED

(* Another connection's entries alongside a handler are the rest of the
   skeleton's *)
Theorem sv_filter_both_other:
  hokv V hf ⇒
  fd ≠ c ⇒
  FILTER (on_fd_v V fd) (trans (both (hf c) (server_v V hf lfd)) q) =
  FILTER (on_fd_v V fd) (trans (server_v V hf lfd) (right_view (hf c) (server_v V hf lfd) q))
Proof
  rpt strip_tac >> irule trans_both_filter_right
  >> drule_then (qspecl_then [‘c’, ‘left_view (hf c) (server_v V hf lfd) q’] mp_tac)
       hokv_own
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> gvs[on_fd_v_def]
QED

(* The connection's own entries alongside its handler are the handler's,
   if the rest of the skeleton never touches it *)
Theorem sv_filter_both_own:
  hokv V hf ⇒
  FILTER (on_fd_v V c) (trans (server_v V hf lfd) (right_view (hf c) (server_v V hf lfd) q)) = [] ⇒
  FILTER (on_fd_v V c) (trans (both (hf c) (server_v V hf lfd)) q) =
  trans (hf c) (left_view (hf c) (server_v V hf lfd) q)
Proof
  rpt strip_tac >> drule trans_both_filter_left >> simp[]
  >> disch_then kall_tac >> simp[FILTER_EQ_ID]
  >> drule_then (qspecl_then [‘c’, ‘left_view (hf c) (server_v V hf lfd) q’] mp_tac)
       hokv_own
  >> simp[]
QED

Theorem sv_nreads_both:
  hokv V hf ⇒
  nreadsv V fd (both (hf c) (server_v V hf lfd) q).actions =
  nreadsv V fd (hf c (left_view (hf c) (server_v V hf lfd) q)).actions +
  nreadsv V fd (server_v V hf lfd (right_view (hf c) (server_v V hf lfd) q)).actions
Proof
  strip_tac >> simp[nreadsv_def] >> irule count_both >>
  metis_tac[hokv_wf, hokv_wf_server_v]
QED

Theorem nreadsv_hf_other:
  vocab_ok V ∧ hokv V hf ⇒
  fd ≠ c ⇒ nreadsv V fd (hf c h).actions = 0
Proof
  rw[nreadsv_def, count_def, FILTER_EQ_NIL, EVERY_MEM] >> strip_tac
  >> drule_all hv_actions_own >> fs[vocab_ok_def]
QED

(* If the skeleton never touches c, none of its prefixes reads c *)
Theorem nreadsv_sv_untouched:
  vocab_ok V ∧ hokv V hf ⇒
  ¬EXISTS (on_fd_v V c) (trans (server_v V hf lfd) R) ⇒
  nreadsv V c (server_v V hf lfd (TAKE j R)).actions = 0
Proof
  rw[nreadsv_def] >> irule count_prefix
  >> qexists_tac ‘(server_v V hf lfd R).actions’
  >> reverse conj_tac
  >- (irule wf_actions_grow >> gs[hokv_wf_server_v, IS_PREFIX_APPEND] >>
      metis_tac[TAKE_DROP])
  >> ‘MAP FST (trans (server_v V hf lfd) R) = (server_v V hf lfd R).actions’
       by metis_tac[MAP_FST_trans, hokv_wf_server_v]
  >> pop_assum (SUBST1_TAC o GSYM)
  >> gvs[count_def, FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, EXISTS_MEM]
  >> rpt strip_tac >> first_x_assum drule >>
  PairCases_on ‘y’ >> gvs[on_fd_v_def, vocab_ok_def]
QED

(* If the skeleton has accepted something, it waited for the listener (h1),
   accepted, and got the response r (in s) *)
Theorem sv_split:
  vocab_ok V ∧ prompt (server_v V hf lfd) h ∧
  acceptedv V (trans (server_v V hf lfd) h) ≠ [] ⇒
  ∃h1 s h3 r. h = h1 ++ [s] ++ h3 ∧ first_rd lfd h1 ∧ oHD s.results = SOME r
Proof
  strip_tac
  >> qspecl_then [‘readable lfd’, ‘h’] strip_assume_tac history_split
  >- (‘trans (server_v V hf lfd) h = trans (readable lfd) h’
        by (ONCE_REWRITE_TAC[sv_steps] >> irule trans_bind_running >>
            fs[readable_def, wait_def])
      >> qpat_x_assum ‘trans _ _ = trans _ _’ mp_tac
      >> simp[readable_def] >> strip_tac >> gvs[])
  >> gvs[first_done_readable]
  >> Cases_on ‘h2’
  >- (‘acceptedv V (trans (server_v V hf lfd) (TAKE (LENGTH h1) h1)) = []’
        by (irule sv_waiting >> simp[])
      >> gvs[])
  >> ‘prompt (server_v V hf lfd) (h1 ++ [h] ++ t)’
       by (qpat_x_assum ‘prompt _ _’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND])
  >> drule_all sv_prompt_accept_answered >> strip_tac
  >> qexistsl_tac [‘h1’, ‘h’, ‘t’, ‘r’] >> simp[]
QED

(* If m never touches c on R, it does not on any prefix of R *)
Theorem untouched_v_TAKE:
  wf m ∧ ¬EXISTS (on_fd_v V c) (trans m R) ⇒
  FILTER (on_fd_v V c) (trans m (TAKE j R)) = []
Proof
  rw[FILTER_EQ_NIL, EVERY_MEM] >> strip_tac >>
  ‘MEM (FST x) (m (TAKE j R)).actions’ by metis_tac[MAP_FST_trans, MEM_MAP] >>
  ‘(m (TAKE j R)).actions ≼ (m R).actions’
    by (irule wf_actions_grow >> simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]) >>
  ‘MEM (FST x) (m R).actions’ by metis_tac[IS_PREFIX_APPEND, MEM_APPEND] >>
  ‘MEM (FST x) (MAP FST (trans m R))’ by metis_tac[MAP_FST_trans] >>
  gvs[MEM_MAP, EXISTS_MEM] >> first_x_assum drule >>
  PairCases_on ‘x’ >> PairCases_on ‘y’ >> gvs[on_fd_v_def]
QED

(* MAIN: inside the skeleton, each accepted connection fd is served by its
   own handler, running on a view g of the skeleton's history from the
   round a in which fd was accepted: g has the same ready sets, the world
   answers the handler promptly, the handler's transcript is the skeleton's
   transcript restricted to fd, and the skeleton's reads of fd are the
   handler's (sw_handler_view, for any vocabulary) *)
Theorem sv_handler_view:
  ∀h. vocab_ok (V : ('act, 'k, 'q, 'res) vocab) ∧ hokv V (hf : num -> (event, 'res) snapshot list -> ('act, 'z option) outcome) ∧
      freshv V (trans (server_v V hf lfd) h) ∧
      prompt (server_v V hf lfd) h ∧
      MEM fd (acceptedv V (trans (server_v V hf lfd) h)) ⇒
      ∃a g. LENGTH g + a = LENGTH h ∧
            (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) h).ready) ∧
            prompt (hf fd) g ∧
            FILTER (on_fd_v V fd) (trans (server_v V hf lfd) h) = trans (hf fd) g ∧
            (∀j. j ≤ LENGTH g ⇒
                 FILTER (on_fd_v V fd) (trans (server_v V hf lfd) (TAKE (a + j) h)) =
                 trans (hf fd) (TAKE j g)) ∧
            (∀j. j ≤ LENGTH g ⇒
                 nreadsv V fd (server_v V hf lfd (TAKE (a + j) h)).actions =
                 nreadsv V fd (hf fd (TAKE j g)).actions) ∧
            (∀m. m ≤ LENGTH h ∧
                 MEM fd (acceptedv V (trans (server_v V hf lfd) (TAKE m h))) ⇒
                 a ≤ m)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt strip_tac
  (* the skeleton waited (h1), accepted, and got the response r (in s) *)
  >> ‘acceptedv V (trans (server_v V hf lfd) h) ≠ []’ by (strip_tac >> gvs[])
  >> drule_all sv_split >> strip_tac >> gvs[]
  >> ‘∀m. LENGTH h1 + 1 ≤ m ⇒
          trans (server_v V hf lfd) (TAKE m (h1 ++ [s] ++ h3)) =
            (V.acc lfd, SOME r) ::
            trans (sv_after_accept V hf lfd r) (TAKE (m − LENGTH h1 − 1) h3) ∧
          (server_v V hf lfd (TAKE m (h1 ++ [s] ++ h3))).actions =
            V.acc lfd :: (sv_after_accept V hf lfd r (TAKE (m − LENGTH h1 − 1) h3)).actions’
       by (rpt strip_tac >> simp[TAKE_after_cons]
           >> qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘TAKE (m − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sv_trans_accept)
           >> qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘TAKE (m − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sv_after_accept_actions)
           >> simp[])
  >> ‘trans (server_v V hf lfd) (h1 ++ [s] ++ h3) =
      (V.acc lfd, SOME r) :: trans (sv_after_accept V hf lfd r) h3’
       by (qspecl_then [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘h3’] mp_tac
             (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sv_trans_accept) >> simp[])
  >> ‘∀m. m ≤ LENGTH h1 ⇒
          acceptedv V (trans (server_v V hf lfd) (TAKE m (h1 ++ [s] ++ h3))) = []’
       by (rpt strip_tac >> ‘TAKE m (h1 ++ [s] ++ h3) = TAKE m h1’ by simp[TAKE_APPEND1]
           >> simp[] >> irule sv_waiting >> simp[])
  >> drule_all prompt_sv_after_accept >> strip_tac
  >> Cases_on ‘vaccd V r’
  (* no new connection: the skeleton starts again *)
  >- (‘sv_after_accept V hf lfd r = server_v V hf lfd’ by simp[sv_after_accept_def]
      >> ‘∀tr. acceptedv V ((V.acc lfd, SOME r) :: tr) = acceptedv V tr’
           by simp[acceptedv_acc_CONS]
      >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘h3’ mp_tac)
      >> impl_tac >- simp[]
      >> impl_tac
      >- (qpat_x_assum ‘freshv _ _’ mp_tac >> qpat_x_assum ‘MEM fd _’ mp_tac
          >> qpat_x_assum ‘prompt (sv_after_accept _ _ _ _) _’ mp_tac >> simp[freshv_def])
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
      >- (rpt strip_tac
          >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
               (qspec_then ‘LENGTH h1 + 1 + a1 + j’ mp_tac)
          >> simp[])
      >> rpt strip_tac >> Cases_on ‘m ≤ LENGTH h1’
      >- (qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
          >> impl_tac >- simp[] >> strip_tac
          >> qpat_x_assum ‘MEM fd (acceptedv _ (trans _ (TAKE _ _)))’ mp_tac
          >> ASM_REWRITE_TAC[MEM])
      >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’ (qspec_then ‘m’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac
      >> qpat_x_assum ‘∀m. m ≤ LENGTH h3 ∧ _ ⇒ _’ (qspec_then ‘m − LENGTH h1 − 1’ mp_tac)
      >> gvs[])
  (* a new connection c: its handler runs on L, the rest of the skeleton on R *)
  >> rename1 ‘vaccd V r = SOME c’
  >> qabbrev_tac ‘L = left_view (hf c) (server_v V hf lfd) h3’
  >> qabbrev_tac ‘R = right_view (hf c) (server_v V hf lfd) h3’
  >> ‘∀q. trans (sv_after_accept V hf lfd r) q =
          trans (both (hf c) (server_v V hf lfd)) q ∧
          (sv_after_accept V hf lfd r q).actions =
          (both (hf c) (server_v V hf lfd) q).actions’
       by simp[sv_after_accept_def, map_def]
  >> ‘acceptedv V (trans (server_v V hf lfd) (h1 ++ [s] ++ h3)) =
      c :: acceptedv V (trans (server_v V hf lfd) R)’
       by simp[acceptedv_acc_CONS, sv_accepted_both, Abbr ‘R’]
  >> ‘¬MEM c (acceptedv V (trans (server_v V hf lfd) R)) ∧
      freshv V (trans (server_v V hf lfd) R)’
       by gvs[freshv_def]
  >> ‘prompt (hf c) L ∧ prompt (server_v V hf lfd) R’
       by (gvs[sv_after_accept_def] >> drule prompt_both >> simp[Abbr ‘L’, Abbr ‘R’])
  (* the rest of the skeleton never touches c *)
  >> ‘¬EXISTS (on_fd_v V c) (trans (server_v V hf lfd) R)’
       by (strip_tac >>
           ‘∀fd hh. EVERY (on_fd_v V fd) (trans (hf fd) hh)’ by metis_tac[hokv_own] >>
           metis_tac[sv_isolates])
  >> Cases_on ‘fd = c’
  (* fd is this connection: it is served by its handler, on L *)
  >- (rpt BasicProvers.VAR_EQ_TAC >> qexistsl_tac [‘LENGTH h1 + 1’, ‘L’]
      >> rpt conj_tac
      >- simp[Abbr ‘L’, LENGTH_views]
      >- (rpt strip_tac >> gvs[Abbr ‘L’, LENGTH_views, sv_views_ready]
          >> simp[EL_APPEND2, EL_CONS, PRE_SUB1, sv_views_ready])
      >- simp[]
      >- (simp[] >> simp[Abbr ‘L’] >> irule sv_filter_both_own
          >> gvs[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM, Abbr ‘R’])
      >- (rpt strip_tac
          >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
               (qspec_then ‘LENGTH h1 + 1 + j’ mp_tac)
          >> simp[] >> strip_tac
          >> ‘TAKE j L = left_view (hf c) (server_v V hf lfd) (TAKE j h3)’
               by simp[Abbr ‘L’, views_TAKE]
          >> pop_assum SUBST1_TAC >> irule sv_filter_both_own >> simp[]
          >> simp[views_TAKE] >> irule untouched_v_TAKE
          >> gs[hokv_wf_server_v, Abbr ‘R’])
      >- (rpt strip_tac
          >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
               (qspec_then ‘LENGTH h1 + 1 + j’ mp_tac)
          >> simp[sv_nreads_both, views_TAKE]
          >> strip_tac >> irule nreadsv_sv_untouched >> fs[])
      >> rpt strip_tac >> spose_not_then assume_tac
      >> qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac
      >> qpat_x_assum ‘MEM fd (acceptedv _ (trans _ (TAKE _ _)))’ mp_tac
      >> ASM_REWRITE_TAC[MEM])
  (* fd is another connection: it is served inside the rest of the skeleton *)
  >> ‘LENGTH R = LENGTH h3 ∧ ∀i. i < LENGTH h3 ⇒ (EL i R).ready = (EL i h3).ready’
       by simp[Abbr ‘R’, sv_views_ready, LENGTH_views]
  >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘R’ mp_tac)
  >> impl_tac >- simp[] >> impl_tac >- gvs[] >> strip_tac
  >> rename1 ‘a1 + LENGTH g1 = LENGTH R’
  >> qexistsl_tac [‘LENGTH h1 + 1 + a1’, ‘g1’] >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> ‘a1 + i < LENGTH h3’ by simp[]
      >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
  >- simp[]
  >- (‘FILTER (on_fd_v V fd) (trans (both (hf c) (server_v V hf lfd)) h3) =
       FILTER (on_fd_v V fd) (trans (server_v V hf lfd) R)’
        by simp[sv_filter_both_other, Abbr ‘R’]
      >> simp[])
  >- (rpt strip_tac
      >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
           (qspec_then ‘LENGTH h1 + 1 + a1 + j’ mp_tac)
      >> simp[] >> strip_tac
      >> ‘FILTER (on_fd_v V fd) (trans (both (hf c) (server_v V hf lfd)) (TAKE (a1 + j) h3)) =
          FILTER (on_fd_v V fd) (trans (server_v V hf lfd) (TAKE (a1 + j) R))’
           by simp[sv_filter_both_other, Abbr ‘R’, views_TAKE]
      >> simp[])
  >- (rpt strip_tac
      >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’
           (qspec_then ‘LENGTH h1 + 1 + a1 + j’ mp_tac)
      >> simp[sv_nreads_both, views_TAKE, nreadsv_hf_other])
  >> rpt strip_tac >> Cases_on ‘m ≤ LENGTH h1’
  >- (qpat_x_assum ‘∀m. m ≤ LENGTH h1 ⇒ _’ (qspec_then ‘m’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac
      >> qpat_x_assum ‘MEM fd (acceptedv _ (trans _ (TAKE _ _)))’ mp_tac
      >> ASM_REWRITE_TAC[MEM])
  >> qpat_x_assum ‘∀m. LENGTH h1 + 1 ≤ m ⇒ _’ (qspec_then ‘m’ mp_tac)
  >> impl_tac >- simp[] >> strip_tac
  >> ‘MEM fd (acceptedv V (trans (server_v V hf lfd) (TAKE (m − LENGTH h1 − 1) R)))’
       by (qpat_x_assum ‘MEM fd (acceptedv _ (trans _ (TAKE m _)))’ mp_tac
           >> simp[acceptedv_acc_CONS, sv_accepted_both, views_TAKE, Abbr ‘R’])
  >> qpat_x_assum ‘∀m. m ≤ LENGTH R ∧ _ ⇒ _’ (qspec_then ‘m − LENGTH h1 − 1’ mp_tac)
  >> simp[]
QED

(* ------------------------------------------------------------------------
   The listener: the skeleton keeps accepting
   ------------------------------------------------------------------------ *)

(* A fresh skeleton, on a history whose first snapshot has the listener
   readable, accepts straight away *)
Theorem sv_fresh_accepts:
  q ≠ [] ∧ Readable lfd ∈ (HD q).ready ∧ 1 ≤ i ⇒
  1 ≤ nacceptsv V lfd
        (server_v (V : ('act, 'k, 'q, 'res) vocab)
                  (hf : num -> (event, 'res) snapshot list -> ('act, 'z option) outcome)
                  lfd (TAKE i q)).actions
Proof
  Cases_on ‘q’ >> rw[]
  >> drule first_rd_now >> strip_tac
  >> ‘TAKE i (h::t) = h :: TAKE (i - 1) t’ by (Cases_on ‘i’ >> gvs[])
  >> ‘server_v V hf lfd (h :: TAKE (i - 1) t) =
      bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) (TAKE (i - 1) t)’
       by (‘h :: TAKE (i - 1) t = [h] ++ TAKE (i - 1) t’ by simp[] >>
           pop_assum SUBST1_TAC >> irule sv_accepts >> simp[])
  >> ‘∃rest. (bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) (TAKE (i - 1) t)).actions =
             V.acc lfd :: rest’ by MATCH_ACCEPT_TAC bind_emit_starts
  >> asm_rewrite_tac[] >> simp[]
QED

(* After an accept, the skeleton runs on a view hv of the rest of the
   history (the right side of both, if a connection was accepted): hv has
   the same ready sets, and the accepts are hv's *)
Theorem sv_after_accept_view:
  vocab_ok V ∧ hokv V hf ⇒
  prompt (sv_after_accept V hf lfd r) q ⇒
  ∃hv. LENGTH hv = LENGTH q ∧
       (∀i. i < LENGTH q ⇒ (EL i hv).ready = (EL i q).ready) ∧
       prompt (server_v V hf lfd) hv ∧
       ∀j. nacceptsv V lfd (sv_after_accept V hf lfd r (TAKE j q)).actions =
           nacceptsv V lfd (server_v V hf lfd (TAKE j hv)).actions
Proof
  Cases_on ‘vaccd V r’
  >- (rw[sv_after_accept_def] >> qexists_tac ‘q’ >> simp[])
  >> rename1 ‘vaccd V r = SOME c’
  >> rw[sv_after_accept_def] >> qexists_tac ‘right_view (hf c) (server_v V hf lfd) q’
  >> drule prompt_both >> simp[sv_views_ready, LENGTH_views, map_def] >> rpt strip_tac
  >> simp[nacceptsv_def]
  >> ‘count (λa. a = V.acc lfd) (both (hf c) (server_v V hf lfd) (TAKE j q)).actions =
      count (λa. a = V.acc lfd)
        (hf c (left_view (hf c) (server_v V hf lfd) (TAKE j q))).actions +
      count (λa. a = V.acc lfd)
        (server_v V hf lfd (right_view (hf c) (server_v V hf lfd) (TAKE j q))).actions’
       by (irule count_both >> metis_tac[hokv_wf, hokv_wf_server_v])
  >> ‘count (λa. a = V.acc lfd)
        (hf c (left_view (hf c) (server_v V hf lfd) (TAKE j q))).actions = 0’
       by (rw[count_def, FILTER_EQ_NIL, EVERY_MEM] >> strip_tac
           >> drule_all hv_actions_own >> fs[vocab_ok_def])
  >> fs[views_TAKE]
QED

(* MAIN: progress of the listener.  If the listener is readable in two
   snapshots in a row (k, k+1), and the world answers promptly, then the
   skeleton accepts during those rounds (sw_accept_progress, for any
   vocabulary) *)
Theorem sv_accept_progress:
  ∀h k. vocab_ok (V : ('act, 'k, 'q, 'res) vocab) ∧
        hokv V (hf : num -> (event, 'res) snapshot list -> ('act, 'z option) outcome) ∧
        prompt (server_v V hf lfd) h ∧ k + 2 ≤ LENGTH h ∧
        (∀j. k ≤ j ∧ j < k + 2 ⇒ Readable lfd ∈ (EL j h).ready) ⇒
        nacceptsv V lfd (server_v V hf lfd (TAKE k h)).actions <
        nacceptsv V lfd (server_v V hf lfd (TAKE (k + 2) h)).actions
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt strip_tac
  (* the skeleton's first wait ends at the latest in snapshot k *)
  >> qspecl_then [‘k’, ‘h’, ‘lfd’] mp_tac (Q.GENL [‘j’, ‘h’, ‘fd’] first_rd_split)
  >> simp[] >> strip_tac >> gvs[]
  >> Cases_on ‘LENGTH h1 = k + 1’
  (* it ends in snapshot k: the first accept is in round k *)
  >- (‘(server_v V hf lfd (TAKE k (h1 ++ h2))).actions = []’
        by simp[TAKE_before, sv_waiting_actions]
      >> simp[TAKE_after]
      >> ‘server_v V hf lfd (h1 ++ TAKE 1 h2) =
          bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) (TAKE 1 h2)’
           by (irule sv_accepts >> simp[])
      >> pop_assum SUBST1_TAC
      >> ‘∃rest. (bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) (TAKE 1 h2)).actions =
                 V.acc lfd :: rest’ by MATCH_ACCEPT_TAC bind_emit_starts
      >> simp[])
  (* it ends earlier: the skeleton accepts, the response r arrives in s1,
     and the skeleton continues on a view hv of the rest *)
  >> ‘LENGTH h1 ≤ k’ by simp[] >> Cases_on ‘h2’ >- gvs[] >> rename1 ‘h1 ++ s1 :: h3’
  >> ‘h1 ++ s1 :: h3 = h1 ++ [s1] ++ h3’ by simp[] >> pop_assum SUBST_ALL_TAC
  >> drule_all sv_prompt_accept_answered >> strip_tac
  >> ‘∀i. LENGTH h1 + 1 ≤ i ⇒
          nacceptsv V lfd (server_v V hf lfd (TAKE i (h1 ++ [s1] ++ h3))).actions =
          1 + nacceptsv V lfd (sv_after_accept V hf lfd r (TAKE (i − LENGTH h1 − 1) h3)).actions’
       by (rpt strip_tac >> simp[TAKE_after_cons]
           >> qspecl_then [‘lfd’, ‘h1’, ‘s1’, ‘r’, ‘TAKE (i − (LENGTH h1 + 1)) h3’] mp_tac
                (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] sv_after_accept_actions)
           >> simp[])
  >> ‘nacceptsv V lfd (server_v V hf lfd (TAKE (LENGTH h1) (h1 ++ [s1] ++ h3))).actions = 1’
       by (‘TAKE (LENGTH h1) (h1 ++ [s1] ++ h3) = h1 ++ []’ by simp[TAKE_APPEND1]
           >> pop_assum SUBST1_TAC
           >> ‘server_v V hf lfd (h1 ++ []) =
               bind (emit (V.acc lfd)) (sv_after_accept V hf lfd) []’
                by (irule sv_accepts >> simp[])
           >> pop_assum SUBST1_TAC >> simp[bind_emit_NIL])
  >> drule_all prompt_sv_after_accept >> strip_tac
  >> drule_all sv_after_accept_view >> strip_tac
  >> Cases_on ‘LENGTH h1 + 1 ≤ k’
  (* the window starts after the restart: by induction *)
  >- (qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘hv’ mp_tac) >> simp[]
      >> disch_then (qspec_then ‘k − LENGTH h1 − 1’ mp_tac)
      >> impl_tac
      >- (conj_tac >- fs[]
          >> rpt strip_tac >> ‘j < LENGTH h3’ by fs[] >> simp[]
          >> qpat_x_assum ‘∀j. k ≤ j ∧ _ ⇒ _’ (qspec_then ‘j + LENGTH h1 + 1’ mp_tac)
          >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
      >> ‘k − LENGTH h1 − 1 + 2 = k + 1 − LENGTH h1 ∧
          k − LENGTH h1 − 1 = k − (LENGTH h1 + 1)’ by simp[]
      >> simp[])
  (* the restart is in the window: the restarted skeleton accepts at once *)
  >> ‘k = LENGTH h1’ by simp[] >> gvs[]
  >> ‘hv ≠ [] ∧ Readable lfd ∈ (HD hv).ready’
       by (Cases_on ‘hv’ >> gvs[] >> Cases_on ‘h3’ >> gvs[]
           >> qpat_x_assum ‘∀j. _ ≤ j ∧ _ ⇒ _’ (qspec_then ‘LENGTH h1 + 1’ mp_tac)
           >> qpat_x_assum ‘∀i. _ ⇒ _’ (qspec_then ‘0’ mp_tac)
           >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
  >> qspecl_then [‘hv’, ‘lfd’, ‘1’] mp_tac (Q.GENL [‘q’, ‘lfd’, ‘i’] sv_fresh_accepts)
  >> simp[]
QED

(* ------------------------------------------------------------------------
   The identity vocabulary: skeletonProgress's theorems, unchanged
   ------------------------------------------------------------------------ *)

(* sw_handler_view's statement, as the idV instance of sv_handler_view *)
Theorem sw_handler_view_from_v:
  ∀h. hok hf ∧ fresh (trans (server_with hf lfd) h) ∧ prompt (server_with hf lfd) h ∧
      MEM fd (accepted (trans (server_with hf lfd) h)) ⇒
      ∃a g. LENGTH g + a = LENGTH h ∧
            (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) h).ready) ∧
            prompt (hf fd) g ∧
            FILTER (on_fd fd) (trans (server_with hf lfd) h) = trans (hf fd) g ∧
            (∀j. j ≤ LENGTH g ⇒
                 FILTER (on_fd fd) (trans (server_with hf lfd) (TAKE (a + j) h)) =
                 trans (hf fd) (TAKE j g)) ∧
            (∀j. j ≤ LENGTH g ⇒
                 nreads fd (server_with hf lfd (TAKE (a + j) h)).actions =
                 nreads fd (hf fd (TAKE j g)).actions) ∧
            (∀m. m ≤ LENGTH h ∧ MEM fd (accepted (trans (server_with hf lfd) (TAKE m h))) ⇒
                 a ≤ m)
Proof
  mp_tac (Q.GEN ‘V’ sv_handler_view |> Q.ISPEC ‘idV’ |> INST_TYPE [“:'z” |-> alpha]) >>
  simp[GSYM server_with_eq_v, vocab_ok_idV, hokv_idV, freshv_idV, acceptedv_idV,
       nreadsv_idV, on_fd_v_idV]
QED

(* sw_accept_progress's statement, as the idV instance of
   sv_accept_progress *)
Theorem sw_accept_progress_from_v:
  ∀h k. hok hf ∧ prompt (server_with hf lfd) h ∧ k + 2 ≤ LENGTH h ∧
        (∀j. k ≤ j ∧ j < k + 2 ⇒ Readable lfd ∈ (EL j h).ready) ⇒
        naccepts lfd (server_with hf lfd (TAKE k h)).actions <
        naccepts lfd (server_with hf lfd (TAKE (k + 2) h)).actions
Proof
  mp_tac (Q.GEN ‘V’ sv_accept_progress |> Q.ISPEC ‘idV’ |> INST_TYPE [“:'z” |-> alpha]) >>
  simp[GSYM server_with_eq_v, vocab_ok_idV, hokv_idV, nacceptsv_idV]
QED
