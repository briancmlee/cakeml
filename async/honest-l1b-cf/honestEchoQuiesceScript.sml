(*
  The echo server falls silent when nothing is ready: after a few
  snapshots in which no event is ready, it emits nothing new and its
  result no longer changes (whatever the results in those snapshots).

  settles d m h: for every q of at least d snapshots with nothing ready,
  m emits nothing in the rounds h ++ q, and m's result after h ++ q is
  its result after the first d of them.  Each combinator keeps it (wait
  at 0, emit at 1, map, bind adding the bounds, both taking the larger);
  the echo's handler and server settle at a constant bound on every
  history (by induction on the history's length).

  For SQ (L3-09): once L1's live fds are drained, the PF loop's snapshots
  have nothing ready (with dead handles dropped from the interest list,
  design option (C)).

  MAIN: handler_settles, server_settles.
*)
Theory honestEchoQuiesce
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncServer asyncProgress
Libs
  preamble

Definition noready_def:
  noready (q : ('e, 'r) snapshot list) ⇔ EVERY (λs. s.ready = {}) q
End

Theorem noready_simps[simp]:
  (noready [] ⇔ T) ∧ (noready (s :: q) ⇔ s.ready = {} ∧ noready q) ∧
  (noready (q1 ++ q2) ⇔ noready q1 ∧ noready q2)
Proof
  simp[noready_def]
QED

Theorem noready_TAKE_DROP[simp]:
  noready q ⇒ noready (TAKE n q) ∧ noready (DROP n q)
Proof
  rw[noready_def] >> metis_tac[EVERY_TAKE, EVERY_DROP]
QED

Definition settles_def:
  settles d m h ⇔
    ∀q. noready q ∧ d ≤ LENGTH q ⇒
        new_actions (log_of m) (h ++ q) = [] ∧
        (m (h ++ q)).result = (m (h ++ TAKE d q)).result
End

Theorem settles_mono:
  settles d m h ∧ d ≤ d' ⇒ settles d' m h
Proof
  rw[settles_def] >>
  first_assum (qspec_then ‘q’ mp_tac) >> (impl_tac >- simp[]) >> strip_tac >> simp[] >>
  first_x_assum (qspec_then ‘TAKE d' q’ mp_tac) >> simp[LENGTH_TAKE, TAKE_TAKE]
QED

(* ------------------------------------------------------------------------
   The primitives
   ------------------------------------------------------------------------ *)

Theorem first_some_noready[local]:
  (∀s. s.ready = {} ⇒ p s = NONE) ⇒
  ∀q. noready q ⇒ first_some p (h ++ q) = first_some p h
Proof
  strip_tac >> Induct_on ‘h’ >> simp[first_some_def] >>
  Induct >> simp[first_some_def]
QED

Theorem wait_settles:
  (∀s. s.ready = {} ⇒ p s = NONE) ⇒ settles 0 (wait p) h
Proof
  rw[settles_def, wait_def, new_actions_def, log_of_def] >>
  drule first_some_noready >> simp[]
QED

Theorem emit_settles:
  settles 1 (emit a) h
Proof
  rw[settles_def, emit_def, new_actions_def, log_of_def] >>
  Cases_on ‘h’ >> Cases_on ‘q’ >> gvs[]
QED

Theorem return_settles:
  settles 0 (return x) h
Proof
  rw[settles_def, return_def, new_actions_def, log_of_def]
QED

Theorem map_settles:
  settles d m h ⇒ settles d (map f m) h
Proof
  simp[settles_def, asyncLevel1Theory.log_of_map] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘q’ mp_tac) >> simp[asyncLevel1Theory.map_def]
QED

(* ------------------------------------------------------------------------
   bind
   ------------------------------------------------------------------------ *)

Theorem skip_TAKE[local]:
  TAKE n (skip_results k q) = skip_results k (TAKE n q)
Proof
  Cases_on ‘q’ >> Cases_on ‘n’ >> simp[skip_results_def]
QED

Theorem noready_skip[local,simp]:
  noready (skip_results k q) ⇔ noready q
Proof
  Cases_on ‘q’ >> simp[skip_results_def]
QED

Theorem LENGTH_skip[local,simp]:
  LENGTH (skip_results k q) = LENGTH q
Proof
  Cases_on ‘q’ >> simp[skip_results_def]
QED

(* The continuation's history, after the rest of h *)
Theorem skip_split[local]:
  ∃q'. skip_results k (h2 ++ q) = skip_results k h2 ++ q' ∧ noready q' = noready q ∧
       LENGTH q' = LENGTH q ∧ ∀j. skip_results k (h2 ++ TAKE j q) = skip_results k h2 ++ TAKE j q'
Proof
  Cases_on ‘h2’ >> simp[skip_results_def]
  >- simp[skip_TAKE]
QED

Theorem running_new_actions[local]:
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒
  new_actions (log_of (bind m f)) h = new_actions (log_of m) h
Proof
  strip_tac >> drule bind_running_TAKE >> strip_tac >>
  Cases_on ‘h’ using SNOC_CASES
  >- (first_x_assum (qspecl_then [‘f’, ‘0’] mp_tac) >> simp[new_actions_NIL, log_of_def]) >>
  simp[new_actions_SNOC, log_of_def, SNOC_APPEND] >>
  first_assum (qspecl_then [‘f’, ‘LENGTH l’] mp_tac) >>
  first_x_assum (qspecl_then [‘f’, ‘SUC (LENGTH l)’] mp_tac) >>
  simp[SNOC_APPEND, TAKE_LENGTH_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

(* m, settled after d snapshots, finishes within them or not at all *)
Theorem settles_finish_bound[local]:
  settles d m h ∧ noready q1 ∧ first_done m (h ++ q1) x ∧
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒ LENGTH q1 ≤ d
Proof
  CCONTR_TAC >> fs[NOT_LESS_EQUAL, settles_def] >>
  first_x_assum (qspec_then ‘q1’ mp_tac) >> simp[] >>
  fs[first_done_def] >>
  qpat_x_assum ‘∀n. n < _ ⇒ _’ (qspec_then ‘LENGTH h + d’ mp_tac) >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

(* Use the settles assumption matching pat, at the snapshots q *)
fun use_settles pat q =
  qpat_assum pat (mp_tac o REWRITE_RULE [settles_def]) >>
  disch_then (qspec_then q mp_tac);

Theorem TAKE_APPEND_ADD[local]:
  TAKE (LENGTH h + j) (h ++ q) = h ++ TAKE j q
Proof
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem bind_settles:
  wf m ∧ settles d1 m h ∧
  (∀x n. n ≤ LENGTH h ∧ first_done m (TAKE n h) x ⇒
         settles d2a (f x)
           (skip_results (LENGTH (new_actions (log_of m) (TAKE n h))) (DROP n h))) ∧
  (∀x q. noready q ∧ first_done m (h ++ q) x ⇒ settles d2b (f x) []) ∧
  d1 + d2b ≤ D ∧ d2a ≤ D ⇒
  settles D (bind m f) h
Proof
  strip_tac >> REWRITE_TAC [settles_def] >> gen_tac >> strip_tac >>
  qspecl_then [‘m’, ‘h’] strip_assume_tac history_split
  >- ((* m still runs on h *)
      qspecl_then [‘m’, ‘h ++ q’] strip_assume_tac history_split
      >- ((* and on h ++ q *)
          ‘new_actions (log_of (bind m f)) (h ++ q) = new_actions (log_of m) (h ++ q)’
            by (irule running_new_actions >> simp[]) >>
          ‘new_actions (log_of m) (h ++ q) = []’ by fs[settles_def] >>
          ‘∀n. n ≤ LENGTH (h ++ TAKE D q) ⇒
               (m (TAKE n (h ++ TAKE D q))).result = NONE’
            by (rpt strip_tac >>
                ‘h ++ TAKE D q = TAKE (LENGTH h + D) (h ++ q)’
                  by simp[TAKE_APPEND_ADD] >>
                pop_assum SUBST1_TAC >> simp[TAKE_TAKE_MIN] >>
                first_x_assum irule >> fs[]) >>
          drule bind_running >>
          qpat_x_assum ‘∀n. n ≤ LENGTH (h ++ q) ⇒ _’ assume_tac >>
          drule bind_running >> simp[]) >>
      (* m first finishes after h ++ q1, q = q1 ++ h2 *)
      ‘LENGTH h < LENGTH h1’
        by (CCONTR_TAC >> fs[NOT_LESS] >>
            ‘TAKE (LENGTH h1) (h ++ q) = h1’
              by (qpat_x_assum ‘h ++ q = _’ SUBST1_TAC >> simp[TAKE_LENGTH_APPEND]) >>
            ‘TAKE (LENGTH h1) h = h1’ by metis_tac[TAKE_APPEND1] >>
            fs[first_done_def] >>
            qpat_x_assum ‘∀n. n ≤ LENGTH h ⇒ _’ (qspec_then ‘LENGTH h1’ mp_tac) >> simp[]) >>
      ‘∃q1. h1 = h ++ q1 ∧ q = q1 ++ h2’
        by (qpat_x_assum ‘h ++ q = _’ mp_tac >> rw[APPEND_EQ_APPEND] >> gvs[]) >>
      gvs[] >>
      ‘LENGTH q1 ≤ d1’ by (irule settles_finish_bound >> simp[] >> metis_tac[]) >>
      ‘settles d2b (f x) []’
        by (qpat_x_assum ‘∀x q. noready q ∧ _ ⇒ _’ irule >> qexists_tac ‘q1’ >> simp[]) >>
      qabbrev_tac ‘k0 = LENGTH (new_actions (log_of m) (h ++ q1))’ >>
      conj_tac
      >- (Cases_on ‘h2 = []’
          >- (gvs[] >>
              ‘new_actions (log_of m) (h ++ q1) = []’
                by (use_settles ‘settles d1 m h’ ‘q1’ >> fs[]) >>
              ‘(f x []).actions = []’
                by (use_settles ‘settles d2b (f x) []’ ‘[]’ >>
                    fs[new_actions_NIL, log_of_def]) >>
              qspecl_then [‘m’, ‘h ++ q1’, ‘x’, ‘f’] mp_tac
                (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’] new_actions_bind_at) >> fs[]) >>
          ‘h ++ (q1 ++ h2) = (h ++ q1) ++ h2’ by simp[] >> pop_assum SUBST1_TAC >>
          drule new_actions_bind_after >> disch_then (qspecl_then [‘h2’, ‘f’] mp_tac) >>
          simp[] >> strip_tac >>
          use_settles ‘settles d2b (f x) []’ ‘skip_results k0 h2’ >> fs[]) >>
      ‘h ++ (q1 ++ h2) = (h ++ q1) ++ h2 ∧
       h ++ TAKE D (q1 ++ h2) = (h ++ q1) ++ TAKE (D − LENGTH q1) h2’
        by simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
      ASM_REWRITE_TAC [] >>
      drule_then (qspecl_then [‘f’, ‘h2’] SUBST1_TAC) bind_continues_result >>
      drule_then (qspecl_then [‘f’, ‘TAKE (D − LENGTH q1) h2’] SUBST1_TAC)
        bind_continues_result >>
      qunabbrev_tac ‘k0’ >>
      qabbrev_tac ‘j = D − LENGTH q1’ >>
      ‘d2b ≤ LENGTH h2 ∧ d2b ≤ j ∧ j ≤ LENGTH h2’ by fs[Abbr ‘j’] >>
      qabbrev_tac ‘k1 = LENGTH (new_actions (log_of m) (h ++ q1))’ >>
      use_settles ‘settles d2b (f x) []’ ‘skip_results k1 h2’ >>
      impl_tac >- (simp[] >> ASM_REWRITE_TAC []) >> strip_tac >>
      use_settles ‘settles d2b (f x) []’ ‘skip_results k1 (TAKE j h2)’ >>
      impl_tac >- (simp[LENGTH_TAKE] >> ASM_REWRITE_TAC []) >> strip_tac >>
      ‘TAKE d2b (TAKE j h2) = TAKE d2b h2’ by simp[TAKE_TAKE] >>
      fs[skip_TAKE]) >>
  (* m finished within h, after h1 *)
  gvs[] >>
  ‘TAKE (LENGTH h1) (h1 ++ h2) = h1 ∧ DROP (LENGTH h1) (h1 ++ h2) = h2’
    by simp[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  qabbrev_tac ‘k0 = LENGTH (new_actions (log_of m) h1)’ >>
  ‘settles d2a (f x) (skip_results k0 h2)’
    by (qpat_x_assum ‘∀x n. _ ⇒ _’ (qspecl_then [‘x’, ‘LENGTH h1’] mp_tac) >> simp[]) >>
  qspecl_then [‘k0’, ‘h2’, ‘q’] strip_assume_tac (Q.GENL [‘k’, ‘h2’, ‘q’] skip_split) >>
  conj_tac
  >- (qpat_x_assum ‘∀j. _’ kall_tac >>
      Cases_on ‘h2 ++ q = []’
      >- (‘h2 = [] ∧ q = []’ by metis_tac[APPEND_eq_NIL] >>
          ‘D = 0 ∧ d1 = 0 ∧ d2a = 0’
            by (qpat_x_assum ‘D ≤ LENGTH q’ mp_tac >> qpat_x_assum ‘d1 + d2b ≤ D’ mp_tac >>
                qpat_x_assum ‘d2a ≤ D’ mp_tac >> ASM_REWRITE_TAC [LENGTH] >> simp[]) >>
          ‘new_actions (log_of m) h1 = []’
            by (use_settles ‘settles d1 m _’ ‘[]’ >> ASM_REWRITE_TAC [APPEND_NIL, LENGTH] >>
                simp[]) >>
          ‘(f x []).actions = []’
            by (qpat_x_assum ‘settles d2a (f x) _’ mp_tac >>
                ASM_REWRITE_TAC [skip_results_def, settles_def] >>
                disch_then (qspec_then ‘[]’ mp_tac) >>
                simp[new_actions_NIL, log_of_def]) >>
          qspecl_then [‘m’, ‘h1’, ‘x’, ‘f’] mp_tac
            (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’] new_actions_bind_at) >>
          ASM_REWRITE_TAC [APPEND_NIL, APPEND]) >>
      ‘h1 ++ h2 ++ q = h1 ++ (h2 ++ q)’ by simp[] >> pop_assum SUBST1_TAC >>
      drule new_actions_bind_after >> disch_then (qspecl_then [‘h2 ++ q’, ‘f’] mp_tac) >>
      simp[] >> strip_tac >>
      use_settles ‘settles d2a (f x) _’ ‘q'’ >> fs[]) >>
  ‘h1 ++ h2 ++ q = h1 ++ (h2 ++ q) ∧
   h1 ++ h2 ++ TAKE D q = h1 ++ (h2 ++ TAKE D q)’ by simp[] >>
  ASM_REWRITE_TAC [] >>
  drule_then (qspecl_then [‘f’, ‘h2 ++ q’] SUBST1_TAC) bind_continues_result >>
  drule_then (qspecl_then [‘f’, ‘h2 ++ TAKE D q’] SUBST1_TAC) bind_continues_result >>
  ASM_REWRITE_TAC [] >>
  ‘d2a ≤ LENGTH q' ∧ d2a ≤ D ∧ D ≤ LENGTH q'’ by fs[] >>
  use_settles ‘settles d2a (f x) _’ ‘q'’ >>
  impl_tac >- ASM_REWRITE_TAC [] >> strip_tac >>
  use_settles ‘settles d2a (f x) _’ ‘TAKE D q'’ >>
  impl_tac >- (simp[LENGTH_TAKE] >> metis_tac[noready_TAKE_DROP]) >> strip_tac >>
  ‘TAKE d2a (TAKE D q') = TAKE d2a q'’ by simp[TAKE_TAKE] >>
  fs[]
QED

(* ------------------------------------------------------------------------
   both
   ------------------------------------------------------------------------ *)

Theorem views_TAKE[local]:
  ∀H n. left_view m1 m2 (TAKE n H) = TAKE n (left_view m1 m2 H) ∧
        right_view m1 m2 (TAKE n H) = TAKE n (right_view m1 m2 H)
Proof
  Induct_on ‘H’ using SNOC_INDUCT >> simp[] >> rpt gen_tac >>
  simp[SNOC_APPEND] >>
  Cases_on ‘n ≤ LENGTH H’
  >- (simp[TAKE_APPEND1] >>
      qspecl_then [‘m1’, ‘m2’, ‘H’, ‘x’] strip_assume_tac (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’] left_view_SNOC) >>
      qspecl_then [‘m1’, ‘m2’, ‘H’, ‘x’] strip_assume_tac (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’] right_view_SNOC) >>
      simp[TAKE_APPEND1]) >>
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem noready_world[local]:
  ∀a b. MAP (λs. (s.ready, s.now)) a = MAP (λs. (s.ready, s.now)) b ⇒ (noready a ⇔ noready b)
Proof
  Induct >> Cases_on ‘b’ >> rw[] >> metis_tac[]
QED

Theorem both_new_actions_all[local]:
  new_actions (log_of (both m1 m2)) h =
    new_actions (log_of m1) (left_view m1 m2 h) ++ new_actions (log_of m2) (right_view m1 m2 h)
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, both_def, par_log_def, par_actions_NIL] >>
  simp[SNOC_APPEND, both_new_actions]
QED

(* The views of h ++ q: those of h, then views of q with nothing ready *)
Theorem views_append[local]:
  noready q ⇒
  ∃ql qr. left_view m1 m2 (h ++ q) = left_view m1 m2 h ++ ql ∧
          right_view m1 m2 (h ++ q) = right_view m1 m2 h ++ qr ∧
          noready ql ∧ noready qr ∧ LENGTH ql = LENGTH q ∧ LENGTH qr = LENGTH q ∧
          ∀j. left_view m1 m2 (h ++ TAKE j q) = left_view m1 m2 h ++ TAKE j ql ∧
              right_view m1 m2 (h ++ TAKE j q) = right_view m1 m2 h ++ TAKE j qr
Proof
  strip_tac >>
  qabbrev_tac ‘L = left_view m1 m2 h’ >> qabbrev_tac ‘R = right_view m1 m2 h’ >>
  qabbrev_tac ‘LQ = left_view m1 m2 (h ++ q)’ >> qabbrev_tac ‘RQ = right_view m1 m2 (h ++ q)’ >>
  ‘LENGTH L = LENGTH h ∧ LENGTH R = LENGTH h ∧ LENGTH LQ = LENGTH h + LENGTH q ∧
   LENGTH RQ = LENGTH h + LENGTH q’ by simp[Abbr ‘L’, Abbr ‘R’, Abbr ‘LQ’, Abbr ‘RQ’] >>
  ‘TAKE (LENGTH h) LQ = L ∧ TAKE (LENGTH h) RQ = R’
    by (qspecl_then [‘h ++ q’, ‘LENGTH h’] mp_tac views_TAKE >>
        simp[TAKE_LENGTH_APPEND, Abbr ‘L’, Abbr ‘R’, Abbr ‘LQ’, Abbr ‘RQ’]) >>
  ‘MAP (λs. (s.ready, s.now)) LQ = MAP (λs. (s.ready, s.now)) (h ++ q) ∧
   MAP (λs. (s.ready, s.now)) RQ = MAP (λs. (s.ready, s.now)) (h ++ q)’
    by simp[Abbr ‘LQ’, Abbr ‘RQ’, both_views_world] >>
  qexistsl [‘DROP (LENGTH h) LQ’, ‘DROP (LENGTH h) RQ’] >>
  rpt conj_tac
  >- metis_tac[TAKE_DROP]
  >- metis_tac[TAKE_DROP]
  >- (qspecl_then [‘DROP (LENGTH h) LQ’, ‘q’] mp_tac noready_world >>
      impl_tac >- (simp[MAP_DROP] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
      simp[])
  >- (qspecl_then [‘DROP (LENGTH h) RQ’, ‘q’] mp_tac noready_world >>
      impl_tac >- (simp[MAP_DROP] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
      simp[])
  >- simp[]
  >- simp[]
  >> gen_tac >>
  ‘h ++ TAKE j q = TAKE (LENGTH h + j) (h ++ q)’ by simp[TAKE_APPEND_ADD] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘h ++ q’, ‘LENGTH h + j’] mp_tac views_TAKE >>
  simp[Abbr ‘LQ’, Abbr ‘RQ’] >> strip_tac >>
  ‘left_view m1 m2 (h ++ q) = L ++ DROP (LENGTH h) (left_view m1 m2 (h ++ q)) ∧
   right_view m1 m2 (h ++ q) = R ++ DROP (LENGTH h) (right_view m1 m2 (h ++ q))’
    by metis_tac[TAKE_DROP] >>
  qabbrev_tac ‘X = DROP (LENGTH h) (left_view m1 m2 (h ++ q))’ >>
  qabbrev_tac ‘Y = DROP (LENGTH h) (right_view m1 m2 (h ++ q))’ >>
  ASM_REWRITE_TAC [] >> fs[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem both_settles:
  settles d m1 (left_view m1 m2 h) ∧ settles d m2 (right_view m1 m2 h) ⇒
  settles d (both m1 m2) h
Proof
  REWRITE_TAC [settles_def] >> rpt strip_tac >>
  qspecl_then [‘m1’, ‘m2’, ‘h’, ‘q’] mp_tac (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘q’] views_append) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then ‘qr’ mp_tac) >> first_x_assum (qspec_then ‘ql’ mp_tac) >>
  simp[] >> rpt strip_tac >>
  simp[both_new_actions_all, both_def]
QED

(* ------------------------------------------------------------------------
   The echo's handler and server
   ------------------------------------------------------------------------ *)

Theorem readable_settles[local]:
  settles 0 (readable fd) h
Proof
  simp[readable_def] >> irule wait_settles >> simp[]
QED

(* With nothing ready, readable never fires *)
Theorem readable_noready[local]:
  noready q ⇒ ¬first_done (readable fd) q x
Proof
  rpt strip_tac >>
  ‘(readable fd q).result = NONE’
    by (qspecl_then [‘fd’, ‘[]’] mp_tac (Q.GENL [‘fd’, ‘h’] readable_settles) >>
        rw[settles_def] >> first_x_assum (qspec_then ‘q’ mp_tac) >>
        simp[readable_def, wait_def, first_some_def]) >>
  fs[first_done_def]
QED

Theorem readable_facts[local]:
  wf (readable fd) ∧ (readable fd []).result = NONE
Proof
  simp[readable_def, wf_wait, wait_def, first_some_def]
QED

Theorem emit_facts[local]:
  wf (emit a) ∧ (emit a []).result = NONE
Proof
  simp[wf_emit, emit_def]
QED

(* Fresh: waiting for readable does nothing *)
Theorem readable_bind_nil[local]:
  settles 0 (bind (readable fd) g) []
Proof
  irule (Q.INST [‘d2a’ |-> ‘0’, ‘d2b’ |-> ‘0’] bind_settles) >>
  simp[readable_facts, readable_settles] >>
  rpt conj_tac >> TRY (simp[first_done_def, readable_facts] >> NO_TAC) >>
  metis_tac[readable_noready]
QED

(* Fresh: an emit, then g *)
Theorem emit_bind_nil[local]:
  (∀x. settles d (g x) []) ⇒ settles (1 + d) (bind (emit a) g) []
Proof
  strip_tac >> irule (Q.INST [‘d2a’ |-> ‘0’] bind_settles) >>
  simp[emit_facts] >> conj_tac >- simp[first_done_def, emit_def] >>
  qexistsl [‘1’, ‘d’] >> simp[emit_settles]
QED

Theorem handler_nil[local]:
  settles 0 (handler fd) []
Proof
  simp[Once handler_steps, readable_bind_nil]
QED

Theorem server_nil[local]:
  settles 0 (server lfd) []
Proof
  simp[Once server_unfold, readable_bind_nil]
QED

Theorem after_read_nil[local]:
  settles 1 (after_read fd res) []
Proof
  Cases_on ‘res’ >> simp[after_read_def]
  >> TRY (irule settles_mono >> qexists_tac ‘0’ >> simp[handler_nil, return_settles] >> NO_TAC)
  >> ‘settles (1 + 0) (bind (emit (Write fd s)) (λw. handler fd)) []’
       by (irule emit_bind_nil >> simp[handler_nil]) >> fs[]
QED

Theorem handler_settles:
  ∀h. settles 2 (handler fd) h
Proof
  ‘∀n h. LENGTH h = n ⇒ settles 2 (handler fd) h’ suffices_by metis_tac[] >>
  completeInduct_on ‘n’ >> rpt strip_tac >>
  ONCE_REWRITE_TAC [handler_steps] >>
  irule (Q.INST [‘d1’ |-> ‘0’, ‘d2a’ |-> ‘2’, ‘d2b’ |-> ‘2’] bind_settles) >>
  simp[readable_facts, readable_settles] >> rpt conj_tac
  >- ((* fresh after readable: the read, then after_read *)
      rpt strip_tac >>
      ‘settles (1 + 1) (bind (emit (Read fd)) (after_read fd)) []’
        by (irule emit_bind_nil >> simp[after_read_nil]) >> fs[]) >>
  (* readable finished within h, after n' ≥ 1 snapshots *)
  rpt strip_tac >>
  ‘n' ≠ 0’ by (strip_tac >> gvs[first_done_def, readable_facts]) >>
  irule (Q.INST [‘d1’ |-> ‘1’, ‘d2a’ |-> ‘2’, ‘d2b’ |-> ‘1’] bind_settles) >>
  simp[emit_facts, emit_settles, after_read_nil] >>
  rpt strip_tac >>
  Cases_on ‘x’ >> simp[after_read_def]
  >> TRY (irule settles_mono >> qexists_tac ‘0’ >> simp[return_settles] >> NO_TAC)
  >> TRY (first_x_assum irule >> simp[LENGTH_DROP] >> NO_TAC) >>
  irule (Q.INST [‘d1’ |-> ‘1’, ‘d2a’ |-> ‘2’, ‘d2b’ |-> ‘0’] bind_settles) >>
  simp[emit_facts, emit_settles, handler_nil] >>
  rpt strip_tac >> first_x_assum irule >> simp[LENGTH_DROP]
QED

(* The server's continuation after its Accept, fresh *)
Theorem accept_cont_nil[local]:
  settles 1 (case res of
               Accepted fd => map (λp. ()) (both (handler fd) (server lfd))
             | _ => server lfd) []
Proof
  Cases_on ‘res’ >> simp[]
  >> TRY (irule settles_mono >> qexists_tac ‘0’ >> simp[server_nil] >> NO_TAC) >>
  irule map_settles >> irule both_settles >> simp[] >>
  conj_tac >> irule settles_mono >> qexists_tac ‘0’ >> simp[handler_nil, server_nil]
QED

Theorem server_settles:
  ∀h. settles 2 (server lfd) h
Proof
  ‘∀n h. LENGTH h = n ⇒ settles 2 (server lfd) h’ suffices_by metis_tac[] >>
  completeInduct_on ‘n’ >> rpt strip_tac >>
  ONCE_REWRITE_TAC [server_unfold] >>
  irule (Q.INST [‘d1’ |-> ‘0’, ‘d2a’ |-> ‘2’, ‘d2b’ |-> ‘2’] bind_settles) >>
  simp[readable_facts, readable_settles] >> rpt conj_tac
  >- ((* fresh after readable: the accept, then its continuation *)
      rpt strip_tac >>
      ‘settles (1 + 1) (bind (emit (Accept lfd))
         (λres. case res of
                  Accepted fd => map (λp. ()) (both (handler fd) (server lfd))
                | _ => server lfd)) []’
        by (irule emit_bind_nil >> simp[accept_cont_nil]) >> fs[]) >>
  rpt strip_tac >>
  ‘n' ≠ 0’ by (strip_tac >> gvs[first_done_def, readable_facts]) >>
  irule (Q.INST [‘d1’ |-> ‘1’, ‘d2a’ |-> ‘2’, ‘d2b’ |-> ‘1’] bind_settles) >>
  simp[emit_facts, emit_settles, accept_cont_nil] >>
  rpt strip_tac >>
  Cases_on ‘x’ >> simp[]
  >> TRY (first_x_assum irule >> simp[LENGTH_DROP] >> NO_TAC) >>
  irule map_settles >> irule both_settles >> simp[handler_settles] >>
  first_x_assum irule >> simp[LENGTH_DROP]
QED
