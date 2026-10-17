(*
  bquiet for the echo server: an empty snapshot (nothing ready, no
  results, time 0), shown to a computation that emits nothing new, is a
  stutter: the computation behaves afterwards exactly as without it.

  stut_at m h k: if m emits nothing new after h, then
                 m (h ++ [es] ++ k) = m (h ++ k).
  Each combinator keeps it, given it for its parts on the same or
  shorter histories (wait_stut, emit_stut, map_stut, bind_stut,
  both_stut); the echo's handler and server have it on every history, by
  induction on the history's length (their recursive calls come after a
  snapshot).  Then the socket-vocabulary server has it (relabelling maps
  the empty snapshot to the empty snapshot), and bquiet follows.

  MAIN: server_stut, echo_bquiet.
*)
Theory honestEchoL0BStutter
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncServer asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  asyncM4Loop asyncM3World honestL1BSim
Libs
  preamble

(* The empty snapshot *)
Definition es_def:
  es = <| ready := {}; now := 0; results := [] |>
End

Theorem es_results[simp]:
  es.results = [] ∧ es.ready = {} ∧ es.now = 0
Proof
  simp[es_def]
QED

Theorem es_with_results[simp]:
  es with results := [] = es
Proof
  simp[es_def, snapshot_component_equality]
QED

Definition stut_at_def:
  stut_at m h k ⇔ (new_actions (log_of m) h = [] ⇒ m (h ++ [es] ++ k) = m (h ++ k))
End

(* A stutter changes no round's new actions *)
Theorem new_actions_stut_le:
  (∀k'. LENGTH k' ≤ LENGTH k ⇒ stut_at m h k') ∧ new_actions (log_of m) h = [] ⇒
  new_actions (log_of m) (h ++ [es] ++ k) = new_actions (log_of m) (h ++ k)
Proof
  rw[stut_at_def] >>
  Cases_on ‘k’ using SNOC_CASES
  >- (simp[new_actions_SNOC] >>
      first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[] >> strip_tac >>
      fs[log_of_def, DROP_LENGTH_NIL]) >>
  REWRITE_TAC [SNOC_APPEND] >>
  ‘h ++ [es] ++ (l ++ [x]) = (h ++ [es] ++ l) ++ [x]’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘h ++ (l ++ [x]) = (h ++ l) ++ [x]’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC [new_actions_SNOC, log_of_def] >>
  ‘m (h ++ [es] ++ l) = m (h ++ l) ∧ m (h ++ [es] ++ (l ++ [x])) = m (h ++ (l ++ [x]))’
    by (conj_tac >> qpat_assum ‘∀k'. _’ irule >> fs[]) >>
  fs[]
QED

Theorem new_actions_stut:
  (∀k. stut_at m h k) ∧ new_actions (log_of m) h = [] ⇒
  ∀k. new_actions (log_of m) (h ++ [es] ++ k) = new_actions (log_of m) (h ++ k)
Proof
  rpt strip_tac >> irule new_actions_stut_le >> simp[]
QED

(* ------------------------------------------------------------------------
   The combinators
   ------------------------------------------------------------------------ *)

Theorem first_some_es[local]:
  p es = NONE ⇒ ∀h. first_some p (h ++ [es] ++ k) = first_some p (h ++ k)
Proof
  strip_tac >> Induct >> simp[first_some_def]
QED

Theorem wait_stut:
  p es = NONE ⇒ stut_at (wait p) h k
Proof
  rw[stut_at_def, wait_def, first_some_es]
QED

Theorem emit_stut:
  stut_at (emit a) h k
Proof
  rw[stut_at_def, emit_def] >> Cases_on ‘h’ >> gvs[new_actions_def, log_of_def, emit_def]
QED

Theorem return_stut:
  stut_at (return x) h k
Proof
  rw[stut_at_def, return_def]
QED

Theorem map_stut:
  stut_at m h k ⇒ stut_at (map f m) h k
Proof
  simp[stut_at_def, log_of_map] >> rpt strip_tac >> fs[] >>
  REWRITE_TAC [asyncLevel1Theory.map_def] >> ASM_REWRITE_TAC []
QED

(* bind, while m runs, emits m's new actions *)
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

(* m before the inserted snapshot, and after it, one snapshot on *)
Theorem take_es_m[local]:
  (∀k'. m (h ++ [es] ++ k') = m (h ++ k')) ⇒
  ∀n. m (TAKE n (h ++ [es] ++ k)) = m (TAKE (if n ≤ LENGTH h then n else n − 1) (h ++ k))
Proof
  strip_tac >> gen_tac >> Cases_on ‘n ≤ LENGTH h’ >> simp[]
  >- (REWRITE_TAC [GSYM APPEND_ASSOC] >> simp[TAKE_APPEND1]) >>
  ‘∃j. n = LENGTH h + SUC j’ by (qexists_tac ‘n − LENGTH h − 1’ >> simp[]) >>
  rw[] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  ‘LENGTH h + SUC j − LENGTH h = SUC j ∧ LENGTH h + SUC j − 1 − LENGTH h = j ∧
   LENGTH h ≤ LENGTH h + SUC j − 1’ by simp[] >>
  simp[] >>
  first_x_assum (qspec_then ‘TAKE j k’ mp_tac) >> REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
QED

Theorem skip_results_APPEND[local]:
  h ≠ [] ⇒ skip_results n (h ++ x) = skip_results n h ++ x
Proof
  Cases_on ‘h’ >> simp[skip_results_def]
QED

Theorem LENGTH_skip_results[local,simp]:
  LENGTH (skip_results n h) = LENGTH h
Proof
  Cases_on ‘h’ >> simp[skip_results_def]
QED

Theorem bind_stut:
  wf m ∧ (m []).result = NONE ∧ (∀k'. stut_at m h k') ∧
  (∀x h' k'. LENGTH h' + LENGTH k' < LENGTH h + LENGTH k ⇒ stut_at (f x) h' k') ⇒
  stut_at (bind m f) h k
Proof
  strip_tac >> REWRITE_TAC [stut_at_def] >> strip_tac >>
  qspecl_then [‘m’, ‘h’] strip_assume_tac history_split
  >- ((* m still runs on h *)
      ‘new_actions (log_of m) h = []’ by metis_tac[running_new_actions] >>
      ‘∀k'. m (h ++ [es] ++ k') = m (h ++ k')’ by fs[stut_at_def] >>
      drule take_es_m >> strip_tac >>
      qspecl_then [‘m’, ‘h ++ k’] strip_assume_tac history_split
      >- (‘∀n. n ≤ LENGTH (h ++ [es] ++ k) ⇒ (m (TAKE n (h ++ [es] ++ k))).result = NONE’
            by (rw[] >> first_x_assum (qspec_then ‘k’ kall_tac) >>
                qpat_x_assum ‘∀n. m (TAKE _ _) = _’ (fn th => REWRITE_TAC [th]) >>
                first_x_assum irule >> rw[]) >>
          drule bind_running >> simp[] >> strip_tac >>
          qpat_x_assum ‘∀n. n ≤ LENGTH (h ++ k) ⇒ _’ assume_tac >>
          drule bind_running >> simp[]) >>
      (* m first finishes after h ++ k1, k1 ≠ [] *)
      ‘LENGTH h < LENGTH h1’
        by (CCONTR_TAC >> fs[NOT_LESS] >>
            ‘TAKE (LENGTH h1) (h ++ k) = h1’
              by (qpat_x_assum ‘h ++ k = _’ SUBST1_TAC >> simp[TAKE_LENGTH_APPEND]) >>
            ‘TAKE (LENGTH h1) h = h1’ by metis_tac[TAKE_APPEND1] >>
            fs[first_done_def] >>
            qpat_x_assum ‘∀n. n ≤ LENGTH h ⇒ _’ (qspec_then ‘LENGTH h1’ mp_tac) >> simp[]) >>
      ‘∃k1. h1 = h ++ k1 ∧ k = k1 ++ h2 ∧ k1 ≠ []’
        by (qpat_x_assum ‘h ++ k = _’ mp_tac >> rw[APPEND_EQ_APPEND] >> gvs[] >>
            Cases_on ‘l’ >> gvs[]) >>
      gvs[] >>
      ‘first_done m (h ++ [es] ++ k1) x’
        by (fs[first_done_def] >> rw[] >>
            qpat_x_assum ‘∀k n. m (TAKE _ _) = _’ (fn th => REWRITE_TAC [th]) >>
            first_x_assum irule >> Cases_on ‘k1’ >> fs[] >> rw[]) >>
      ‘new_actions (log_of m) (h ++ [es] ++ k1) = new_actions (log_of m) (h ++ k1)’
        by (irule new_actions_stut >> simp[]) >>
      ‘h ++ [es] ++ (k1 ++ h2) = (h ++ [es] ++ k1) ++ h2 ∧ h ++ (k1 ++ h2) = (h ++ k1) ++ h2’
        by simp[] >>
      ASM_REWRITE_TAC [] >>
      drule_then (qspecl_then [‘f’, ‘h2’] SUBST1_TAC) bind_continues >>
      qpat_x_assum ‘first_done m (h ++ k1) x’ (fn th =>
        REWRITE_TAC [SIMP_RULE std_ss [] (Q.SPECL [‘f’, ‘h2’] (MATCH_MP bind_continues th))]) >>
      simp[] >> metis_tac[]) >>
  (* m finished within h *)
  ‘h1 ≠ []’ by (strip_tac >> gvs[first_done_NIL]) >>
  Cases_on ‘h2 = []’
  >- (gvs[] >>
      drule_all new_actions_bind_at >> disch_then (qspec_then ‘f’ mp_tac) >> simp[] >>
      strip_tac >>
      ‘(f x ([] ++ [es] ++ k)) = f x ([] ++ k)’
        by (qpat_x_assum ‘∀x h' k'. _’ (qspecl_then [‘x’, ‘[]’, ‘k’] mp_tac) >>
            impl_tac >- (Cases_on ‘h’ >> fs[]) >>
            simp[stut_at_def, new_actions_NIL, log_of_def]) >>
      fs[] >>
      drule_then (qspecl_then [‘f’, ‘es :: k’] mp_tac) bind_continues >>
      drule_then (qspecl_then [‘f’, ‘k’] mp_tac) bind_continues >>
      rpt strip_tac >>
      ‘h ++ [es] ++ k = h ++ es :: k’ by simp[] >> pop_assum SUBST1_TAC >>
      ASM_REWRITE_TAC [] >> simp[]) >>
  drule new_actions_bind_after >> disch_then (qspecl_then [‘h2’, ‘f’] mp_tac) >> simp[] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘skip_results k0 h2’ >>
  ‘f x (skip_results k0 h2 ++ [es] ++ k) = f x (skip_results k0 h2 ++ k)’
    by (qpat_x_assum ‘∀x h' k'. _’ (qspecl_then [‘x’, ‘skip_results k0 h2’, ‘k’] mp_tac) >>
        impl_tac >- (Cases_on ‘h1’ >> fs[] >> simp[]) >>
        rw[stut_at_def] >> gvs[]) >>
  ‘h1 ++ h2 ++ [es] ++ k = h1 ++ (h2 ++ [es] ++ k) ∧ h1 ++ h2 ++ k = h1 ++ (h2 ++ k)’ by simp[] >>
  ASM_REWRITE_TAC [] >>
  drule_then (qspecl_then [‘f’, ‘h2 ++ [es] ++ k’] SUBST1_TAC) bind_continues >>
  drule_then (qspecl_then [‘f’, ‘h2 ++ k’] SUBST1_TAC) bind_continues >>
  simp[Abbr ‘k0’, skip_results_APPEND] >>
  ‘skip_results (LENGTH (new_actions (log_of m) h1)) (h2 ++ [es] ++ k) =
   skip_results (LENGTH (new_actions (log_of m) h1)) h2 ++ [es] ++ k’
    by metis_tac[skip_results_APPEND, APPEND_ASSOC] >>
  fs[skip_results_APPEND]
QED

(* ------------------------------------------------------------------------
   both
   ------------------------------------------------------------------------ *)

Theorem both_new_actions_all[local]:
  new_actions (log_of (both m1 m2)) h =
    new_actions (log_of m1) (left_view m1 m2 h) ++ new_actions (log_of m2) (right_view m1 m2 h)
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, both_def, par_log_def, par_actions_NIL] >>
  simp[SNOC_APPEND, both_new_actions]
QED

(* The views, with the empty snapshot inserted: both sides see it, and
   then the same as without it *)
Theorem views_es[local]:
  (∀h' k'. LENGTH h' + LENGTH k' ≤ LENGTH h + LENGTH kk ⇒ stut_at m1 h' k' ∧ stut_at m2 h' k') ∧
  new_actions (log_of m1) (left_view m1 m2 h) = [] ∧
  new_actions (log_of m2) (right_view m1 m2 h) = [] ⇒
  ∀k. LENGTH k ≤ LENGTH kk ⇒
    ∃k1 k2.
      left_view m1 m2 (h ++ [es] ++ k) = left_view m1 m2 h ++ [es] ++ k1 ∧
      left_view m1 m2 (h ++ k) = left_view m1 m2 h ++ k1 ∧
      right_view m1 m2 (h ++ [es] ++ k) = right_view m1 m2 h ++ [es] ++ k2 ∧
      right_view m1 m2 (h ++ k) = right_view m1 m2 h ++ k2 ∧
      LENGTH k1 = LENGTH k ∧ LENGTH k2 = LENGTH k ∧
      par_log m1 m2 (h ++ [es] ++ k) = par_log m1 m2 (h ++ k)
Proof
  strip_tac >> Induct_on ‘k’ using SNOC_INDUCT
  >- (strip_tac >> qexistsl [‘[]’, ‘[]’] >>
      simp[left_view_SNOC_eq, right_view_SNOC_eq, par_log_SNOC] >>
      ‘new_actions (log_of m1) (left_view m1 m2 h ++ [es]) = []’
        by (qspecl_then [‘[]’, ‘m1’, ‘left_view m1 m2 h’] mp_tac
              (Q.GENL [‘k’, ‘m’, ‘h’] new_actions_stut_le) >> simp[] >>
            disch_then irule >>
            first_x_assum (qspecl_then [‘left_view m1 m2 h’, ‘[]’] mp_tac) >> simp[]) >>
      ‘new_actions (log_of m2) (right_view m1 m2 h ++ [es]) = []’
        by (qspecl_then [‘[]’, ‘m2’, ‘right_view m1 m2 h’] mp_tac
              (Q.GENL [‘k’, ‘m’, ‘h’] new_actions_stut_le) >> simp[] >>
            disch_then irule >>
            first_x_assum (qspecl_then [‘right_view m1 m2 h’, ‘[]’] mp_tac) >> simp[]) >>
      simp[left_view_SNOC_eq, right_view_SNOC_eq]) >>
  rpt strip_tac >> fs[SNOC_APPEND] >>
  qabbrev_tac ‘L = left_view m1 m2 h’ >> qabbrev_tac ‘R = right_view m1 m2 h’ >>
  (* the stutter on each side, up to the next round *)
  ‘∀k'. LENGTH k' ≤ LENGTH k + 1 ⇒
        new_actions (log_of m1) (L ++ [es] ++ k') = new_actions (log_of m1) (L ++ k') ∧
        new_actions (log_of m2) (R ++ [es] ++ k') = new_actions (log_of m2) (R ++ k')’
    by (rpt strip_tac
        >- (qspecl_then [‘k'’, ‘m1’, ‘L’] mp_tac (Q.GENL [‘k’, ‘m’, ‘h’] new_actions_stut_le) >>
            simp[] >> disch_then irule >> rpt strip_tac >>
            first_x_assum (qspecl_then [‘L’, ‘k''’] mp_tac) >> simp[Abbr ‘L’])
        >> qspecl_then [‘k'’, ‘m2’, ‘R’] mp_tac (Q.GENL [‘k’, ‘m’, ‘h’] new_actions_stut_le) >>
        simp[] >> disch_then irule >> rpt strip_tac >>
        first_x_assum (qspecl_then [‘R’, ‘k''’] mp_tac) >> simp[Abbr ‘R’]) >>
  qabbrev_tac ‘n1 = LENGTH (new_actions (log_of m1) (L ++ k1))’ >>
  qexistsl [‘k1 ++ [x with results := TAKE n1 x.results]’,
            ‘k2 ++ [x with results := DROP n1 x.results]’] >>
  ‘h ++ [es] ++ (k ++ [x]) = (h ++ [es] ++ k) ++ [x] ∧ h ++ (k ++ [x]) = (h ++ k) ++ [x]’
    by simp[] >>
  ASM_REWRITE_TAC [] >>
  REWRITE_TAC [left_view_SNOC_eq, right_view_SNOC_eq, par_log_SNOC] >>
  ASM_REWRITE_TAC [] >>
  ‘new_actions (log_of m1) (L ++ [es] ++ k1) = new_actions (log_of m1) (L ++ k1)’
    by (first_x_assum (qspec_then ‘k1’ mp_tac) >> simp[]) >>
  ASM_REWRITE_TAC [] >>
  simp[Abbr ‘n1’] >>
  qpat_assum ‘∀k'. LENGTH k' ≤ _ ⇒ _’
    (qspec_then ‘k1 ++ [x with results := TAKE (LENGTH (new_actions (log_of m1) (L ++ k1))) x.results]’ mp_tac) >>
  qpat_assum ‘∀k'. LENGTH k' ≤ _ ⇒ _’
    (qspec_then ‘k2 ++ [x with results := DROP (LENGTH (new_actions (log_of m1) (L ++ k1))) x.results]’ mp_tac) >>
  simp[] >> rpt strip_tac >> fs[]
QED

Theorem both_stut:
  (∀h' k'. LENGTH h' + LENGTH k' ≤ LENGTH h + LENGTH k ⇒ stut_at m1 h' k' ∧ stut_at m2 h' k') ⇒
  stut_at (both m1 m2) h k
Proof
  strip_tac >> REWRITE_TAC [stut_at_def] >> strip_tac >>
  fs[both_new_actions_all] >>
  qspecl_then [‘k’, ‘h’, ‘m1’, ‘m2’] mp_tac
    (Q.GENL [‘kk’, ‘h’, ‘m1’, ‘m2’] views_es) >>
  simp[] >> disch_then (qspec_then ‘k’ mp_tac) >> simp[] >> strip_tac >>
  simp[both_def] >>
  ‘m1 (left_view m1 m2 h ++ [es] ++ k1) = m1 (left_view m1 m2 h ++ k1) ∧
   m2 (right_view m1 m2 h ++ [es] ++ k2) = m2 (right_view m1 m2 h ++ k2)’
    by (conj_tac
        >- (first_x_assum (qspecl_then [‘left_view m1 m2 h’, ‘k1’] mp_tac) >>
            simp[stut_at_def])
        >> first_x_assum (qspecl_then [‘right_view m1 m2 h’, ‘k2’] mp_tac) >>
           simp[stut_at_def]) >>
  fs[]
QED

(* ------------------------------------------------------------------------
   The echo's handler and server
   ------------------------------------------------------------------------ *)

Theorem readable_stut[local]:
  stut_at (readable fd) h k
Proof
  simp[readable_def] >> irule wait_stut >> simp[]
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

Theorem handler_stut:
  ∀h k. stut_at (handler fd) h k
Proof
  ‘∀n h k fd. LENGTH h + LENGTH k = n ⇒ stut_at (handler fd) h k’ suffices_by metis_tac[] >>
  completeInduct_on ‘n’ >> rpt strip_tac >>
  ONCE_REWRITE_TAC [handler_unfold] >> REWRITE_TAC [handler_body_def] >>
  irule bind_stut >> simp[readable_stut, readable_facts] >> rpt strip_tac >>
  irule bind_stut >> simp[emit_stut, emit_facts] >> rpt strip_tac >>
  Cases_on ‘x’ >> simp[return_stut]
  >- (irule bind_stut >> simp[emit_stut, emit_facts] >> rpt strip_tac >>
      first_x_assum irule >> qexists_tac ‘LENGTH h''' + LENGTH k'''’ >> simp[]) >>
  first_x_assum irule >> qexists_tac ‘LENGTH h'' + LENGTH k''’ >> simp[]
QED

Theorem server_stut:
  ∀h k. stut_at (server lfd) h k
Proof
  ‘∀n h k lfd. LENGTH h + LENGTH k = n ⇒ stut_at (server lfd) h k’ suffices_by metis_tac[] >>
  completeInduct_on ‘n’ >> rpt strip_tac >>
  ONCE_REWRITE_TAC [server_unfold] >>
  irule bind_stut >> simp[readable_stut, readable_facts] >> rpt strip_tac >>
  irule bind_stut >> simp[emit_stut, emit_facts] >> rpt strip_tac >>
  Cases_on ‘x’ >> simp[]
  >> TRY (first_x_assum irule >> qexists_tac ‘LENGTH h'' + LENGTH k''’ >> simp[] >> NO_TAC) >>
  irule map_stut >> irule both_stut >> rpt strip_tac >> simp[handler_stut] >>
  first_x_assum irule >> qexists_tac ‘LENGTH h''' + LENGTH k'''’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The socket-vocabulary echo: bquiet
   ------------------------------------------------------------------------ *)

Theorem sfs_esnap[local]:
  sfs esnap = es
Proof
  simp[snap_map_def, sfe_def, ssnap_def, es_def]
QED

(* MAIN: an empty snapshot shown to the idle echo is a stutter *)
Theorem echo_bquiet:
  bquiet (srelabel (server kl)) (interest fds0) (K F)
Proof
  rw[bquiet_def]
  >- (fs[new_actions_relabel] >>
      ‘MAP sfs (h ++ [esnap] ++ k) = MAP sfs h ++ [es] ++ MAP sfs k’
        by simp[sfs_esnap] >>
      simp[] >>
      ‘new_actions (log_of (server kl)) (MAP sfs h) = []’ by fs[MAP_EQ_NIL] >>
      qspecl_then [‘server kl’, ‘MAP sfs h’] mp_tac (Q.GENL [‘m’, ‘h’] new_actions_stut) >>
      simp[server_stut, sfs_esnap])
  >> simp[interest_def, FOLDL_APPEND, ssnap_def, add_accepted_def]
QED
