(*
  The GC hub on the chat server's runs: the guard holds, so the GC server
  is the chat server.

   - writer_args: a writer's Fetch positions start at the position its
     Start was answered with, and never decrease;
   - chat_gc_guard: on any history whose transcript hands out distinct
     connections (freshc) of 64-bit fds, every Fetch asks for at least the
     GC hub's base (the GC hub's cursor of that connection is its join
     position or one of its earlier Fetch positions, and base is the
     least cursor);
   - gc_server_eq: so with_tap of the GC hub and of the full hub give the
     chat server's inner machine the same history, and the two servers
     are the same machine on such histories.
*)
Theory asyncChatGCRun
Ancestors
  pair list rich_list arithmetic option string words alist
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncWithStore asyncWithTap asyncWithTapSim asyncChatSW asyncChatModel
  asyncChatSafe asyncChatGC
Libs
  BasicProvers dep_rewrite

(* ------------------------------------------------------------------------
   A writer's Fetch positions
   ------------------------------------------------------------------------ *)

(* Every Fetch of fd in ws asks for at least j, and for at least what every
   earlier Fetch of fd asked for *)
Definition wargs_ok_def:
  wargs_ok fd j (ws : ((action, num # cquery) kact # 'r) list) ⇔
    ∀k i r. k < LENGTH ws ∧ EL k ws = (Kv (fd, Fetch i), r) ⇒
            j ≤ i ∧ ∀k' i' r'. k' < k ∧ EL k' ws = (Kv (fd, Fetch i'), r') ⇒ i' ≤ i
End

Theorem wargs_ok_NIL[simp]:
  wargs_ok fd j []
Proof
  simp[wargs_ok_def]
QED

Theorem wargs_ok_other:
  (∀i. FST e ≠ Kv (fd, Fetch i)) ∧ wargs_ok fd j ws ⇒ wargs_ok fd j (e :: ws)
Proof
  rw[wargs_ok_def] >> Cases_on ‘k’ >> gvs[] >>
  first_x_assum drule_all >> rw[] >>
  Cases_on ‘k'’ >> gvs[] >> metis_tac[]
QED

Theorem wargs_ok_fetch:
  j ≤ i ∧ wargs_ok fd i ws ⇒ wargs_ok fd j ((Kv (fd, Fetch i), r) :: ws)
Proof
  rw[wargs_ok_def] >> Cases_on ‘k’ >> gvs[] >>
  first_x_assum drule_all >> rw[] >>
  Cases_on ‘k'’ >> gvs[] >> metis_tac[]
QED

Theorem trans_emit_running[local]:
  (∀n. n ≤ LENGTH h ⇒ (emit a (TAKE n h)).result = NONE) ⇒
  trans (emit a) h = [(a, NONE)]
Proof
  rw[trans_emit] >> Cases_on ‘h’ >> gvs[] >>
  first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def] >>
  rename1 ‘oHD s.results’ >> Cases_on ‘s.results’ >> simp[]
QED

Theorem wloop_args:
  ∀hh i. wargs_ok fd i (trans (wloop (fd, i)) hh)
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[wloop_unfold] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Fetch i))) K0) hh’ >>
  qspecl_then [‘emit (Kv (fd, Fetch i))’, ‘K0’, ‘hh’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[] >>
      strip_tac >> irule wargs_ok_fetch >> simp[]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >>
  irule wargs_ok_fetch >> simp[] >>
  Cases_on ‘res’ >> simp[Abbr ‘K0’] >>
  Cases_on ‘b’ >> simp[] >>
  rename1 ‘Lines ln’ >> Cases_on ‘ln = ""’ >> simp[] >>
  TRY (first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit WR) K1) h2’ >>
  qspecl_then [‘emit WR’, ‘K1’, ‘h2’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[] >>
      strip_tac >> irule wargs_ok_other >> simp[Abbr ‘WR’]) >>
  drule first_done_emit >> strip_tac >>
  gvs[trans_emit, Abbr ‘K1’, Abbr ‘WR’] >>
  irule wargs_ok_other >> simp[] >>
  first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘i + STRLEN ln’ mp_tac) >>
  rw[wargs_ok_def] >> res_tac >> simp[]
QED

(* MAIN: a writer's transcript has no Fetch, or starts with its Start
   answered with a position j, and then asks for at least j, increasingly *)
Theorem writer_args:
  (∀k i r. k < LENGTH (trans (writer fd) hh) ⇒
           EL k (trans (writer fd) hh) ≠ (Kv (fd, Fetch i), r)) ∨
  ∃j ws. trans (writer fd) hh = (Kv (fd, Start), SOME (KvR (Pos j))) :: ws ∧
        wargs_ok fd j ws
Proof
  simp[writer_def] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Start))) K0) hh’ >>
  qspecl_then [‘emit (Kv (fd, Start))’, ‘K0’, ‘hh’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[] >>
      rw[] >> disj1_tac >> Cases_on ‘k’ >> simp[]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >>
  Cases_on ‘res’ >> simp[Abbr ‘K0’] >> TRY (Cases_on ‘b’) >>
  simp[wloop_args] >> rw[] >> Cases_on ‘k’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Positions in a filtered list
   ------------------------------------------------------------------------ *)

Overload idx = “λP l p. LENGTH (FILTER P (TAKE p l))”

Theorem FILTER_idx:
  ∀l p. p < LENGTH l ∧ P (EL p l) ⇒
        idx P l p < LENGTH (FILTER P l) ∧ EL (idx P l p) (FILTER P l) = EL p l
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘p’ >> rw[] >> fs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem FILTER_idx_lt:
  ∀l k p. k < p ∧ p ≤ LENGTH l ∧ P (EL k l) ⇒ idx P l k < idx P l p
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘k’ >> Cases_on ‘p’ >> rw[] >> fs[] >>
  Cases_on ‘n’ >> fs[]
QED

Theorem FILTER_pos:
  ∀l m. m < LENGTH (FILTER P l) ⇒
        ∃q. q < LENGTH l ∧ P (EL q l) ∧ EL m (FILTER P l) = EL q l ∧ idx P l q = m
Proof
  Induct >> simp[] >> rpt gen_tac >> rw[]
  >- (Cases_on ‘m’ >> fs[]
      >- (qexists_tac ‘0’ >> simp[])
      >> first_x_assum drule >> strip_tac >> qexists_tac ‘SUC q’ >> simp[])
  >> first_x_assum drule >> strip_tac >> qexists_tac ‘SUC q’ >> simp[]
QED

Theorem idx_lt_pos:
  idx P l q < idx P l p ∧ P (EL q l) ∧ q < LENGTH l ∧ p ≤ LENGTH l ⇒ q < p
Proof
  rpt strip_tac >> CCONTR_TAC >>
  Cases_on ‘q = p’ >- fs[] >>
  ‘p < q’ by simp[] >>
  ‘idx P l p ≤ idx P l q’
    by (‘TAKE q l = TAKE p l ++ DROP p (TAKE q l)’
          by (‘TAKE p l = TAKE p (TAKE q l)’ by simp[TAKE_TAKE_MIN, MIN_DEF] >>
              pop_assum SUBST1_TAC >> simp[TAKE_DROP]) >>
        pop_assum SUBST1_TAC >> simp[FILTER_APPEND]) >>
  fs[]
QED

(* ------------------------------------------------------------------------
   The full hub's joins
   ------------------------------------------------------------------------ *)

Theorem joins_same:
  ∀tr st. (∀l fd. MEM (Sock (Accept l), SOME (SockR (Accepted fd))) tr ⇒ n2w fd ≠ w) ⇒
          ALOOKUP (tap_fold chat_tap chat_delta st tr).joins w = ALOOKUP st.joins w
Proof
  Induct >> simp[tap_fold_def] >> PairCases >> Cases_on ‘h0’ >>
  simp[tap_fold_def] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac ‘tap_fold chat_tap chat_delta SS tr’ >>
  ‘ALOOKUP (tap_fold chat_tap chat_delta SS tr).joins w = ALOOKUP SS.joins w’
    by (first_x_assum irule >> metis_tac[]) >>
  simp[Abbr ‘SS’]
  >- (every_case_tac >> simp[chat_tap_def] >> every_case_tac >> fs[] >>
      metis_tac[])
  >> PairCases_on ‘q’ >> Cases_on ‘q1’ >> simp[chat_delta_def]
QED

Theorem joins_some:
  ALOOKUP (tap_fold chat_tap chat_delta empty_store tr).joins w = SOME j ⇒
  ∃l fd. MEM (Sock (Accept l), SOME (SockR (Accepted fd))) tr ∧ n2w fd = w
Proof
  CCONTR_TAC >> fs[] >>
  ‘ALOOKUP (tap_fold chat_tap chat_delta empty_store tr).joins w =
   ALOOKUP empty_store.joins w’ by (irule joins_same >> metis_tac[]) >>
  fs[empty_store_def]
QED

(* ------------------------------------------------------------------------
   The GC hub's cursors
   ------------------------------------------------------------------------ *)

Theorem collect_fields[local]:
  (collect st).curs = st.curs ∧ (collect st).gjoins = st.gjoins
Proof
  simp[collect_def]
QED

Theorem gc_curs_step[local]:
  (∀w c. ALOOKUP st.curs w = SOME c ⇒ ALOOKUP st.gjoins w = SOME c ∨ P w c) ∧
  ALOOKUP (tap_fold gc_tap gc_delta st [e]).curs w = SOME c ⇒
  ALOOKUP (tap_fold gc_tap gc_delta st [e]).gjoins w = SOME c ∨ P w c ∨
  ∃fd' i' r. e = (Kv (fd', Fetch i'), r) ∧ n2w fd' = w ∧ c ≤ i'
Proof
  PairCases_on ‘e’ >> Cases_on ‘e0’ >> simp[tap_fold_def] >> strip_tac
  >- (Cases_on ‘e1’ >> fs[] >> Cases_on ‘x’ >> fs[gc_tap_def, collect_fields] >>
      Cases_on ‘a’ >> fs[gc_tap0_def] >>
      every_case_tac >> gvs[] >> TRY (Cases_on ‘n2w n = w’) >> gvs[])
  >> PairCases_on ‘q’ >> Cases_on ‘q1’ >>
  fs[gc_delta_def, collect_fields, AFUPDKEY_ALOOKUP] >>
  every_case_tac >> gvs[]
QED

(* A cursor is its connection's join position, or at most an earlier
   Fetch's position *)
Theorem gc_curs:
  ∀tr w c.
    ALOOKUP (tap_fold gc_tap gc_delta empty_gstore tr).curs w = SOME c ⇒
    ALOOKUP (tap_fold gc_tap gc_delta empty_gstore tr).gjoins w = SOME c ∨
    ∃k fd' i' r. k < LENGTH tr ∧ EL k tr = (Kv (fd', Fetch i'), r) ∧
                 n2w fd' = w ∧ c ≤ i'
Proof
  Induct_on ‘tr’ using SNOC_INDUCT
  >- simp[tap_fold_def, empty_gstore_def] >>
  rpt gen_tac >> simp[SNOC_APPEND, tap_fold_APPEND] >> strip_tac >>
  qabbrev_tac ‘st = tap_fold gc_tap gc_delta empty_gstore tr’ >>
  qspecl_then [‘st’, ‘λw c. ∃k fd' i' r. k < LENGTH tr ∧ EL k tr = (Kv (fd', Fetch i'), r) ∧
                                       n2w fd' = w ∧ c ≤ i'’, ‘x’, ‘w’, ‘c’] mp_tac
    (Q.GENL [‘st’, ‘P’, ‘e’, ‘w’, ‘c’] gc_curs_step) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >> simp[]
  >- (fs[] >> disj2_tac >> qexistsl_tac [‘k’, ‘fd'’, ‘i'’, ‘r’] >> simp[EL_APPEND1])
  >> disj2_tac >> qexistsl_tac [‘LENGTH tr’, ‘fd'’, ‘i'’, ‘r’] >> simp[EL_APPEND2]
QED

(* ------------------------------------------------------------------------
   The guard on the chat server's transcripts
   ------------------------------------------------------------------------ *)

Theorem ws_at[local]:
  L = x :: ws ∧ n < LENGTH L ∧ EL n L = e ∧ 0 < n ⇒
  n − 1 < LENGTH ws ∧ EL (n − 1) ws = e
Proof
  Cases_on ‘n’ >> rw[] >> fs[]
QED

Theorem acceptedc_lt[local]:
  fds_ok (untag tr) ∧ MEM fd (acceptedc tr) ⇒ fd < dimword(:64)
Proof
  rw[acceptedc_def, MEM_FLAT, MEM_MAP] >> every_case_tac >> gvs[] >>
  rename1 ‘MEM (Sock (Accept l0), SOME (SockR (Accepted fd))) tr’ >>
  ‘MEM (Accept l0, SOME (Accepted fd)) (untag tr)’
    by (simp[untag_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        qexists_tac ‘(Sock (Accept l0), SOME (SockR (Accepted fd)))’ >> simp[]) >>
  fs[fds_ok_def] >> res_tac >> fs[]
QED

Theorem MEM_acceptedc_of[local]:
  MEM (Sock (Accept l), SOME (SockR (Accepted fd))) tr ⇒ MEM fd (acceptedc tr)
Proof
  simp[acceptedc_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> strip_tac >>
  first_assum (irule_at Any) >> simp[]
QED

Theorem wq_on_fdc[local]:
  FILTER (wq fd) tr = FILTER (wq fd) (FILTER (on_fdc fd) tr)
Proof
  simp[FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM] >> gen_tac >> simp[wq_def, on_fdc_def, on_fd_def] >>
  Cases_on ‘FST x’ >> simp[] >> metis_tac[PAIR, FST]
QED

(* MAIN: on a transcript of the chat server's inner machine that hands out
   distinct 64-bit connections and whose answers are the full hub's, every
   Fetch asks for at least the GC hub's base *)
Theorem chat_gc_guard:
  freshc (trans (chat_inner lfd) IH) ∧ fds_ok (untag (trans (chat_inner lfd) IH)) ∧
  answers_ok chat_tap chat_delta empty_store (trans (chat_inner lfd) IH) ⇒
  guard_ok gc_guard gc_tap gc_delta empty_gstore (trans (chat_inner lfd) IH)
Proof
  qabbrev_tac ‘TT = trans (chat_inner lfd) IH’ >> strip_tac >>
  ‘(∀fd. FILTER (on_fdc fd) TT = [] ∨ ∃L. FILTER (on_fdc fd) TT = trans (chat_handler fd) L) ∧
   (∀fd. EXISTS (on_fdc fd) TT ⇒ MEM fd (acceptedc TT))’
    by (qspecl_then [‘chat_handler’, ‘lfd’] mp_tac
          (Q.GENL [‘h’, ‘lfd’] cserver_with_isolates) >>
        simp[chat_handler_on_fdc] >> disch_then (qspec_then ‘IH’ mp_tac) >>
        fs[Abbr ‘TT’, chat_inner_def]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum ‘Abbrev _’ kall_tac >>
  (* the writer of a connection with a Fetch at p *)
  ‘∀p fd q r. p < LENGTH TT ∧ EL p TT = (Kv (fd, q), r) ⇒
     fd < dimword(:64) ∧
     ∃(R : (event, (canswer, asyncServer$response) kres) snapshot list).
       FILTER (wq fd) TT = trans (writer fd) R’
    by (rpt gen_tac >> strip_tac >>
        ‘EXISTS (on_fdc fd) TT’
          by (simp[EXISTS_MEM] >> qexists_tac ‘EL p TT’ >> simp[EL_MEM, on_fdc_def]) >>
        conj_tac >- metis_tac[acceptedc_lt] >>
        qpat_assum ‘∀fd. FILTER (on_fdc fd) TT = [] ∨ _’ (qspec_then ‘fd’ strip_assume_tac)
        >- (‘MEM (EL p TT) (FILTER (on_fdc fd) TT)’
              by simp[MEM_FILTER, EL_MEM, on_fdc_def] >> gvs[]) >>
        ONCE_REWRITE_TAC[wq_on_fdc] >> simp[] >>
        qspecl_then [‘fd’, ‘L’] strip_assume_tac
          (Q.GENL [‘fd’, ‘L’] chat_handler_writer) >>
        qexists_tac ‘R’ >> simp[]) >>
  ‘∀p. p ≤ LENGTH TT ⇒ guard_ok gc_guard gc_tap gc_delta empty_gstore (TAKE p TT)’
    suffices_by (disch_then (qspec_then ‘LENGTH TT’ mp_tac) >> simp[]) >>
  Induct >- simp[] >> strip_tac >> fs[] >>
  ‘TAKE (SUC p) TT = TAKE p TT ++ [EL p TT]’ by simp[TAKE_SUC_EL] >>
  simp[guard_ok_APPEND, guard_ok_CONS, gc_guard_def] >>
  rpt strip_tac >>
  ‘∃fd. q = (fd, Fetch i)’ by (Cases_on ‘q’ >> fs[]) >>
  qpat_x_assum ‘SND q = _’ kall_tac >> gvs[] >>
  qabbrev_tac ‘gb = tap_fold gc_tap gc_delta empty_gstore (TAKE p TT)’ >>
  qabbrev_tac ‘ab = tap_fold chat_tap chat_delta empty_store (TAKE p TT)’ >>
  ‘gR ab gb’
    by (simp[Abbr ‘ab’, Abbr ‘gb’] >> irule (MATCH_MP tap_fold_sim gc_sim_ok) >>
        simp[gR_empty]) >>
  (* the writer *)
  first_assum (qspecl_then [‘p’, ‘fd’, ‘Fetch i’, ‘r’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘wq fd (EL p TT)’ by simp[wq_def] >>
  mp_tac (Q.SPECL [‘TT’, ‘p’] (Q.ISPEC ‘wq fd’ (Q.GEN ‘P’ FILTER_idx))) >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [‘fd’, ‘R’] strip_assume_tac (Q.GENL [‘fd’, ‘hh’] writer_args)
  >- (‘idx (wq fd) TT p < LENGTH (trans (writer fd) R)’ by metis_tac[] >>
      first_x_assum drule >> metis_tac[]) >>
  ‘0 < idx (wq fd) TT p’
    by (CCONTR_TAC >> ‘idx (wq fd) TT p = 0’ by decide_tac >> gvs[]) >>
  (* where the Start is *)
  ‘0 < LENGTH (FILTER (wq fd) TT)’ by simp[] >>
  mp_tac (Q.SPECL [‘TT’, ‘0’] (Q.ISPEC ‘wq fd’ (Q.GEN ‘P’ FILTER_pos))) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_rename_tac ‘FILTER (wq fd) (TAKE ps TT) = []’ >>
  ‘ps < p’
    by (CCONTR_TAC >>
        Cases_on ‘ps = p’
        >- (qpat_x_assum ‘ps = p’ SUBST_ALL_TAC >>
            qpat_x_assum ‘_ = EL p TT’ mp_tac >>
            qpat_x_assum ‘EL p TT = _’ (fn th => REWRITE_TAC[th]) >> simp[]) >>
        mp_tac (Q.SPECL [‘TT’, ‘p’, ‘ps’] (Q.ISPEC ‘wq fd’ (Q.GEN ‘P’ FILTER_idx_lt))) >>
        simp[]) >>
  qpat_x_assum ‘_ = EL ps TT’ (assume_tac o SYM) >>
  ‘ALOOKUP (tap_fold chat_tap chat_delta empty_store (TAKE ps TT)).joins (n2w fd) = SOME j’
    by (qpat_x_assum ‘answers_ok _ _ _ _’
          (mp_tac o Q.SPECL [‘ps’, ‘(fd, Start)’, ‘KvR (Pos j)’] o
           REWRITE_RULE[answers_ok_def]) >>
        simp[chat_delta_def] >> every_case_tac >> simp[]) >>
  (* no other accept of fd up to p *)
  ‘∃la fda. MEM (Sock (Accept la), SOME (SockR (Accepted fda))) (TAKE ps TT) ∧
            n2w fda = (n2w fd : word64)’
    by (irule joins_some >> qexists_tac ‘j’ >> first_assum ACCEPT_TAC) >>
  ‘TAKE p TT = TAKE ps TT ++ DROP ps (TAKE p TT)’
    by (‘TAKE ps TT = TAKE ps (TAKE p TT)’ by simp[TAKE_TAKE_MIN, MIN_DEF] >>
        pop_assum SUBST1_TAC >> simp[TAKE_DROP]) >>
  ‘∀lb fdb. MEM (Sock (Accept lb), SOME (SockR (Accepted fdb))) (DROP ps (TAKE p TT)) ⇒
            n2w fdb ≠ (n2w fd : word64)’
    by (rpt strip_tac >>
        ‘TT = TAKE ps TT ++ DROP ps (TAKE p TT) ++ DROP p TT’
          by (qpat_x_assum ‘TAKE p TT = _’ (SUBST1_TAC o SYM) >> simp[]) >>
        ‘MEM fda (acceptedc (TAKE ps TT)) ∧ MEM fdb (acceptedc (DROP ps (TAKE p TT)))’
          by metis_tac[MEM_acceptedc_of] >>
        ‘ALL_DISTINCT (acceptedc (TAKE ps TT ++ DROP ps (TAKE p TT) ++ DROP p TT))’
          by metis_tac[freshc_def] >>
        ‘MEM fda (acceptedc TT) ∧ MEM fdb (acceptedc TT)’
          by (qpat_x_assum ‘TT = _’ (fn th => ONCE_REWRITE_TAC[th]) >> simp[]) >>
        ‘fda < dimword(:64) ∧ fdb < dimword(:64)’ by metis_tac[acceptedc_lt] >>
        ‘(n2w fda : word64) = n2w fdb’
          by (qpat_x_assum ‘n2w fda = _’ SUBST1_TAC >>
              qpat_x_assum ‘n2w fdb = _’ (SUBST1_TAC o SYM) >> REFL_TAC) >>
        ‘fda = fdb’ by (pop_assum mp_tac >> simp[n2w_11, LESS_MOD]) >>
        gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘ALOOKUP ab.joins (n2w fd) = SOME j’
    by (qpat_x_assum ‘TAKE p TT = _’ (fn th => simp[Abbr ‘ab’, Once th]) >>
        simp[tap_fold_APPEND] >>
        qmatch_goalsub_abbrev_tac ‘tap_fold chat_tap chat_delta A0 (DROP ps (TAKE p TT))’ >>
        ‘ALOOKUP (tap_fold chat_tap chat_delta A0 (DROP ps (TAKE p TT))).joins (n2w fd) =
         ALOOKUP A0.joins (n2w fd)’
          by (irule joins_same >> first_assum ACCEPT_TAC) >>
        simp[Abbr ‘A0’]) >>
  qpat_x_assum ‘TAKE p TT = _’ kall_tac >>
  (* the GC hub's cursor of fd *)
  ‘gb.gjoins = ab.joins ∧ MAP FST gb.curs = MAP FST gb.gjoins ∧ gc_inv gb’
    by fs[gR_def] >>
  ‘MEM (n2w fd, j) ab.joins’
    by (qpat_assum ‘ALOOKUP ab.joins _ = _’ (ACCEPT_TAC o MATCH_MP ALOOKUP_MEM)) >>
  ‘MEM (n2w fd) (MAP FST gb.curs)’
    by (qpat_assum ‘MAP FST gb.curs = _’ SUBST1_TAC >>
        qpat_assum ‘gb.gjoins = _’ SUBST1_TAC >>
        REWRITE_TAC[MEM_MAP] >> qexists_tac ‘(n2w fd, j)’ >>
        conj_tac >- REWRITE_TAC[FST] >> first_assum ACCEPT_TAC) >>
  ‘∃c. ALOOKUP gb.curs (n2w fd) = SOME c’
    by (Cases_on ‘ALOOKUP gb.curs (n2w fd)’
        >- (pop_assum mp_tac >> REWRITE_TAC[ALOOKUP_NONE] >>
            pop_assum (fn th => REWRITE_TAC[th]))
        >> qexists_tac ‘x’ >> REFL_TAC) >>
  (* fd's Fetch at p, in the writer's list after its Start *)
  ‘idx (wq fd) TT p − 1 < LENGTH ws ∧
   EL (idx (wq fd) TT p − 1) ws = (Kv (fd, Fetch i), r)’
    by (mp_tac (Q.SPECL [‘(Kv (fd, Start), SOME (KvR (Pos j)))’, ‘ws’,
                          ‘idx (wq fd) TT p’, ‘(Kv (fd, Fetch i), r)’]
                  (Q.ISPEC ‘FILTER (wq fd) TT’ (Q.GENL [‘L’, ‘x’, ‘ws’, ‘n’, ‘e’] ws_at))) >>
        impl_tac >- (rpt conj_tac
                     >- (qpat_assum ‘FILTER (wq fd) TT = _’ SUBST1_TAC >> first_assum ACCEPT_TAC)
                     >- first_assum ACCEPT_TAC
                     >- (qpat_assum ‘EL (idx (wq fd) TT p) _ = _’ SUBST1_TAC >>
                         first_assum ACCEPT_TAC)
                     >> first_assum ACCEPT_TAC) >>
        REWRITE_TAC[]) >>
  ‘ALOOKUP gb.gjoins (n2w fd) = SOME c ∨
   ∃k fd' i' r'. k < p ∧ EL k TT = (Kv (fd', Fetch i'), r') ∧
                 n2w fd' = (n2w fd : word64) ∧ c ≤ i'’
    by (qunabbrev_tac ‘gb’ >>
        qpat_assum ‘ALOOKUP (tap_fold gc_tap _ _ _).curs _ = SOME c’
          (strip_assume_tac o MATCH_MP gc_curs) >- (disj1_tac >> first_assum ACCEPT_TAC) >>
        disj2_tac >> qexistsl_tac [‘k’, ‘fd'’, ‘i'’] >>
        ‘k < p’ by (qpat_x_assum ‘k < LENGTH _’ mp_tac >> simp[LENGTH_TAKE_EQ]) >>
        ‘EL k (TAKE p TT) = EL k TT’ by (irule rich_listTheory.EL_TAKE >> qpat_assum ‘k < p’ ACCEPT_TAC) >>
        pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        qexists_tac ‘r'’ >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘ALOOKUP gb.gjoins (n2w fd) = SOME c ⇒ c ≤ i’
    by (strip_tac >>
        ‘SOME c = SOME j’
              by (qpat_x_assum ‘ALOOKUP gb.gjoins _ = SOME c’ (SUBST1_TAC o SYM) >>
                  qpat_assum ‘gb.gjoins = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
            ‘c = j’ by fs[] >> pop_assum SUBST1_TAC >>
            qpat_assum ‘wargs_ok _ _ _’ (mp_tac o REWRITE_RULE[wargs_ok_def]) >>
            disch_then (qspecl_then [‘idx (wq fd) TT p − 1’, ‘i’, ‘r’] mp_tac) >>
            impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
            strip_tac >> first_assum ACCEPT_TAC) >>
  ‘∀k fd' i' (r' : (canswer, asyncServer$response) kres option).
     k < p ∧ EL k TT = (Kv (fd', Fetch i'), r') ∧ n2w fd' = (n2w fd : word64) ∧ c ≤ i' ⇒
     c ≤ i’
    by (rpt gen_tac >> strip_tac >>
        ‘fd' < dimword(:64)’
             by (first_assum (qspecl_then [‘k’, ‘fd'’, ‘Fetch i'’, ‘r'’] mp_tac) >>
                 impl_tac >- (conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
                 strip_tac >> ‘dimword(:64) = 18446744073709551616’ by EVAL_TAC >>
                 pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        ‘fd' = fd’ by (qpat_x_assum ‘n2w fd' = _’ mp_tac >> simp[n2w_11, LESS_MOD]) >>
        qpat_x_assum ‘fd' = fd’ SUBST_ALL_TAC >>
        ‘wq fd (EL k TT)’ by (qpat_assum ‘EL k TT = _’ SUBST1_TAC >> simp[wq_def]) >>
        ‘idx (wq fd) TT k < idx (wq fd) TT p’
          by (mp_tac (Q.SPECL [‘TT’, ‘k’, ‘p’] (Q.ISPEC ‘wq fd’ (Q.GEN ‘P’ FILTER_idx_lt))) >>
              impl_tac >- simp[] >> simp[]) >>
        mp_tac (Q.SPECL [‘TT’, ‘k’] (Q.ISPEC ‘wq fd’ (Q.GEN ‘P’ FILTER_idx))) >>
        impl_tac >- simp[] >> strip_tac >>
        ‘0 < idx (wq fd) TT k’
          by (CCONTR_TAC >>
              ‘idx (wq fd) TT k = 0’ by decide_tac >>
              qpat_x_assum ‘EL (idx (wq fd) TT k) _ = _’ mp_tac >>
              pop_assum SUBST1_TAC >>
              qpat_assum ‘FILTER (wq fd) TT = _’ SUBST1_TAC >>
              qpat_assum ‘trans (writer fd) R = _’ SUBST1_TAC >>
              qpat_assum ‘EL k TT = _’ SUBST1_TAC >> simp[]) >>
        ‘idx (wq fd) TT k − 1 < LENGTH ws ∧
         EL (idx (wq fd) TT k − 1) ws = (Kv (fd, Fetch i'), r')’
          by (mp_tac (Q.SPECL [‘(Kv (fd, Start), SOME (KvR (Pos j)))’,
                                ‘ws’, ‘idx (wq fd) TT k’, ‘(Kv (fd, Fetch i'), r')’]
                        (Q.ISPEC ‘FILTER (wq fd) TT’ (Q.GENL [‘L’, ‘x’, ‘ws’, ‘n’, ‘e’] ws_at))) >>
              impl_tac >- (rpt conj_tac
                           >- (qpat_assum ‘FILTER (wq fd) TT = _’ SUBST1_TAC >>
                               first_assum ACCEPT_TAC)
                           >- first_assum ACCEPT_TAC
                           >- (qpat_assum ‘EL (idx (wq fd) TT k) _ = _’ SUBST1_TAC >>
                               first_assum ACCEPT_TAC)
                           >> first_assum ACCEPT_TAC) >>
              REWRITE_TAC[]) >>
        qpat_assum ‘wargs_ok _ _ _’ (mp_tac o REWRITE_RULE[wargs_ok_def]) >>
        disch_then (qspecl_then [‘idx (wq fd) TT p − 1’, ‘i’, ‘r’] mp_tac) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        strip_tac >>
        first_x_assum (qspecl_then [‘idx (wq fd) TT k − 1’, ‘i'’, ‘r'’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
        decide_tac) >>
  ‘c ≤ i’
    by (TRY (qpat_x_assum ‘ALOOKUP gb.gjoins _ = SOME c ⇒ _’ irule >>
             first_assum ACCEPT_TAC >> NO_TAC) >>
        qpat_x_assum ‘∀k fd' i' r'. _’ drule_all >> DISCH_THEN ACCEPT_TAC) >>
  ‘MEM c (MAP SND gb.curs)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  fs[gc_inv_def] >> res_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The GC server is the chat server
   ------------------------------------------------------------------------ *)

(* MAIN: on such histories, the GC hub gives the inner machine the same
   history as the full hub *)
Theorem gc_hist_eq:
  freshc (trans (chat_inner lfd) (tap_hist chat_tap chat_delta empty_store (chat_inner lfd) hh)) ∧
  fds_ok (untag (trans (chat_inner lfd)
                   (tap_hist chat_tap chat_delta empty_store (chat_inner lfd) hh))) ⇒
  tap_hist gc_tap gc_delta empty_gstore (chat_inner lfd) hh =
  tap_hist chat_tap chat_delta empty_store (chat_inner lfd) hh
Proof
  strip_tac >> irule tap_hist_sim >> simp[wf_chat_inner] >>
  qexistsl_tac [‘gc_guard’, ‘gR’] >>
  simp[wf_chat_inner, gc_sim_ok, gR_empty] >>
  irule chat_gc_guard >> simp[tap_answers, wf_chat_inner]
QED

Theorem gc_server_eq:
  freshc (trans (chat_inner lfd) (tap_hist chat_tap chat_delta empty_store (chat_inner lfd) hh)) ∧
  fds_ok (untag (trans (chat_inner lfd)
                   (tap_hist chat_tap chat_delta empty_store (chat_inner lfd) hh))) ⇒
  gc_server lfd hh = chat_server lfd hh
Proof
  strip_tac >> drule_all gc_hist_eq >>
  simp[gc_server_def, chat_server_def, with_tap_def]
QED
