(*
  The simulation, for the poll: polling handles in the version-2 world
  (hpoll) gives the ready handles that polling them as fds gives in the
  related version-1 world (sock_poll), when the handles are the listener
  and handed-out ones; both worlds tick, and stay related.
*)
Theory asyncHLSimPoll
Ancestors
  llist alist words ffiSpikeSocketFFI ffiSpikeSocketFair asyncM3World
  socketV2FFI socketV2Fair asyncHLFair asyncHLModel asyncHLSimWorld
  asyncHLSimTick asyncHLSimOps
Libs
  preamble

(* The handles a loop may poll: the listener and the handed-out ones *)
Definition hpoll_ok_def:
  hpoll_ok lfd n h ⇔ h = lfd ∨ ∃j. j < n ∧ h = hdl lfd j
End

Theorem hsim0_hdl_not_lfd[local]:
  hsim0 lfd s1 (s2, hs) ∧ j < LENGTH s2.clients ⇒ hdl lfd j ≠ lfd
Proof
  strip_tac >> ‘s2.clients ≠ []’ by (strip_tac >> fs[]) >>
  drule_all hsim0_bound >> strip_tac >> irule hdl_not_lfd >> fs[]
QED

Theorem hsim0_tbl_lfd[local]:
  hsim0 lfd s1 (s2, hs) ⇒ ALOOKUP hs.tbl lfd = NONE
Proof
  strip_tac >> Cases_on ‘ALOOKUP hs.tbl lfd’ >> simp[] >>
  ‘∃j. j < hs.nxt ∧ lfd = hdl lfd j’ by (fs[hsim0_def] >> metis_tac[]) >>
  ‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
  ‘j < LENGTH s2.clients’ by simp[] >>
  drule_all hsim0_hdl_not_lfd >> simp[]
QED

(* A polled handle is ready in the version-2 world exactly when it is in
   the version-1 world *)
Theorem hsim0_ready:
  hsim0 lfd s1 (s2, hs) ∧ hpoll_ok lfd hs.nxt h ⇒
  ((case ALOOKUP hs.tbl h of
    | SOME f => is_ready2 s2 f
    | NONE => if h = lfd then is_ready2 s2 h else T) ⇔ is_ready s1 h)
Proof
  strip_tac >> qpat_x_assum ‘hpoll_ok _ _ _’ mp_tac >> simp[hpoll_ok_def] >>
  Cases_on ‘h = lfd’
  (* the listener *)
  >- (pop_assum SUBST_ALL_TAC >> simp[] >> drule hsim0_tbl_lfd >> strip_tac >> simp[] >>
      ‘ALOOKUP s1.conns lfd = NONE’
        by (simp[ALOOKUP_NONE] >>
            ‘MAP FST s1.conns = REVERSE (GENLIST (hdl lfd) (LENGTH s2.clients))’
              by fs[hsim0_def] >>
            simp[MEM_GENLIST] >> rpt strip_tac >>
            drule_all hsim0_hdl_not_lfd >> simp[]) >>
      ‘client_of s2 lfd = NONE’
        by (simp[client_of_def] >> Cases_on ‘ALOOKUP s2.open_fds lfd’ >> simp[] >>
            imp_res_tac ALOOKUP_MEM >> fs[hsim0_def, MEM_MAP] >>
            metis_tac[FST]) >>
      ‘s2.listening = [(lfd, GENLIST (λi. hs.nxt + i) (LENGTH s2.clients − hs.nxt))] ∧
       s1.listeners = [(lfd, GENLIST (λi. hdl lfd (hs.nxt + i)) (LENGTH s2.clients − hs.nxt))]’
        by fs[hsim0_def] >>
      asm_simp_tac (srw_ss()) [is_ready2_def, is_ready_def, GENLIST_EQ_NIL])
  (* a handed-out handle *)
  >> simp[] >> strip_tac >> rveq >>
  ‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
  ‘j < LENGTH s2.clients’ by simp[] >>
  drule_all hsim0_hdl_not_lfd >> strip_tac >>
  drule_all hsim0_conn >> strip_tac >>
  drule hsim0_hdl_eq >> strip_tac >>
  ‘s2.clients ≠ []’ by (strip_tac >> fs[]) >>
  qpat_x_assum ‘hsim0 _ _ _’ mp_tac >>
  qpat_assum ‘s2.clients ≠ []’ (fn th => simp[hsim0_def, th]) >> strip_tac >>
  ‘ALOOKUP s1.listeners (hdl lfd j) = NONE’
    by (qpat_assum ‘s1.listeners = _’ SUBST1_TAC >> simp[] >>
        qpat_x_assum ‘hdl lfd j ≠ lfd’ mp_tac >> simp[]) >>
  simp[is_ready_def] >>
  Cases_on ‘ALOOKUP hs.tbl (hdl lfd j)’ >> simp[] >>
  TRY (qpat_x_assum ‘∀j. j < hs.nxt ∧ ALOOKUP hs.tbl _ = NONE ⇒ _’ (qspec_then ‘j’ mp_tac) >>
       impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[] >> NO_TAC) >>
  rename1 ‘ALOOKUP hs.tbl (hdl lfd j) = SOME f’ >>
  ‘ALOOKUP s2.open_fds f = SOME j’
    by (qpat_x_assum ‘∀h f. ALOOKUP hs.tbl h = SOME f ⇔ _’
          (qspecl_then [‘hdl lfd j’, ‘f’] mp_tac) >>
        qpat_assum ‘ALOOKUP hs.tbl _ = SOME _’ (fn th => rewrite_tac[th]) >>
        strip_tac >>
        qpat_x_assum ‘∀j1 j2. _’ (qspecl_then [‘j'’, ‘j’] mp_tac) >>
        impl_tac >- simp[] >>
        qpat_x_assum ‘hdl lfd j = hdl lfd j'’ (fn th => rewrite_tac[th]) >>
        strip_tac >> fs[]) >>
  ‘f ≠ lfd’
    by (qpat_x_assum ‘∀f. MEM f (MAP FST s2.open_fds) ⇒ _’ (qspec_then ‘f’ mp_tac) >>
        impl_tac
        >- (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> qexists_tac ‘(f, j)’ >> simp[]) >>
        simp[]) >>
  ‘ALOOKUP s2.listening f = NONE’
    by (qpat_assum ‘s2.listening = _’ SUBST1_TAC >> simp[]) >>
  simp[is_ready2_def, client_of_def]
QED

Theorem MEM_hpoll_fds[local]:
  MEM h hfds ∧ ALOOKUP hs.tbl h = SOME f ⇒ MEM f (hpoll_fds lfd hs hfds)
Proof
  rw[hpoll_fds_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists_tac ‘h’ >> simp[]
QED

Theorem MEM_hpoll_fds_lfd[local]:
  MEM lfd hfds ∧ ALOOKUP hs.tbl lfd = NONE ⇒ MEM lfd (hpoll_fds lfd hs hfds)
Proof
  rw[hpoll_fds_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists_tac ‘lfd’ >> simp[]
QED

Theorem hpoll_eq[local]:
  hpoll lfd hs hfds s =
    (hready lfd hs (FILTER (is_ready2 (tick2 s)) (hpoll_fds lfd hs hfds)) hfds, tick2 s)
Proof
  simp[hpoll_def, sock_poll2_def]
QED

(* MAIN: a poll of related worlds *)
Theorem hpoll_sim:
  hsim lfd s1 (s2, hs) ∧ sched_wf2 s2 ∧ EVERY (hpoll_ok lfd hs.nxt) hfds ⇒
  FST (hpoll lfd hs hfds s2) = FST (sock_poll hfds s1) ∧
  hsim lfd (SND (sock_poll hfds s1)) (SND (hpoll lfd hs hfds s2), hs) ∧
  sched_wf2 (SND (hpoll lfd hs hfds s2)) ∧
  LENGTH (SND (hpoll lfd hs hfds s2)).clients = LENGTH (tick2 s2).clients
Proof
  strip_tac >> drule sched_wf2_tick >> strip_tac >>
  drule_all tick_sim >> strip_tac >>
  asm_simp_tac (srw_ss()) [hpoll_eq, sock_poll_def, hready_def, FILTER_EQ] >>
  rpt strip_tac >>
  ‘hsim0 lfd (tick s1) (tick2 s2, hs)’ by fs[hsim_def] >>
  ‘hpoll_ok lfd hs.nxt h’ by fs[EVERY_MEM] >>
  drule_all hsim0_ready >> disch_then (SUBST1_TAC o SYM) >>
  Cases_on ‘ALOOKUP hs.tbl h’ >> simp[]
  >- (Cases_on ‘h = lfd’ >> simp[] >> pop_assum SUBST_ALL_TAC >>
      ‘MEM lfd (hpoll_fds lfd hs hfds)’ by (irule MEM_hpoll_fds_lfd >> fs[]) >>
      simp[MEM_FILTER])
  >> ‘MEM x (hpoll_fds lfd hs hfds)’ by (irule MEM_hpoll_fds >> qexists_tac ‘h’ >> fs[]) >>
  simp[MEM_FILTER]
QED
