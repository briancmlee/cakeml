(*
  The simulation, for the program's operations: the handle layer's hdo
  answers an action exactly as the version-1 world does (sock_do), on
  the related worlds, and keeps the relation, for the actions the echo
  server performs (accepts on the listener; reads and writes on handles
  it has been given).
*)
Theory lifetimeSimOps
Ancestors
  llist alist words socketWorld socketFair loopPollWorld
  loopSockInv lifetimeWorld lifetimeFair lifetimeProof lifetimeFairShape loopHandlesModel
  lifetimeSimWorld lifetimeSimTick
Libs
  preamble

(* The actions of a computation that has been given the handles of the
   first a clients, on listener lfd *)
Definition act_ok_def:
  (act_ok lfd a (Accept l) ⇔ l = lfd) ∧
  (act_ok lfd a (Read c k) ⇔ ∃j. j < a ∧ c = hdl lfd j) ∧
  (act_ok lfd a (Write c bs) ⇔ ∃j. j < a ∧ c = hdl lfd j)
End

Theorem GENLIST_shift[local]:
  0 < n ⇒ GENLIST (λi. f (a + i)) n = f a :: GENLIST (λi. f (a + 1 + i)) (n − 1)
Proof
  Cases_on ‘n’ >> simp[GENLIST_CONS, combinTheory.o_DEF, ADD1]
QED

(* ------------------------------------------------------------------------
   Accept
   ------------------------------------------------------------------------ *)

Theorem hdo_sim_accept:
  hsim lfd s1 (s2, hs) ∧ sock_do s1 (Accept lfd) = SOME (r, s1') ⇒
  ∃s2' hs' evs. hdo lfd (s2, hs) (Accept lfd) = SOME (r, (s2', hs'), evs) ∧
                hsim lfd s1' (s2', hs') ∧ LENGTH s2'.clients = LENGTH s2.clients ∧
                s2'.future = s2.future
Proof
  rw[hsim_def] >>
  qpat_assum ‘hsim0 _ _ _’
    (fn th => MAP_EVERY assume_tac (CONJUNCTS (REWRITE_RULE[hsim0_def] th))) >>
  gvs[sock_do_def, sock_accept_def, AllCaseEqs()] >>
  Cases_on ‘LENGTH s2.clients − hs.nxt’ >> gvs[GENLIST_CONS, combinTheory.o_DEF] >>
  TRY (simp[hdo_def, sock_accept2_def] >> NO_TAC) >>
  (* the oldest pending client, hs.nxt, gets the kernel's fd f *)
  ‘LENGTH (used_fds s2) < dimword (:64)’ by gvs[used_fds_def] >>
  qabbrev_tac ‘f = s2.alloc hs.nxt (used_fds s2)’ >>
  ‘¬MEM f (used_fds s2)’ by gvs[alloc_ok_def, Abbr ‘f’] >>
  ‘hdln (w2n lfd) hs.nxt < dimword (:64)’
    by (qspecl_then [‘w2n lfd’, ‘hs.nxt’] assume_tac (Q.GENL [‘lfdn’, ‘j’] hdln_lt) >>
        gvs[]) >>
  simp[hdo_def, sock_accept2_def] >>
  simp[hsim0_def, AFUPDKEY_def] >> rpt conj_tac
  >- (‘LENGTH s2.clients − (hs.nxt + 1) = n’ by fs[] >> simp[GENLIST_FUN_EQ, ADD1])
  >- (‘LENGTH s2.clients − (hs.nxt + 1) = n’ by fs[] >> simp[GENLIST_FUN_EQ, ADD1])
  >- (rw[] >> ‘j < hs.nxt’ by (CCONTR_TAC >> ‘j = hs.nxt’ by simp[] >> gvs[]) >>
      qpat_x_assum ‘∀j. j < hs.nxt ∧ _ ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[])
  >> ‘∀j. j < hs.nxt + 1 ∧ j ≠ hs.nxt ⇒ hdl lfd hs.nxt ≠ hdl lfd j’
       by (rpt strip_tac >>
           qspecl_then [‘hs.nxt’, ‘j’, ‘LENGTH s2.clients + 1’, ‘lfd’] mp_tac
             (Q.GENL [‘j1’,‘j2’,‘k’,‘lfd’] hdl_neq) >> impl_tac >- fs[] >> fs[])
  >> ‘¬MEM f (MAP FST s2.open_fds) ∧ ¬MEM f s2.reserved ∧ f ≠ lfd’
       by (qpat_x_assum ‘¬MEM f (used_fds s2)’ mp_tac >> simp[used_fds_def])
  >> ‘ALOOKUP s2.open_fds f = NONE’ by simp[ALOOKUP_NONE]
  >- (rpt gen_tac >> Cases_on ‘hdl lfd hs.nxt = h’ >> simp[]
      >- (qpat_x_assum ‘hdl lfd hs.nxt = h’ (SUBST_ALL_TAC o SYM) >>
          eq_tac >> strip_tac
          >- (qexists_tac ‘hs.nxt’ >> simp[])
          >> ‘j = hs.nxt’
               by (CCONTR_TAC >>
                   qpat_x_assum ‘∀j. j < hs.nxt + 1 ∧ _ ⇒ _’ (qspec_then ‘j’ mp_tac) >>
                   simp[]) >>
          pop_assum SUBST_ALL_TAC >> Cases_on ‘f = f'’ >- simp[] >>
          qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> simp[] >> strip_tac >>
          qpat_x_assum ‘∀f j. ALOOKUP s2.open_fds f = SOME j ⇒ j < hs.nxt’ drule >>
          simp[])
      >> Cases_on ‘f = f'’ >> simp[]
      >- (gvs[] >> rpt strip_tac >> gvs[])
      >> qpat_x_assum ‘∀h f. ALOOKUP hs.tbl h = SOME f ⇔ _’
           (qspecl_then [‘h’, ‘f'’] SUBST1_TAC) >>
      eq_tac >> strip_tac
      >- (qexists_tac ‘j’ >> fs[])
      >> qexists_tac ‘j’ >> fs[] >>
      qpat_x_assum ‘∀f j. ALOOKUP s2.open_fds f = SOME j ⇒ j < hs.nxt’ drule >>
      simp[])
  >- (rpt gen_tac >> Cases_on ‘f = f'’ >> simp[] >> strip_tac >>
      qpat_x_assum ‘∀f j. ALOOKUP s2.open_fds f = SOME j ⇒ j < hs.nxt’ drule >> simp[])
  >- (simp[MEM_MAP] >> Cases >> rw[] >> strip_tac >>
      drule_all ALOOKUP_ALL_DISTINCT_MEM >> strip_tac >> res_tac >> fs[])
  >> rw[] >> fs[] >> res_tac >> fs[]
QED

(* ------------------------------------------------------------------------
   Read
   ------------------------------------------------------------------------ *)

Theorem ALOOKUP_ADELKEY_eq[local]:
  ALOOKUP (ADELKEY k al) x = if x = k then NONE else ALOOKUP al x
Proof
  rw[ALOOKUP_ADELKEY]
QED

Theorem ALL_DISTINCT_MAP_ADELKEY[local]:
  ALL_DISTINCT (MAP g al) ⇒ ALL_DISTINCT (MAP g (ADELKEY k al))
Proof
  simp[ADELKEY_def] >> Induct_on ‘al’ >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

(* The fd of an open handle is unique *)
Theorem distinct_snd[local]:
  ∀al. ALL_DISTINCT (MAP SND al) ∧ MEM (a, v) al ∧ MEM (b, v) al ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem open_fd_unique[local]:
  ALL_DISTINCT (MAP SND al) ∧ ALOOKUP al f = SOME j ∧ ALOOKUP al f' = SOME j ⇒ f = f'
Proof
  rw[] >> imp_res_tac ALOOKUP_MEM >> metis_tac[distinct_snd]
QED

(* Handles of clients are distinct *)
Theorem hsim0_hdl_inj:
  hsim0 lfd s1 (s2, hs) ∧ j1 < LENGTH s2.clients ∧ j2 < LENGTH s2.clients ∧
  hdl lfd j1 = hdl lfd j2 ⇒ j1 = j2
Proof
  rpt strip_tac >> CCONTR_TAC >>
  ‘s2.clients ≠ []’ by (strip_tac >> gvs[]) >>
  drule_all hsim0_bound >> strip_tac >>
  qspecl_then [‘j1’, ‘j2’, ‘LENGTH s2.clients + 1’, ‘lfd’] mp_tac
    (Q.GENL [‘j1’,‘j2’,‘k’,‘lfd’] hdl_neq) >>
  impl_tac >- simp[] >> simp[]
QED

Theorem hsim0_hdl_eq:
  hsim0 lfd s1 (s2, hs) ⇒
  ∀j1 j2. j1 < LENGTH s2.clients ∧ j2 < LENGTH s2.clients ⇒
          (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)
Proof
  rw[] >> eq_tac >> rw[] >> irule hsim0_hdl_inj >> metis_tac[]
QED

(* The table's fd for an open handle is the client's fd *)
Theorem hsim0_tbl_open:
  hsim0 lfd s1 (s2, hs) ∧ j < LENGTH s2.clients ∧
  ALOOKUP hs.tbl (hdl lfd j) = SOME f ⇒
  ALOOKUP s2.open_fds f = SOME j
Proof
  strip_tac >>
  ‘∃j'. j' < hs.nxt ∧ hdl lfd j = hdl lfd j' ∧ ALOOKUP s2.open_fds f = SOME j'’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def] >> metis_tac[]) >>
  ‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
  ‘j' < LENGTH s2.clients’ by simp[] >>
  ‘j = j'’ by (irule hsim0_hdl_inj >> metis_tac[]) >>
  gvs[]
QED

Theorem MEM_MAP_FST_ADELKEY[local]:
  MEM x (MAP FST (ADELKEY k al)) ⇒ MEM x (MAP FST al)
Proof
  simp[ADELKEY_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem LENGTH_ADELKEY_LEQ[local]:
  LENGTH (ADELKEY k al) ≤ LENGTH al
Proof
  simp[ADELKEY_def, LENGTH_FILTER_LEQ]
QED

Theorem close_closed[local]:
  (∀j. j < n ∧ ALOOKUP tbl (hdl lfd j) = NONE ⇒
       (EL j cs).incoming = [] ∧ (EL j cs).peer_closed) ∧
  (∀j1 j2. j1 < L ∧ j2 < L ⇒ (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)) ∧
  n ≤ L ∧ j < n ∧ (EL j cs).incoming = [] ∧ (EL j cs).peer_closed ⇒
  ∀j'. j' < n ∧ ALOOKUP (ADELKEY (hdl lfd j) tbl) (hdl lfd j') = NONE ⇒
       (EL j' cs).incoming = [] ∧ (EL j' cs).peer_closed
Proof
  strip_tac >> gen_tac >> Cases_on ‘j' = j’ >- simp[] >>
  strip_tac >>
  ‘hdl lfd j' ≠ hdl lfd j’ by (qpat_x_assum ‘∀j1 j2. _’ (qspecl_then [‘j'’, ‘j’] mp_tac) >>
                               simp[]) >>
  qpat_x_assum ‘∀j. _’ irule >> fs[ALOOKUP_ADELKEY_eq]
QED

Theorem close_tbl[local]:
  (∀h f. ALOOKUP tbl h = SOME f ⇔ ∃j. j < n ∧ h = hdl lfd j ∧ ALOOKUP ofs f = SOME j) ∧
  (∀j1 j2. j1 < L ∧ j2 < L ⇒ (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)) ∧
  n ≤ L ∧ ALL_DISTINCT (MAP SND ofs) ∧ j < n ∧ ALOOKUP ofs f = SOME j ⇒
  ∀h f'. ALOOKUP (ADELKEY (hdl lfd j) tbl) h = SOME f' ⇔
         ∃j'. j' < n ∧ h = hdl lfd j' ∧ ALOOKUP (ADELKEY f ofs) f' = SOME j'
Proof
  strip_tac >> rpt gen_tac >> simp[ALOOKUP_ADELKEY_eq] >> eq_tac
  >- (Cases_on ‘h = hdl lfd j’ >> simp[] >> strip_tac >>
      rename1 ‘ALOOKUP ofs f' = SOME j'’ >> qexists_tac ‘j'’ >>
      simp[] >> strip_tac >> gvs[])
  >> strip_tac >> Cases_on ‘f' = f’ >> fs[] >>
  ‘hdl lfd j' ≠ hdl lfd j’
    by (strip_tac >>
        ‘j' = j’ by (qpat_x_assum ‘∀j1 j2. _’ (qspecl_then [‘j'’, ‘j’] mp_tac) >> simp[]) >>
        metis_tac[open_fd_unique]) >>
  simp[] >> metis_tac[]
QED

(* An EOF on an open handle: close its fd and drop it *)
Theorem hsim0_close:
  hsim0 lfd s1 (s2, hs) ∧ j < hs.nxt ∧ ALOOKUP hs.tbl (hdl lfd j) = SOME f ∧
  (EL j s2.clients).incoming = [] ∧ (EL j s2.clients).peer_closed ⇒
  hsim0 lfd s1 (s2 with open_fds := ADELKEY f s2.open_fds,
                hs with tbl := ADELKEY (hdl lfd j) hs.tbl)
Proof
  strip_tac >>
  ‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
  ‘ALOOKUP s2.open_fds f = SOME j’ by (irule hsim0_tbl_open >> simp[] >> metis_tac[]) >>
  drule hsim0_hdl_eq >> strip_tac >>
  ‘s2.clients ≠ []’ by (strip_tac >> gvs[]) >>
  qpat_x_assum ‘hsim0 _ _ _’ mp_tac >>
  qpat_assum ‘s2.clients ≠ []’ (fn th => simp[hsim0_def, th]) >> strip_tac >>
  rpt conj_tac
  >- fs[]
  >- (qspecl_then [‘hs.nxt’, ‘hs.tbl’, ‘lfd’, ‘s2.clients’, ‘LENGTH s2.clients’, ‘j’] mp_tac
        (Q.GENL [‘n’, ‘tbl’, ‘lfd’, ‘cs’, ‘L’, ‘j’] close_closed) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >- (qspecl_then [‘hs.tbl’, ‘hs.nxt’, ‘lfd’, ‘s2.open_fds’, ‘LENGTH s2.clients’, ‘j’, ‘f’]
        mp_tac (Q.GENL [‘tbl’, ‘n’, ‘lfd’, ‘ofs’, ‘L’, ‘j’, ‘f’] close_tbl) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >- (rw[ALOOKUP_ADELKEY_eq] >>
      qpat_x_assum ‘∀f j. _ ⇒ j < hs.nxt’ (qspecl_then [‘f'’, ‘j'’] mp_tac) >>
      asm_rewrite_tac[])
  >- (irule ALL_DISTINCT_MAP_ADELKEY >> first_assum ACCEPT_TAC)
  >- (irule ALL_DISTINCT_MAP_ADELKEY >> first_assum ACCEPT_TAC)
  >- (ntac 2 strip_tac >> drule MEM_MAP_FST_ADELKEY >> strip_tac >>
      qpat_x_assum ‘∀f. MEM f (MAP FST s2.open_fds) ⇒ _’ drule >> simp[])
  >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH s2.open_fds’ >>
  simp[LENGTH_ADELKEY_LEQ]
QED

(* Data read from client j (in both worlds) *)
Theorem hsim0_consume:
  hsim0 lfd s1 (s2, hs) ∧ j < LENGTH s2.clients ⇒
  hsim0 lfd (s1 with conns := AFUPDKEY (hdl lfd j)
                                (λcn. cn with incoming := DROP k cn.incoming) s1.conns)
            (update_client j (λcn. cn with incoming := DROP k cn.incoming) s2, hs)
Proof
  strip_tac >>
  drule hsim0_hdl_eq >> strip_tac >>
  ‘s2.clients ≠ []’ by (strip_tac >> gvs[]) >>
  qpat_x_assum ‘hsim0 _ _ _’ mp_tac >>
  qpat_assum ‘s2.clients ≠ []’
    (fn th => simp[hsim0_def, update_client_def, AFUPDKEY_ALOOKUP, EL_LUPDATE, th]) >>
  strip_tac >> rpt conj_tac
  >- fs[]
  >- (rpt gen_tac >> Cases_on ‘j' = j’ >> simp[] >> strip_tac
      >- (Cases_on ‘ALOOKUP s1.conns (hdl lfd j)’ >> fs[] >> rveq >>
          qpat_x_assum ‘∀j cn. _ ∧ ALOOKUP _ _ = _ ⇒ _’ (qspecl_then [‘j’, ‘x’] mp_tac) >> simp[])
      >> ‘hdl lfd j' ≠ hdl lfd j’
           by (qpat_assum ‘∀j1 j2. _’ (qspecl_then [‘j'’, ‘j’] mp_tac) >> fs[]) >>
      Cases_on ‘ALOOKUP s1.conns (hdl lfd j')’ >> fs[] >> rveq >>
      qpat_x_assum ‘∀j cn. _ ∧ ALOOKUP _ _ = _ ⇒ _’ (qspecl_then [‘j'’, ‘x’] mp_tac) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘∀j. j < hs.nxt ∧ _ ⇒ _’ (qspec_then ‘j'’ mp_tac) >> simp[] >>
      rw[] >> simp[])
  >> first_assum ACCEPT_TAC
QED

Theorem hdo_sim_read:
  hsim lfd s1 (s2, hs) ∧ j < hs.nxt ∧
  sock_do s1 (Read (hdl lfd j) k) = SOME (r, s1') ⇒
  ∃s2' hs' evs. hdo lfd (s2, hs) (Read (hdl lfd j) k) = SOME (r, (s2', hs'), evs) ∧
                hsim lfd s1' (s2', hs') ∧ LENGTH s2'.clients = LENGTH s2.clients ∧
                s2'.future = s2.future
Proof
  strip_tac >>
  ‘hsim0 lfd s1 (s2, hs)’ by fs[hsim_def] >>
  ‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
  ‘j < LENGTH s2.clients’ by simp[] >>
  drule_all hsim0_conn >> strip_tac >>
  qpat_x_assum ‘sock_do _ _ = _’ mp_tac >> simp[sock_do_def, sock_read_def] >>
  strip_tac >>
  Cases_on ‘ALOOKUP hs.tbl (hdl lfd j)’
  (* a closed handle: at EOF, in both worlds *)
  >- (‘(EL j s2.clients).incoming = [] ∧ (EL j s2.clients).peer_closed’
        by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def] >> metis_tac[]) >>
      gvs[hdo_def])
  (* an open handle, on fd f *)
  >> rename1 ‘ALOOKUP hs.tbl (hdl lfd j) = SOME f’ >>
  drule_all hsim0_tbl_open >> strip_tac >>
  ‘client_of s2 f = SOME j’ by simp[client_of_def] >>
  simp[hdo_def, sock_read2_def] >>
  Cases_on ‘(EL j s2.clients).incoming = []’ >> gvs[]
  >- (Cases_on ‘(EL j s2.clients).peer_closed’ >> gvs[] >>
      (* EOF: the handle layer closes f and drops the handle *)
      asm_simp_tac (srw_ss()) [sock_close2_def] >>
      qpat_x_assum ‘hsim _ _ _’ mp_tac >> simp[hsim_def] >> strip_tac >>
      irule hsim0_close >> fs[])
  (* data *)
  >> ‘TAKE k (EL j s2.clients).incoming ≠ []’ by fs[TAKE_EQ_NIL] >>
  Cases_on ‘TAKE k (EL j s2.clients).incoming’ >> fs[] >>
  qpat_x_assum ‘hsim _ _ _’ mp_tac >> simp[hsim_def, update_client_def] >> strip_tac >>
  drule_then (qspecl_then [‘k’, ‘j’] mp_tac) hsim0_consume >>
  impl_tac >- fs[] >> simp[update_client_def]
QED

(* ------------------------------------------------------------------------
   Write
   ------------------------------------------------------------------------ *)

(* The relation looks at the version-1 connections only through their
   fds, unread bytes and EOF flags ... *)
Theorem hsim0_conns_cong[local]:
  hsim0 lfd s1 (s2, hs) ∧ MAP FST cs = MAP FST s1.conns ∧
  (∀h cn'. ALOOKUP cs h = SOME cn' ⇒
           ∃cn. ALOOKUP s1.conns h = SOME cn ∧ cn'.incoming = cn.incoming ∧
                cn'.peer_closed = cn.peer_closed) ⇒
  hsim0 lfd (s1 with conns := cs) (s2, hs)
Proof
  rewrite_tac[hsim0_def] >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  asm_simp_tac (srw_ss()) [] >> rpt strip_tac >>
  TRY (qpat_x_assum ‘∀f j. _ ⇒ j < hs.nxt’ drule >> simp[] >> NO_TAC) >>
  qpat_x_assum ‘∀h cn'. ALOOKUP cs h = _ ⇒ _’ drule >> strip_tac >>
  qpat_x_assum ‘∀j cn. _ ∧ ALOOKUP s1.conns _ = _ ⇒ _’ drule_all >> simp[]
QED

(* ... and at the version-2 clients only through their number, unread bytes
   and EOF flags *)
Theorem hsim0_clients_cong[local]:
  hsim0 lfd s1 (s2, hs) ∧ LENGTH cs = LENGTH s2.clients ∧
  (∀j. j < LENGTH cs ⇒ (EL j cs).incoming = (EL j s2.clients).incoming ∧
                       (EL j cs).peer_closed = (EL j s2.clients).peer_closed) ⇒
  hsim0 lfd s1 (s2 with clients := cs, hs)
Proof
  rewrite_tac[hsim0_def] >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘cs = [] ⇔ s2.clients = []’ by metis_tac[LENGTH_NIL] >>
  asm_simp_tac (srw_ss()) [] >> rpt conj_tac >> rpt strip_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_x_assum ‘∀f j. _ ⇒ j < hs.nxt’ drule >> simp[] >> NO_TAC) >>
  TRY (Cases_on ‘s2.clients = []’ >> fs[] >> NO_TAC) >>
  qpat_x_assum ‘∀j. j < LENGTH cs ⇒ _’ (qspec_then ‘j’ mp_tac) >>
  qpat_x_assum ‘∀j. j < hs.nxt ∧ _ ⇒ _’ (qspec_then ‘j’ mp_tac) >>
  fs[]
QED

(* The relation does not look at what the server wrote *)
Theorem hsim0_write1[local]:
  hsim0 lfd s1 (s2, hs) ⇒
  hsim0 lfd (s1 with conns := AFUPDKEY c (λcn. cn with outgoing := cn.outgoing ++ bs) s1.conns)
            (s2, hs)
Proof
  strip_tac >> irule hsim0_conns_cong >> simp[AFUPDKEY_ALOOKUP] >>
  rpt gen_tac >> Cases_on ‘ALOOKUP s1.conns h’ >> simp[] >> rw[] >>
  simp[socketWorldTheory.conn_accfupds]
QED

Theorem hsim0_write:
  hsim0 lfd s1 (s2, hs) ⇒
  hsim0 lfd (s1 with conns := AFUPDKEY c (λcn. cn with outgoing := cn.outgoing ++ bs) s1.conns)
            (update_client j (λcn. cn with outgoing := cn.outgoing ++ bs) s2, hs)
Proof
  strip_tac >> drule hsim0_write1 >>
  disch_then (qspecl_then [‘c’, ‘bs’] assume_tac) >>
  simp[update_client_def] >> irule hsim0_clients_cong >>
  simp[EL_LUPDATE] >> rw[]
QED

Theorem hdo_sim_write:
  hsim lfd s1 (s2, hs) ∧ j < hs.nxt ∧
  sock_do s1 (Write (hdl lfd j) bs) = SOME (r, s1') ⇒
  ∃s2' hs' evs. hdo lfd (s2, hs) (Write (hdl lfd j) bs) = SOME (r, (s2', hs'), evs) ∧
                hsim lfd s1' (s2', hs') ∧ LENGTH s2'.clients = LENGTH s2.clients ∧
                s2'.future = s2.future
Proof
  strip_tac >>
  ‘hsim0 lfd s1 (s2, hs)’ by fs[hsim_def] >>
  ‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
  ‘j < LENGTH s2.clients’ by simp[] >>
  drule_all hsim0_conn >> strip_tac >>
  qpat_x_assum ‘sock_do _ _ = _’ mp_tac >>
  asm_simp_tac (srw_ss()) [sock_do_def, sock_write_def] >> strip_tac >>
  rveq >> qpat_x_assum ‘hsim _ _ _’ mp_tac >> simp[hsim_def] >> strip_tac >>
  Cases_on ‘ALOOKUP hs.tbl (hdl lfd j)’
  (* a closed handle: the write is dropped *)
  >- (asm_simp_tac (srw_ss()) [hdo_def] >> irule hsim0_write1 >> simp[])
  (* an open handle, on fd f *)
  >> rename1 ‘ALOOKUP hs.tbl (hdl lfd j) = SOME f’ >>
  drule_all hsim0_tbl_open >> strip_tac >>
  ‘client_of s2 f = SOME j’ by simp[client_of_def] >>
  asm_simp_tac (srw_ss()) [hdo_def, sock_write2_def] >>
  simp[hsim0_write, update_client_def]
QED

(* ------------------------------------------------------------------------
   A round's actions
   ------------------------------------------------------------------------ *)

Theorem hdo_sched_wf2:
  lifetime_fair s ∧ hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ⇒ lifetime_fair s'
Proof
  Cases_on ‘a’ >> rw[hdo_def, AllCaseEqs()] >> metis_tac[lifetime_fair_ops]
QED

(* The handles handed out so far are the first nxt ones *)
Theorem hdo_nxt:
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ⇒
  GENLIST (hdl lfd) hs'.nxt = GENLIST (hdl lfd) hs.nxt ++ wacc [(a, r)]
Proof
  Cases_on ‘a’ >> rw[hdo_def, AllCaseEqs(), wacc_def] >>
  simp[GSYM ADD1, GENLIST, SNOC_APPEND]
QED

(* MAIN: the handle layer performs a round's actions exactly as the
   version-1 world does, when they use only handed-out handles *)
Theorem hacts_sim:
  ∀acts s1 s2 hs rs evs1 s1'.
    hsim lfd s1 (s2, hs) ∧ lifetime_fair s2 ∧ EVERY (action_ok lfd acc) acts ∧
    set acc ⊆ set (GENLIST (hdl lfd) hs.nxt) ∧
    sock_acts s1 acts = SOME (rs, evs1, s1') ⇒
    ∃evs2 s2' hs'.
      hacts lfd (s2, hs) acts = SOME (rs, evs2, (s2', hs')) ∧
      hsim lfd s1' (s2', hs') ∧ lifetime_fair s2' ∧
      LENGTH s2'.clients = LENGTH s2.clients ∧ s2'.future = s2.future ∧
      GENLIST (hdl lfd) hs'.nxt = GENLIST (hdl lfd) hs.nxt ++ wacc (ZIP (acts, rs))
Proof
  Induct >> simp[sock_acts_def, hacts_def, wacc_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sock_do s1 a = SOME (r, s1a)’ >>
  ‘∃s2a hsa evsa. hdo lfd (s2, hs) a = SOME (r, (s2a, hsa), evsa) ∧
                  hsim lfd s1a (s2a, hsa) ∧ LENGTH s2a.clients = LENGTH s2.clients ∧
                  s2a.future = s2.future’
    by (Cases_on ‘a’ >> fs[action_ok_def]
        >- (rveq >> drule_all hdo_sim_accept >> simp[])
        >- (‘MEM c (GENLIST (hdl lfd) hs.nxt)’ by fs[SUBSET_DEF] >>
            fs[MEM_GENLIST] >> rveq >> drule_all hdo_sim_read >> simp[])
        >> ‘MEM c (GENLIST (hdl lfd) hs.nxt)’ by fs[SUBSET_DEF] >>
        fs[MEM_GENLIST] >> rveq >> drule_all hdo_sim_write >> simp[]) >>
  ‘lifetime_fair s2a’ by metis_tac[hdo_sched_wf2] >>
  drule hdo_nxt >> strip_tac >>
  first_x_assum (qspecl_then [‘s1a’, ‘s2a’, ‘hsa’, ‘rs'’, ‘evs’, ‘s1'’] mp_tac) >>
  impl_tac
  >- (simp[] >> fs[SUBSET_DEF]) >>
  strip_tac >> simp[] >> fs[wacc_def]
QED
