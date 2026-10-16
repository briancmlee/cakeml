(*
  The simulation, world side: a version-2 world, with the handle loop's
  table, against the version-1 world in which client j's connection has
  the fd hdl lfd j (the handle the loop gives it).

   - rn_sched: the version-1 schedule of a version-2 one (Connect2 l becomes
     Connect l (hdl lfd k) for the k-th client, Data2 j / Eof2 j are on
     hdl lfd j); v1of lfd sk2 is the version-1 world of sk2.
   - hsim0 lfd s1 (s2, hs): the listener's queues correspond (version 2:
     the clients a, a+1, ..., k-1 not yet accepted; version 1: their
     handles); the connections of s1 are the handles of the clients, with
     the same unread data and EOF flags; the table maps exactly the open
     handles to their fds; closed handles' clients are at EOF with nothing
     to read; the fds are sane.  hsim adds the schedules.
   - deliver_sim, tick_sim: arrivals and ticks keep the relation, and an
     effective version-2 arrival is an effective version-1 one.
*)
Theory lifetimeSimWorld
Ancestors
  llist alist words socketWorld socketFair lifetimeWorld
  lifetimeFair lifetimeFairShape loopHandlesModel
Libs
  preamble

(* ------------------------------------------------------------------------
   Handles are distinct
   ------------------------------------------------------------------------ *)

Theorem hdln_lt:
  hdln lfdn j ≤ j + 1
Proof
  rw[hdln_def]
QED

Theorem hdln_11:
  hdln lfdn j1 = hdln lfdn j2 ⇔ j1 = j2
Proof
  rw[hdln_def]
QED

Theorem hdln_not_lfd:
  hdln lfdn j ≠ lfdn
Proof
  rw[hdln_def]
QED

Theorem hdl_11:
  j1 + 1 < dimword (:64) ∧ j2 + 1 < dimword (:64) ⇒
  (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)
Proof
  rw[hdl_def] >> ‘hdln (w2n lfd) j1 ≤ j1 + 1 ∧ hdln (w2n lfd) j2 ≤ j2 + 1’
    by simp[hdln_lt] >>
  ‘hdln (w2n lfd) j1 < dimword (:64) ∧ hdln (w2n lfd) j2 < dimword (:64)’ by simp[] >>
  simp[hdln_11]
QED

Theorem hdl_not_lfd:
  j + 1 < dimword (:64) ⇒ hdl lfd j ≠ lfd
Proof
  rw[hdl_def] >>
  qspecl_then [‘w2n lfd’, ‘j’] assume_tac (Q.GENL [‘lfdn’, ‘j’] hdln_lt) >>
  ‘hdln (w2n lfd) j < dimword (:64)’ by simp[] >>
  strip_tac >>
  ‘w2n (n2w (hdln (w2n lfd) j) : word64) = hdln (w2n lfd) j’ by simp[] >>
  ‘w2n (n2w (hdln (w2n lfd) j) : word64) = w2n lfd’ by metis_tac[] >>
  metis_tac[hdln_not_lfd]
QED

(* ------------------------------------------------------------------------
   The renamed schedule
   ------------------------------------------------------------------------ *)

Definition rn_arr_def:
  rn_arr lfd k (Connect2 l) = (k + 1, Connect l (hdl lfd k)) ∧
  rn_arr lfd k (Data2 j bs) = (k, Data (hdl lfd j) bs) ∧
  rn_arr lfd k (Eof2 j) = (k, Eof (hdl lfd j))
End

Definition rn_step_def:
  rn_step lfd k [] = (k, []) ∧
  rn_step lfd k (a :: as) =
    let (k1, b) = rn_arr lfd k a;
        (k2, bs) = rn_step lfd k1 as
    in (k2, b :: bs)
End

Definition rn_sched_def:
  rn_sched lfd k ll =
    LUNFOLD (λ(k, ll). case LHD ll of
                       | NONE => NONE
                       | SOME st => SOME ((FST (rn_step lfd k st), THE (LTL ll)),
                                          SND (rn_step lfd k st))) (k, ll)
End

Theorem rn_sched_LHD:
  LHD (rn_sched lfd k ll) = OPTION_MAP (λst. SND (rn_step lfd k st)) (LHD ll)
Proof
  simp[rn_sched_def, Once LUNFOLD] >> CASE_TAC >> simp[]
QED

Theorem rn_sched_LTL:
  LHD ll = SOME st ⇒
  LTL (rn_sched lfd k ll) = SOME (rn_sched lfd (FST (rn_step lfd k st)) (THE (LTL ll)))
Proof
  simp[rn_sched_def, Once LUNFOLD]
QED

(* The version-1 world of a version-2 world *)
Definition v1of_def:
  v1of lfd s2 =
    <| listeners := [(lfd, [])]; conns := []; sched := rn_sched lfd 0 s2.future |>
End

(* ------------------------------------------------------------------------
   The relation
   ------------------------------------------------------------------------ *)

Definition hsim0_def:
  hsim0 lfd s1 (s2, hs) ⇔
    hs.nxt ≤ LENGTH s2.clients ∧
    (s2.clients = [] ∨
     LENGTH s2.reserved + LENGTH s2.listening + LENGTH s2.clients < dimword (:64)) ∧
    s2.listening =
      [(lfd, GENLIST (λi. hs.nxt + i) (LENGTH s2.clients − hs.nxt))] ∧
    s1.listeners =
      [(lfd, GENLIST (λi. hdl lfd (hs.nxt + i)) (LENGTH s2.clients − hs.nxt))] ∧
    MAP FST s1.conns = REVERSE (GENLIST (hdl lfd) (LENGTH s2.clients)) ∧
    (∀j cn. j < LENGTH s2.clients ∧ ALOOKUP s1.conns (hdl lfd j) = SOME cn ⇒
            cn.incoming = (EL j s2.clients).incoming ∧
            cn.peer_closed = (EL j s2.clients).peer_closed) ∧
    (∀j. j < hs.nxt ∧ ALOOKUP hs.tbl (hdl lfd j) = NONE ⇒
         (EL j s2.clients).incoming = [] ∧ (EL j s2.clients).peer_closed) ∧
    (∀h f. ALOOKUP hs.tbl h = SOME f ⇔
           ∃j. j < hs.nxt ∧ h = hdl lfd j ∧ ALOOKUP s2.open_fds f = SOME j) ∧
    (∀f j. ALOOKUP s2.open_fds f = SOME j ⇒ j < hs.nxt) ∧
    ALL_DISTINCT (MAP FST s2.open_fds) ∧ ALL_DISTINCT (MAP SND s2.open_fds) ∧
    (∀f. MEM f (MAP FST s2.open_fds) ⇒ ¬MEM f s2.reserved ∧ f ≠ lfd) ∧
    LENGTH s2.open_fds ≤ hs.nxt ∧ alloc_ok s2.alloc
End

Definition hsim_def:
  hsim lfd s1 (s2, hs) ⇔
    hsim0 lfd s1 (s2, hs) ∧ s1.sched = rn_sched lfd (LENGTH s2.clients) s2.future
End

(* The start: the version-1 world of a version-2 server world *)
Theorem hsim_init:
  s2.listening = [(lfd, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ⇒
  hsim lfd (v1of lfd s2) (s2, hinit)
Proof
  rw[hsim_def, hsim0_def, v1of_def, hinit_def]
QED

Theorem hsim_bound:
  hsim0 lfd s1 (s2, hs) ∧ j < LENGTH s2.clients ⇒ j + 1 < dimword (:64)
Proof
  rw[hsim0_def] >> gvs[]
QED

(* ------------------------------------------------------------------------
   Arrivals
   ------------------------------------------------------------------------ *)

(* The connections of s1 are the handles of the clients *)
Theorem hsim0_is_conn:
  hsim0 lfd s1 (s2, hs) ⇒
  (is_conn s1 c ⇔ ∃j. j < LENGTH s2.clients ∧ c = hdl lfd j)
Proof
  rw[hsim0_def, is_conn_def, ALOOKUP_NONE, MEM_GENLIST] >> metis_tac[]
QED

Theorem hsim0_conn:
  hsim0 lfd s1 (s2, hs) ∧ j < LENGTH s2.clients ⇒
  ∃cn. ALOOKUP s1.conns (hdl lfd j) = SOME cn ∧
       cn.incoming = (EL j s2.clients).incoming ∧
       cn.peer_closed = (EL j s2.clients).peer_closed
Proof
  strip_tac >>
  ‘is_conn s1 (hdl lfd j)’ by (drule hsim0_is_conn >> simp[] >> metis_tac[]) >>
  gvs[is_conn_def] >> Cases_on ‘ALOOKUP s1.conns (hdl lfd j)’ >> gvs[] >>
  gvs[hsim0_def]
QED

Theorem hsim0_bound:
  hsim0 lfd s1 (s2, hs) ∧ s2.clients ≠ [] ⇒ LENGTH s2.clients + 1 < dimword (:64)
Proof
  rw[hsim0_def] >> gvs[]
QED

Theorem hdl_neq:
  j1 < k ∧ j2 < k ∧ k < dimword (:64) ∧ j1 ≠ j2 ⇒ hdl lfd j1 ≠ hdl lfd j2
Proof
  rpt strip_tac >>
  qspecl_then [‘lfd’, ‘j1’, ‘j2’] mp_tac (Q.GENL [‘lfd’, ‘j1’, ‘j2’] hdl_11) >>
  impl_tac >- fs[] >> fs[]
QED

(* A new client connects *)
Theorem deliver_sim_connect:
  hsim0 lfd s1 (s2, hs) ∧
  LENGTH s2.reserved + LENGTH s2.listening + LENGTH s2.clients + 1 < dimword (:64) ⇒
  arrival_ok s1 (Connect lfd (hdl lfd (LENGTH s2.clients))) ∧
  hsim0 lfd (deliver1 s1 (Connect lfd (hdl lfd (LENGTH s2.clients))))
            (deliver2 s2 (Connect2 lfd), hs)
Proof
  strip_tac >>
  qpat_assum ‘hsim0 _ _ _’
    (fn th => MAP_EVERY assume_tac (CONJUNCTS (REWRITE_RULE[hsim0_def] th))) >>
  qabbrev_tac ‘k = LENGTH s2.clients’ >>
  ‘k + 1 < dimword (:64)’ by gvs[] >>
  ‘hdl lfd k ≠ lfd’ by simp[hdl_not_lfd] >>
  ‘¬is_conn s1 (hdl lfd k)’
    by (drule hsim0_is_conn >> simp[] >> rpt strip_tac >>
        qspecl_then [‘j’, ‘k’, ‘k + 1’, ‘lfd’] mp_tac
          (Q.GENL [‘j1’,‘j2’,‘k’,‘lfd’] hdl_neq) >> simp[]) >>
  ‘is_listener s1 lfd ∧ ¬is_listener s1 (hdl lfd k)’ by gvs[is_listener_def] >>
  conj_tac >- simp[arrival_ok_def] >>
  simp[deliver1_def, deliver2_def] >>
  qpat_assum ‘s1.listeners = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_assum ‘s2.listening = _’ (fn th => REWRITE_TAC[th]) >>
  ‘k + 1 − hs.nxt = SUC (k − hs.nxt)’ by simp[Abbr ‘k’] >>
  simp[hsim0_def] >>
  ‘k − hs.nxt + hs.nxt = k’ by simp[Abbr ‘k’] >>
  rpt conj_tac
  >- gvs[]
  >- simp[AFUPDKEY_def, GENLIST, SNOC_APPEND]
  >- simp[AFUPDKEY_def, GENLIST, SNOC_APPEND]
  >- simp[GENLIST, REVERSE_SNOC, GSYM ADD1]
  >- (rpt gen_tac >> Cases_on ‘j = k’ >> simp[Abbr ‘k’, EL_APPEND2, empty_conn_def] >>
      strip_tac >> ‘j < LENGTH s2.clients’ by simp[] >>
      ‘hdl lfd j ≠ hdl lfd (LENGTH s2.clients)’
        by (qspecl_then [‘j’, ‘LENGTH s2.clients’, ‘LENGTH s2.clients + 1’, ‘lfd’] mp_tac
              (Q.GENL [‘j1’,‘j2’,‘k’,‘lfd’] hdl_neq) >> simp[]) >>
      gvs[EL_APPEND1] >>
      qpat_x_assum ‘∀j cn. j < _ ∧ _ ⇒ _’ (qspecl_then [‘j’,‘cn’] mp_tac) >> simp[])
  >- (rw[] >> ‘j < LENGTH s2.clients’ by simp[] >> simp[EL_APPEND1] >>
      qpat_x_assum ‘∀j. j < hs.nxt ∧ _ ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[])
  >> metis_tac[]
QED

(* A client still open on the server side is not at EOF *)
Theorem hsim0_closed_eof[local]:
  hsim0 lfd s1 (s2, hs) ∧ j < hs.nxt ∧ ALOOKUP hs.tbl (hdl lfd j) = NONE ⇒
  (EL j s2.clients).peer_closed
Proof
  rw[hsim0_def] >> metis_tac[]
QED

(* Data from client j *)
Theorem deliver_sim_data:
  hsim0 lfd s1 (s2, hs) ∧ j < LENGTH s2.clients ∧ ¬(EL j s2.clients).peer_closed ⇒
  arrival_ok s1 (Data (hdl lfd j) bs) ∧
  hsim0 lfd (deliver1 s1 (Data (hdl lfd j) bs)) (deliver2 s2 (Data2 j bs), hs)
Proof
  strip_tac >> drule_all hsim0_conn >> strip_tac >>
  conj_tac >- simp[arrival_ok_def] >>
  ‘s2.clients ≠ []’ by (strip_tac >> gvs[]) >>
  drule_all hsim0_bound >> strip_tac >>
  simp[deliver1_def, deliver2_def, update_client_def] >>
  gvs[hsim0_def, AFUPDKEY_ALOOKUP, EL_LUPDATE] >> rpt conj_tac
  >- (rpt gen_tac >> Cases_on ‘j' = j’ >> simp[] >> strip_tac >> gvs[] >>
      TRY (qpat_assum ‘∀j cn. j < _ ∧ _ ⇒ _’ (qspecl_then [‘j’,‘cn’] mp_tac) >>
           impl_tac >- fs[] >> strip_tac >> fs[] >> NO_TAC)
      >> ‘hdl lfd j' ≠ hdl lfd j’
           by (qspecl_then [‘j'’,‘j’,‘LENGTH s2.clients + 1’,‘lfd’] mp_tac
                 (Q.GENL [‘j1’,‘j2’,‘k’,‘lfd’] hdl_neq) >> impl_tac >- fs[] >> simp[])
      >> Cases_on ‘ALOOKUP s1.conns (hdl lfd j')’ >> gvs[]
      >> qpat_assum ‘∀j cn. j < _ ∧ _ ⇒ _’ (qspecl_then [‘j'’,‘cn'’] mp_tac) >> fs[])
  >- (rpt gen_tac >> strip_tac >> Cases_on ‘j' = j’ >> gvs[] >>
      qpat_assum ‘∀j. j < hs.nxt ∧ _ ⇒ _’ (qspec_then ‘j'’ mp_tac) >> fs[])
  >> metis_tac[]
QED

(* EOF from client j *)
Theorem deliver_sim_eof:
  hsim0 lfd s1 (s2, hs) ∧ j < LENGTH s2.clients ∧ ¬(EL j s2.clients).peer_closed ⇒
  arrival_ok s1 (Eof (hdl lfd j)) ∧
  hsim0 lfd (deliver1 s1 (Eof (hdl lfd j))) (deliver2 s2 (Eof2 j), hs)
Proof
  strip_tac >> drule_all hsim0_conn >> strip_tac >>
  conj_tac >- simp[arrival_ok_def] >>
  ‘s2.clients ≠ []’ by (strip_tac >> gvs[]) >>
  drule_all hsim0_bound >> strip_tac >>
  simp[deliver1_def, deliver2_def, update_client_def] >>
  gvs[hsim0_def, AFUPDKEY_ALOOKUP, EL_LUPDATE] >> rpt conj_tac
  >- (rpt gen_tac >> Cases_on ‘j' = j’ >> simp[] >> strip_tac >> gvs[] >>
      TRY (qpat_assum ‘∀j cn. j < _ ∧ _ ⇒ _’ (qspecl_then [‘j’,‘cn’] mp_tac) >>
           impl_tac >- fs[] >> strip_tac >> fs[] >> NO_TAC)
      >> ‘hdl lfd j' ≠ hdl lfd j’
           by (qspecl_then [‘j'’,‘j’,‘LENGTH s2.clients + 1’,‘lfd’] mp_tac
                 (Q.GENL [‘j1’,‘j2’,‘k’,‘lfd’] hdl_neq) >> impl_tac >- fs[] >> simp[])
      >> Cases_on ‘ALOOKUP s1.conns (hdl lfd j')’ >> gvs[]
      >> qpat_assum ‘∀j cn. j < _ ∧ _ ⇒ _’ (qspecl_then [‘j'’,‘cn'’] mp_tac) >> fs[])
  >- (rpt gen_tac >> strip_tac >> Cases_on ‘j' = j’ >> gvs[] >>
      qpat_assum ‘∀j. j < hs.nxt ∧ _ ⇒ _’ (qspec_then ‘j'’ mp_tac) >> fs[])
  >> metis_tac[]
QED

(* MAIN: an effective version-2 arrival is an effective version-1 arrival
   (renamed), and delivering both keeps the relation *)
Theorem deliver_sim:
  hsim0 lfd s1 (s2, hs) ∧ arrival_ok2 s2 a2 ∧
  rn_arr lfd (LENGTH s2.clients) a2 = (k', b) ⇒
  arrival_ok s1 b ∧ hsim0 lfd (deliver1 s1 b) (deliver2 s2 a2, hs) ∧
  LENGTH (deliver2 s2 a2).clients = k' ∧
  (deliver2 s2 a2).future = s2.future
Proof
  Cases_on ‘a2’ >> simp[rn_arr_def] >> strip_tac >> gvs[arrival_ok2_def]
  >- (‘∃q. s2.listening = [(lfd,q)]’ by fs[hsim0_def] >>
      ‘c = lfd’ by (CCONTR_TAC >> gvs[]) >> gvs[] >>
      drule deliver_sim_connect >> impl_tac >- fs[] >>
      strip_tac >> simp[] >> gvs[deliver2_def])
  >- (drule_all deliver_sim_data >> simp[deliver2_def, update_client_def])
  >> drule_all deliver_sim_eof >> simp[deliver2_def, update_client_def]
QED
