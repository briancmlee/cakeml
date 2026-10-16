(*
  The proof of lifetime_core_link (lifetimeCore): conservativity of the
  lifetimes world over the core world.

  - The fds: without closes, client j's fd is core_fd sk j; these are
    distinct, and none is the listener or a reserved fd (alloc_ok and
    lifetime_fair's bound on the number of clients).
  - The worlds: lsim relates a core state to a lifetimes state (the
    listener's queue on the clients' fds; client j's stream on core_fd
    sk j; the accepted clients open on their fds; the schedules related
    by core_sched).  Time (tick) and every socket call on the listener
    or an accepted fd keep it, with the same answer.
  - The runs: along a run whose calls are allowed (call_ok), the two
    oracles answer the same, so semantics_prog_upto (ffiAgreeUpto) gives
    the same behaviour, in both directions.

  A LEAF: nothing else depends on this theory.
*)
Theory lifetimeCoreProof
Ancestors
  pair list rich_list arithmetic option llist alist words
  ffi semantics evaluate evaluateProps ml_prog
  socketWorld socketFair EchoSpec
  lifetimeWorld lifetimeFair EchoEpisodesSpec lifetimeFairShape ffiAgreeUpto lifetimeCore
Libs
  preamble

(* ------------------------------------------------------------------------
   The fds of the accepts
   ------------------------------------------------------------------------ *)

Theorem core_fds_GENLIST:
  ∀j. core_fds sk j = REVERSE (GENLIST (core_fd sk) j)
Proof
  Induct >> simp[core_fds_def, GENLIST, REVERSE_SNOC] >>
  simp[core_fd_def, core_fds_def]
QED

Theorem LENGTH_core_fds[simp]:
  LENGTH (core_fds sk j) = j
Proof
  simp[core_fds_GENLIST]
QED

Theorem MEM_core_fds:
  MEM f (core_fds sk j) ⇔ ∃i. i < j ∧ f = core_fd sk i
Proof
  simp[core_fds_GENLIST, MEM_GENLIST] >> metis_tac[]
QED

Theorem core_fd_eq:
  core_fd sk j = sk.alloc j (sk.reserved ++ MAP FST sk.listening ++ core_fds sk j)
Proof
  simp[core_fd_def, core_fds_def]
QED

(* Room for the first n clients (vacuous before any client connects) *)
Definition room_def:
  room sk n ⇔ n = 0 ∨ LENGTH sk.reserved + LENGTH sk.listening + n < dimword (:64)
End

Theorem room_lt:
  room sk n ∧ j < n ⇒ room sk (SUC j)
Proof
  rw[room_def] >> simp[]
QED

Theorem core_fd_fresh:
  alloc_ok sk.alloc ∧ room sk (SUC j) ⇒
  ¬MEM (core_fd sk j) (sk.reserved ++ MAP FST sk.listening ++ core_fds sk j)
Proof
  strip_tac >> REWRITE_TAC[core_fd_eq] >> fs[alloc_ok_def, room_def] >>
  first_x_assum irule >> simp[]
QED

Theorem core_fd_11:
  alloc_ok sk.alloc ∧ room sk n ∧ i < n ∧ j < n ⇒
  (core_fd sk i = core_fd sk j ⇔ i = j)
Proof
  strip_tac >> reverse eq_tac >- simp[] >> strip_tac >> CCONTR_TAC >>
  ‘i < j ∨ j < i’ by decide_tac
  >- (‘room sk (SUC j)’ by metis_tac[room_lt] >>
      ‘¬MEM (core_fd sk j) (core_fds sk j)’ by (drule_all core_fd_fresh >> simp[]) >>
      gvs[MEM_core_fds] >> metis_tac[])
  >> ‘room sk (SUC i)’ by metis_tac[room_lt] >>
  ‘¬MEM (core_fd sk i) (core_fds sk i)’ by (drule_all core_fd_fresh >> simp[]) >>
  gvs[MEM_core_fds] >> metis_tac[]
QED

Theorem core_fd_not_listener:
  alloc_ok sk.alloc ∧ room sk n ∧ j < n ∧ MEM l (MAP FST sk.listening) ⇒
  core_fd sk j ≠ l
Proof
  strip_tac >> ‘room sk (SUC j)’ by metis_tac[room_lt] >>
  drule_all core_fd_fresh >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The core world's connections: client j's stream on core_fd sk j
   ------------------------------------------------------------------------ *)

Definition conns_of_def:
  conns_of sk (cl : conn list) = REVERSE (GENLIST (λj. (core_fd sk j, EL j cl)) (LENGTH cl))
End

Theorem conns_of_NIL[simp]:
  conns_of sk [] = []
Proof
  simp[conns_of_def]
QED

Theorem conns_of_SNOC:
  conns_of sk (SNOC c cl) = (core_fd sk (LENGTH cl), c) :: conns_of sk cl
Proof
  simp[conns_of_def, GENLIST, REVERSE_SNOC, EL_LENGTH_SNOC] >>
  simp[GENLIST_FUN_EQ, EL_SNOC]
QED

Theorem ALOOKUP_conns_of:
  ∀cl j. alloc_ok sk.alloc ∧ room sk (LENGTH cl) ∧ j < LENGTH cl ⇒
         ALOOKUP (conns_of sk cl) (core_fd sk j) = SOME (EL j cl)
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[conns_of_SNOC, room_def] >> rpt strip_tac >>
  Cases_on ‘j = LENGTH cl’ >> simp[EL_LENGTH_SNOC] >>
  ‘core_fd sk j ≠ core_fd sk (LENGTH cl)’
    by (drule core_fd_11 >> disch_then (qspec_then ‘SUC (LENGTH cl)’ mp_tac) >> simp[room_def]) >>
  simp[EL_SNOC]
QED

Theorem ALOOKUP_conns_of_NONE:
  ∀cl. (∀j. j < LENGTH cl ⇒ f ≠ core_fd sk j) ⇒ ALOOKUP (conns_of sk cl) f = NONE
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[conns_of_SNOC] >> rpt strip_tac >>
  first_x_assum irule >> rw[] >> first_x_assum irule >> simp[]
QED

Theorem AFUPDKEY_conns_of:
  ∀cl j. alloc_ok sk.alloc ∧ room sk (LENGTH cl) ∧ j < LENGTH cl ⇒
         AFUPDKEY (core_fd sk j) g (conns_of sk cl) =
         conns_of sk (LUPDATE (g (EL j cl)) j cl)
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[conns_of_SNOC, room_def] >> rpt strip_tac >>
  Cases_on ‘j = LENGTH cl’
  >- (simp[AFUPDKEY_def, EL_LENGTH_SNOC, LUPDATE_SNOC, conns_of_SNOC]) >>
  ‘core_fd sk j ≠ core_fd sk (LENGTH cl)’
    by (drule core_fd_11 >> disch_then (qspec_then ‘SUC (LENGTH cl)’ mp_tac) >> simp[room_def]) >>
  simp[AFUPDKEY_def, LUPDATE_SNOC, conns_of_SNOC, EL_SNOC]
QED

(* Lists of clients with the same length and the same EOF flags *)
Theorem LENGTH_LUPDATE_conns[simp]:
  LENGTH (LUPDATE x j (cl : conn list)) = LENGTH cl
Proof
  simp[]
QED

(* The accepted clients, newest first, on their fds *)
Definition open_of_def:
  open_of sk k = REVERSE (GENLIST (λj. (core_fd sk j, j)) k)
End

Theorem open_of_SUC:
  open_of sk (SUC k) = (core_fd sk k, k) :: open_of sk k
Proof
  simp[open_of_def, GENLIST, REVERSE_SNOC]
QED

Theorem LENGTH_open_of[simp]:
  LENGTH (open_of sk k) = k
Proof
  simp[open_of_def]
QED

Theorem MAP_FST_open_of:
  MAP FST (open_of sk k) = core_fds sk k
Proof
  Induct_on ‘k’ >> simp[open_of_SUC, core_fds_def, core_fd_eq] >> simp[open_of_def]
QED

Theorem ALOOKUP_open_of:
  ∀k j. alloc_ok sk.alloc ∧ room sk k ∧ j < k ⇒
        ALOOKUP (open_of sk k) (core_fd sk j) = SOME j
Proof
  Induct >> simp[open_of_SUC, room_def] >> rpt strip_tac >>
  Cases_on ‘j = k’ >> simp[] >>
  ‘core_fd sk k ≠ core_fd sk j’
    by (drule core_fd_11 >> disch_then (qspec_then ‘SUC k’ mp_tac) >> simp[room_def]) >>
  simp[room_def]
QED

Theorem ALOOKUP_open_of_NONE:
  ∀k. (∀j. j < k ⇒ f ≠ core_fd sk j) ⇒ ALOOKUP (open_of sk k) f = NONE
Proof
  Induct >> simp[open_of_SUC, open_of_def] >> rw[] >>
  fs[GSYM open_of_def] >> first_x_assum irule >> rw[] >> first_x_assum irule >> simp[]
QED

(* ------------------------------------------------------------------------
   The core schedule
   ------------------------------------------------------------------------ *)

Theorem core_sched_LHD:
  LHD (core_sched sk n ll) = OPTION_MAP (core_step sk n) (LHD ll)
Proof
  simp[core_sched_def] >> Cases_on ‘LHD ll’ >> simp[]
QED

Theorem core_sched_LTL:
  LHD ll = SOME st ⇒
  THE (LTL (core_sched sk n ll)) =
  core_sched sk (n + LENGTH (FILTER is_connect2 st)) (THE (LTL ll))
Proof
  simp[core_sched_def]
QED

(* ------------------------------------------------------------------------
   The simulation
   ------------------------------------------------------------------------ *)

(* The states, apart from the schedules: k clients accepted (on their
   fds), the others queued on the listener, every client's stream on its
   fd in the core world *)
Definition lsim0_def:
  lsim0 sk lfd (s1 : sockets) (s2 : sockets2) ⇔
    sk.listening = [(lfd, [])] ∧ alloc_ok sk.alloc ∧
    s2.reserved = sk.reserved ∧ s2.alloc = sk.alloc ∧
    room sk (LENGTH s2.clients) ∧
    ∃k. k ≤ LENGTH s2.clients ∧
        s2.listening = [(lfd, GENLIST (λi. k + i) (LENGTH s2.clients − k))] ∧
        s2.open_fds = open_of sk k ∧
        s1.listeners = [(lfd, GENLIST (λi. core_fd sk (k + i)) (LENGTH s2.clients − k))] ∧
        s1.conns = conns_of sk s2.clients
End

Definition lsim_def:
  lsim sk lfd s1 s2 ⇔
    lsim0 sk lfd s1 s2 ∧ lifetime_fair s2 ∧
    s1.sched = core_sched sk (LENGTH s2.clients) s2.future
End

(* The listener is not a client's fd *)
Theorem lsim0_fd_not_lfd:
  lsim0 sk lfd s1 s2 ∧ j < LENGTH s2.clients ⇒ core_fd sk j ≠ lfd
Proof
  strip_tac >>
  qpat_x_assum ‘lsim0 _ _ _ _’ (strip_assume_tac o REWRITE_RULE[lsim0_def]) >>
  qspecl_then [‘sk’, ‘LENGTH s2.clients’, ‘j’, ‘lfd’] mp_tac
    (Q.GENL [‘sk’, ‘n’, ‘j’, ‘l’] core_fd_not_listener) >>
  asm_rewrite_tac[] >> simp[]
QED

(* ------------------------------------------------------------------------
   Arrivals
   ------------------------------------------------------------------------ *)

Theorem step_ok2_future:
  ∀st s. step_ok2 (s with future := x) st ⇔ step_ok2 s st
Proof
  Induct >> simp[step_ok2_def] >> rpt gen_tac >>
  ‘deliver2 (s with future := x) h = deliver2 s h with future := x’
    by (Cases_on ‘h’ >> rw[deliver2_def, update_client_def]) >>
  Cases_on ‘h’ >> simp[arrival_ok2_def]
QED

Theorem deliver_lsim0:
  lsim0 sk lfd s1 s2 ∧ arrival_ok2 s2 a ⇒
  lsim0 sk lfd (deliver1 s1 (core_arrival sk (LENGTH s2.clients) a)) (deliver2 s2 a) ∧
  LENGTH (deliver2 s2 a).clients = LENGTH s2.clients + (if is_connect2 a then 1 else 0)
Proof
  Cases_on ‘a’ >> simp[arrival_ok2_def, core_arrival_def, is_connect2_def] >> strip_tac
  (* a client connects *)
  >- (‘room sk (SUC (LENGTH s2.clients))’ by gvs[lsim0_def, room_def] >>
      ‘alloc_ok sk.alloc ∧ MEM lfd (MAP FST sk.listening)’ by gvs[lsim0_def] >>
      ‘core_fd sk (LENGTH s2.clients) ≠ lfd’
        by (qspecl_then [‘sk’, ‘SUC (LENGTH s2.clients)’, ‘LENGTH s2.clients’, ‘lfd’] mp_tac
              (Q.GENL [‘sk’, ‘n’, ‘j’, ‘l’] core_fd_not_listener) >>
            asm_rewrite_tac[] >> simp[]) >>
      ‘∀j. j < LENGTH s2.clients ⇒ core_fd sk (LENGTH s2.clients) ≠ core_fd sk j’
        by (rpt strip_tac >>
            qspecl_then [‘sk’, ‘SUC (LENGTH s2.clients)’, ‘LENGTH s2.clients’, ‘j’] mp_tac
              (Q.GENL [‘sk’, ‘n’, ‘i’, ‘j’] core_fd_11) >>
            asm_rewrite_tac[] >> simp[]) >>
      ‘ALOOKUP (conns_of sk s2.clients) (core_fd sk (LENGTH s2.clients)) = NONE’
        by (irule ALOOKUP_conns_of_NONE >> metis_tac[]) >>
      gvs[lsim0_def] >>
      simp[deliver1_def, deliver2_def, is_listener_def, is_conn_def, AFUPDKEY_def] >>
      conj_tac >- simp[GSYM ADD1] >> qexists_tac ‘k’ >>
      simp[GSYM SNOC_APPEND, conns_of_SNOC, GSYM ADD1] >>
      ‘SUC (LENGTH s2.clients) − k = SUC (LENGTH s2.clients − k)’ by simp[] >>
      simp[GENLIST, SNOC_APPEND])
  (* data *)
  >- (gvs[lsim0_def] >> rename1 ‘Data2 j bs’ >>
      simp[deliver1_def, deliver2_def, update_client_def] >>
      qspecl_then [‘sk’, ‘λcn. if cn.peer_closed then cn else cn with incoming := cn.incoming ++ bs’,
                   ‘s2.clients’, ‘j’] mp_tac (Q.GENL [‘sk’, ‘g’] AFUPDKEY_conns_of) >>
      impl_tac >- simp[] >>
      simp[] >> strip_tac >> rpt conj_tac >> TRY (qexists_tac ‘k’) >> simp[])
  (* EOF *)
  >> gvs[lsim0_def] >> rename1 ‘Eof2 j’ >>
  simp[deliver1_def, deliver2_def, update_client_def] >>
  qspecl_then [‘sk’, ‘λcn. cn with peer_closed := T’, ‘s2.clients’, ‘j’] mp_tac
    (Q.GENL [‘sk’, ‘g’] AFUPDKEY_conns_of) >>
  impl_tac >- simp[] >>
  simp[] >> strip_tac >> rpt conj_tac >> TRY (qexists_tac ‘k’) >> simp[]
QED

Theorem FOLDL_deliver1_sched[simp]:
  ∀l s. (FOLDL deliver1 s l).sched = s.sched
Proof
  Induct >> simp[] >> Cases >> rw[deliver1_def]
QED

Theorem FOLDL_deliver2_future[simp]:
  ∀l s. (FOLDL deliver2 s l).future = s.future
Proof
  Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def]
QED

Theorem lsim0_sched[simp]:
  (lsim0 sk lfd (s1 with sched := x) s2 ⇔ lsim0 sk lfd s1 s2) ∧
  (lsim0 sk lfd s1 (s2 with future := y) ⇔ lsim0 sk lfd s1 s2)
Proof
  simp[lsim0_def]
QED

Theorem deliver_step_lsim0:
  ∀st s1 s2.
    lsim0 sk lfd s1 s2 ∧ step_ok2 s2 st ⇒
    lsim0 sk lfd (FOLDL deliver1 s1 (core_step sk (LENGTH s2.clients) st)) (FOLDL deliver2 s2 st) ∧
    LENGTH (FOLDL deliver2 s2 st).clients = LENGTH s2.clients + LENGTH (FILTER is_connect2 st)
Proof
  Induct >> simp[core_step_def, step_ok2_def] >> rpt gen_tac >> strip_tac >>
  drule_all deliver_lsim0 >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >> Cases_on ‘is_connect2 h’ >> gvs[ADD1]
QED

(* MAIN (time): a tick keeps the simulation *)
Theorem tick_lsim:
  lsim sk lfd s1 s2 ⇒ lsim sk lfd (tick s1) (tick2 s2)
Proof
  rw[lsim_def] >> drule lifetime_fair_tick >> strip_tac >> simp[] >>
  simp[tick_def, tick2_def, core_sched_LHD] >>
  Cases_on ‘LHD s2.future’ >> simp[deliver_def] >>
  rename1 ‘LHD s2.future = SOME st’ >>
  ‘step_ok2 (s2 with future := THE (LTL s2.future)) st’
    by gvs[step_ok2_future, next_step2_def] >>
  ‘lsim0 sk lfd (s1 with sched := THE (LTL s1.sched)) (s2 with future := THE (LTL s2.future))’
    by simp[] >>
  drule_all deliver_step_lsim0 >> simp[] >> strip_tac >>
  drule core_sched_LTL >> simp[]
QED

(* ------------------------------------------------------------------------
   The socket calls, on the listener and accepted fds
   ------------------------------------------------------------------------ *)

(* An fd a call may name: the listener, or an accepted connection *)
Definition ok_fd_def:
  ok_fd lfd (s2 : sockets2) f ⇔ f = lfd ∨ MEM f (MAP FST s2.open_fds)
End

(* An accepted fd is some client's, accepted in order *)
Theorem lsim0_ok_fd:
  lsim0 sk lfd s1 s2 ∧ ok_fd lfd s2 f ⇒
  f = lfd ∨ ∃j k. f = core_fd sk j ∧ j < k ∧ k ≤ LENGTH s2.clients ∧ s2.open_fds = open_of sk k
Proof
  rw[lsim0_def, ok_fd_def] >> gvs[MAP_FST_open_of, MEM_core_fds] >> metis_tac[]
QED

Theorem lsim0_lfd_lookups:
  lsim0 sk lfd s1 s2 ⇒
  ALOOKUP s1.conns lfd = NONE ∧ ALOOKUP s2.open_fds lfd = NONE
Proof
  strip_tac >>
  ‘∀j. j < LENGTH s2.clients ⇒ core_fd sk j ≠ lfd’ by metis_tac[lsim0_fd_not_lfd] >>
  gvs[lsim0_def] >> conj_tac
  >- (irule ALOOKUP_conns_of_NONE >> metis_tac[]) >>
  irule ALOOKUP_open_of_NONE >> rw[] >> first_x_assum irule >> simp[]
QED

Theorem lsim0_fd_lookups:
  lsim0 sk lfd s1 s2 ∧ s2.open_fds = open_of sk k ∧ j < k ∧ k ≤ LENGTH s2.clients ⇒
  ALOOKUP s1.conns (core_fd sk j) = SOME (EL j s2.clients) ∧
  ALOOKUP s1.listeners (core_fd sk j) = NONE ∧
  ALOOKUP s2.listening (core_fd sk j) = NONE ∧
  client_of s2 (core_fd sk j) = SOME j
Proof
  strip_tac >>
  ‘core_fd sk j ≠ lfd’ by (irule lsim0_fd_not_lfd >> qexistsl [‘s1’, ‘s2’] >> simp[room_def]) >>
  gvs[lsim0_def, room_def] >>
  ‘k' = k’ by metis_tac[LENGTH_open_of] >> gvs[room_def] >>
  ‘ALOOKUP (open_of sk k) (core_fd sk j) = SOME j’
    by (irule ALOOKUP_open_of >> gvs[room_def]) >>
  gvs[client_of_def] >>
  irule ALOOKUP_conns_of >> simp[room_def]
QED

Theorem is_ready_lsim:
  lsim0 sk lfd s1 s2 ∧ ok_fd lfd s2 f ⇒ (is_ready s1 f ⇔ is_ready2 s2 f)
Proof
  strip_tac >> drule_all lsim0_ok_fd >> strip_tac
  >- (drule lsim0_lfd_lookups >> strip_tac >> gvs[lsim0_def] >>
      simp[is_ready_def, is_ready2_def, client_of_def] >>
      ‘k ≤ LENGTH s2.clients’ by simp[] >>
      simp[GENLIST_EQ_NIL])
  >> drule_all lsim0_fd_lookups >> strip_tac >>
  simp[is_ready_def, is_ready2_def]
QED

(* An update of client j's stream, in both worlds *)
Theorem lsim0_update:
  lsim0 sk lfd s1 s2 ∧ s2.open_fds = open_of sk k ∧ j < k ∧ k ≤ LENGTH s2.clients ⇒
  lsim0 sk lfd (s1 with conns := AFUPDKEY (core_fd sk j) g s1.conns)
               (update_client j g s2)
Proof
  strip_tac >> gvs[lsim0_def, update_client_def] >>
  qspecl_then [‘sk’, ‘g’, ‘s2.clients’, ‘j’] mp_tac (Q.GENL [‘sk’, ‘g’] AFUPDKEY_conns_of) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >> qexists_tac ‘k'’ >> simp[]
QED

Theorem read_lsim:
  lsim0 sk lfd s1 s2 ∧ ok_fd lfd s2 f ⇒
  (sock_read f n s1 = NONE ∧ sock_read2 f n s2 = NONE) ∨
  ∃r s1' s2'. sock_read f n s1 = SOME (r, s1') ∧ sock_read2 f n s2 = SOME (r, s2') ∧
              lsim0 sk lfd s1' s2' ∧ s1'.sched = s1.sched ∧ s2'.future = s2.future ∧
              s2'.open_fds = s2.open_fds ∧ LENGTH s2'.clients = LENGTH s2.clients
Proof
  strip_tac >> drule_all lsim0_ok_fd >> strip_tac
  >- (drule lsim0_lfd_lookups >> strip_tac >> disj1_tac >>
      simp[sock_read_def, sock_read2_def, client_of_def]) >>
  disj2_tac >> drule_all lsim0_fd_lookups >> strip_tac >>
  simp[sock_read_def, sock_read2_def] >>
  rw[] >> simp[update_client_def] >>
  qspecl_then [‘k’, ‘j’, ‘λcn. cn with incoming := DROP n cn.incoming’] mp_tac
    (Q.GENL [‘k’, ‘j’, ‘g’] lsim0_update) >>
  simp[update_client_def]
QED

Theorem write_lsim:
  lsim0 sk lfd s1 s2 ∧ ok_fd lfd s2 f ⇒
  (sock_write f bs s1 = NONE ∧ sock_write2 f bs s2 = NONE) ∨
  ∃s1' s2'. sock_write f bs s1 = SOME s1' ∧ sock_write2 f bs s2 = SOME s2' ∧
            lsim0 sk lfd s1' s2' ∧ s1'.sched = s1.sched ∧ s2'.future = s2.future ∧
            s2'.open_fds = s2.open_fds ∧ LENGTH s2'.clients = LENGTH s2.clients
Proof
  strip_tac >> drule_all lsim0_ok_fd >> strip_tac
  >- (drule lsim0_lfd_lookups >> strip_tac >> disj1_tac >>
      simp[sock_write_def, sock_write2_def, client_of_def]) >>
  disj2_tac >> drule_all lsim0_fd_lookups >> strip_tac >>
  simp[sock_write_def, sock_write2_def, update_client_def] >>
  qspecl_then [‘k’, ‘j’, ‘λcn. cn with outgoing := cn.outgoing ++ bs’] mp_tac
    (Q.GENL [‘k’, ‘j’, ‘g’] lsim0_update) >>
  simp[update_client_def]
QED

Theorem accept_lsim:
  lsim0 sk lfd s1 s2 ⇒
  (sock_accept l s1 = NONE ∧ sock_accept2 l s2 = NONE) ∨
  ∃r s1' s2'. sock_accept l s1 = SOME (r, s1') ∧ sock_accept2 l s2 = SOME (r, s2') ∧
              lsim0 sk lfd s1' s2' ∧ s1'.sched = s1.sched ∧ s2'.future = s2.future ∧
              LENGTH s2'.clients = LENGTH s2.clients ∧
              MAP FST s2'.open_fds = (case r of SOME f => [f] | NONE => []) ++ MAP FST s2.open_fds
Proof
  strip_tac >> Cases_on ‘l = lfd’
  >- (disj2_tac >> gvs[lsim0_def] >>
      simp[sock_accept_def, sock_accept2_def] >>
      Cases_on ‘LENGTH s2.clients − k’ >> simp[]
      >- (rpt conj_tac >> TRY (qexists_tac ‘k’) >> simp[]) >>
      rename1 ‘_ = SUC m’ >>
      simp[GENLIST_CONS, used_fds_def, MAP_FST_open_of] >>
      ‘LENGTH sk.reserved + SUC k < dimword (:64)’ by gvs[room_def] >>
      simp[] >>
      ‘sk.alloc k (sk.reserved ++ [l] ++ core_fds sk k) = core_fd sk k’
        by simp[core_fd_eq] >>
      gvs[] >> simp[AFUPDKEY_def, combinTheory.o_DEF, MAP_FST_open_of] >>
      qexists_tac ‘SUC k’ >> simp[open_of_SUC, ADD1] >>
      ‘LENGTH s2.clients − (k + 1) = m’ by simp[] >>
      simp[GENLIST_FUN_EQ])
  >> disj1_tac >> gvs[lsim0_def] >>
  simp[sock_accept_def, sock_accept2_def]
QED

Theorem FOLDL_deliver2_open_fds[simp]:
  ∀l s. (FOLDL deliver2 s l).open_fds = s.open_fds
Proof
  Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def]
QED

Theorem tick2_open_fds[simp]:
  (tick2 s).open_fds = s.open_fds
Proof
  rw[tick2_def] >> CASE_TAC >> simp[]
QED

(* ------------------------------------------------------------------------
   The oracles
   ------------------------------------------------------------------------ *)

(* A call allowed after the fds A were accepted *)
Definition allowed_def:
  allowed lfd A n conf ⇔
    n ≠ ExtCall «sock_close» ∧ EVERY (λf. f = lfd ∨ MEM f A) (call_fds n conf)
End

(* The fd an answer to «sock_accept» hands out (as EchoEpisodesSpec's event_accepted) *)
Definition acc_of_def:
  acc_of n (out : word8 list) =
    if n = ExtCall «sock_accept» ∧ LENGTH out = 9 ∧ HD out = 1w
    then [bytes_fd (TL out)] else []
End

(* MAIN (calls): an allowed call gets the same answer from both worlds, and
   the simulation goes on *)
Theorem oracle_lsim:
  lsim sk lfd s1 s2 ∧ (∀f. MEM f A ⇔ MEM f (MAP FST s2.open_fds)) ∧
  allowed lfd A n conf ⇒
  (∃out s1' s2'. socket_oracle n s1 conf bytes = Oracle_return s1' out ∧
                 socket2_oracle n s2 conf bytes = Oracle_return s2' out ∧
                 lsim sk lfd s1' s2' ∧
                 ∀f. MEM f (A ++ acc_of n out) ⇔ MEM f (MAP FST s2'.open_fds)) ∨
  (∃res. socket_oracle n s1 conf bytes = Oracle_final res ∧
         socket2_oracle n s2 conf bytes = Oracle_final res)
Proof
  strip_tac >> Cases_on ‘n’ >>
  simp[socket_oracle_def, socket2_oracle_def] >>
  rename1 ‘ExtCall m’ >>
  ‘∀f. MEM f (call_fds (ExtCall m) conf) ⇒ ok_fd lfd s2 f’
    by (gvs[allowed_def, EVERY_MEM, ok_fd_def] >> metis_tac[]) >>
  ‘m ≠ «sock_close»’ by gvs[allowed_def] >>
  qpat_x_assum ‘allowed _ _ _ _’ kall_tac >>
  simp[socket_fn_def, socket2_fn_def] >>
  Cases_on ‘m = «sock_poll»’
  (* poll: one tick, the same ready fds *)
  >- (gvs[ffi_sock_poll_def, ffi_sock_poll2_def] >> IF_CASES_TAC >> simp[] >>
      drule tick_lsim >> strip_tac >> simp[acc_of_def] >>
      fs[lsim_def] >>
      simp[MAP_EQ_f] >> rpt strip_tac >> rename1 ‘MEM fd _’ >>
      ‘is_ready (tick s1) fd ⇔ is_ready2 (tick2 s2) fd’
        by (irule is_ready_lsim >> qexistsl [‘lfd’, ‘sk’] >> simp[] >>
            first_x_assum (qspec_then ‘fd’ mp_tac) >> simp[call_fds_def, ok_fd_def]) >>
      simp[]) >>
  Cases_on ‘m = «sock_accept»’
  >- (gvs[ffi_sock_accept_def, ffi_sock_accept2_def] >> IF_CASES_TAC >> simp[] >>
      fs[lsim_def] >> drule accept_lsim >>
      disch_then (qspec_then ‘bytes_fd conf’ strip_assume_tac) >> simp[] >>
      Cases_on ‘r’ >> gvs[acc_of_def] >>
      metis_tac[lifetime_fair_ops]) >>
  Cases_on ‘m = «sock_read»’
  >- (gvs[ffi_sock_read_def, ffi_sock_read2_def] >> IF_CASES_TAC >> simp[] >>
      ‘ok_fd lfd s2 (bytes_fd conf)’ by (first_x_assum irule >> simp[call_fds_def]) >>
      fs[lsim_def] >>
      drule_all read_lsim >>
      disch_then (qspec_then ‘LENGTH bytes − 9’ strip_assume_tac) >> simp[] >>
      Cases_on ‘r’ >> simp[acc_of_def] >> rw[] >>
      metis_tac[lifetime_fair_ops]) >>
  Cases_on ‘m = «sock_write»’
  >- (gvs[ffi_sock_write_def, ffi_sock_write2_def] >> IF_CASES_TAC >> simp[] >>
      ‘ok_fd lfd s2 (bytes_fd (TAKE 8 conf))’ by (first_x_assum irule >> simp[call_fds_def]) >>
      fs[lsim_def] >>
      drule_all write_lsim >>
      disch_then (qspec_then ‘DROP 8 conf’ strip_assume_tac) >> simp[acc_of_def] >>
      metis_tac[lifetime_fair_ops]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Along a run
   ------------------------------------------------------------------------ *)

(* Every call is allowed, given the answers of the run *)
Definition ok_calls_def:
  ok_calls lfd A [] anss = T ∧
  ok_calls lfd A ((n, c, b) :: cs) anss =
    (allowed lfd A n c ∧
     case anss of
     | INL out :: rest => ok_calls lfd (A ++ acc_of n out) cs rest
     | _ => T)
End

Theorem socket_ffi_state[simp]:
  (socket_ffi s with ffi_state := s') = socket_ffi s' ∧
  (lifetime_ffi t with ffi_state := t') = lifetime_ffi t'
Proof
  simp[socket_ffi_def, lifetime_ffi_def]
QED

(* MAIN (runs): along a run whose calls are allowed (judged by either
   world's answers), the two worlds answer the same to every prefix *)
Theorem answers_agree:
  ∀cs A s1 s2 anss.
    lsim sk lfd s1 s2 ∧ (∀f. MEM f A ⇔ MEM f (MAP FST s2.open_fds)) ∧
    ok_calls lfd A cs anss ∧
    (anss = ffi_answers (socket_ffi s1) cs ∨ anss = ffi_answers (lifetime_ffi s2) cs) ⇒
    ∀cs'. cs' ≼ cs ⇒ ffi_answers (socket_ffi s1) cs' = ffi_answers (lifetime_ffi s2) cs'
Proof
  Induct >> simp[ffi_answers_def, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  Cases >> simp[ffi_answers_def] >> PairCases_on ‘h’ >> strip_tac >> gvs[] >>
  rename1 ‘(n, c, b) :: cs’ >>
  gvs[ok_calls_def] >>
  drule_all oracle_lsim >> disch_then (qspec_then ‘b’ strip_assume_tac) >>
  gvs[socket_ffi_def, lifetime_ffi_def, ffi_answers_def] >>
  first_x_assum (qspecl_then [‘A ++ acc_of n out’, ‘s1'’, ‘s2'’] mp_tac) >>
  gvs[socket_ffi_def, lifetime_ffi_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The calls of a behaviour, and of its clocked runs
   ------------------------------------------------------------------------ *)

Theorem call_ok_allowed:
  call_ok lfd evs n c ⇔ allowed lfd (accepted_fds evs) n c
Proof
  simp[call_ok_def, allowed_def]
QED

Theorem accepted_fds_simps[simp]:
  accepted_fds [] = [] ∧
  accepted_fds (IO_event n c bl :: evs) = acc_of n (MAP SND bl) ++ accepted_fds evs ∧
  accepted_fds (l1 ++ l2) = accepted_fds l1 ++ accepted_fds l2
Proof
  simp[accepted_fds_def] >> Cases_on ‘n’ >>
  rw[event_accepted_def, acc_of_def] >> gvs[]
QED

Theorem calls_ok_CONS:
  calls_ok lfd evs ⇔
  ∀pre n c bl post. evs = pre ++ IO_event n c bl :: post ⇒ allowed lfd (accepted_fds pre) n c
Proof
  simp[calls_ok_def, call_ok_allowed]
QED

Theorem calls_ok_prefix:
  calls_ok lfd evs ∧ evs' ≼ evs ⇒ calls_ok lfd evs'
Proof
  rw[calls_ok_CONS, IS_PREFIX_APPEND] >> gvs[] >>
  first_x_assum irule >> metis_tac[APPEND_ASSOC, APPEND]
QED

(* The calls of a run, with their answers, are ok_calls *)
Theorem ok_of_calls_ok:
  ∀evs A rest.
    (∀pre n c bl post. evs = pre ++ IO_event n c bl :: post ⇒
                       allowed lfd (A ++ accepted_fds pre) n c) ∧
    (∀n c b. MEM (n, c, b) fin ⇒ allowed lfd (A ++ accepted_fds evs) n c) ∧
    LENGTH fin ≤ 1 ⇒
    ok_calls lfd A (calls_of evs ++ fin) (answers_of evs ++ rest)
Proof
  Induct
  >- (simp[calls_of_def, answers_of_def] >> Cases_on ‘fin’ >> simp[ok_calls_def] >>
      PairCases_on ‘h’ >> Cases_on ‘t’ >> gvs[ok_calls_def] >>
      rw[] >> every_case_tac >> simp[ok_calls_def]) >>
  Cases >> rpt gen_tac >> strip_tac >>
  simp[calls_of_def, answers_of_def, ok_calls_def] >>
  conj_tac
  >- (first_x_assum (qspecl_then [‘[]’, ‘f’, ‘l’, ‘l0’, ‘evs’] mp_tac) >> simp[]) >>
  simp[GSYM calls_of_def, GSYM answers_of_def] >>
  first_x_assum irule >> rw[] >>
  TRY (first_x_assum (qspecl_then [‘IO_event f l l0 :: pre’] mp_tac) >> simp[] >> NO_TAC) >>
  first_x_assum drule >> REWRITE_TAC[accepted_fds_simps, APPEND_ASSOC]
QED

(* As echoQuiet's clocked_vs_terminating (copied: this theory is a
   leaf and depends on no server's theories) *)
Theorem clocked_vs_terminating[local]:
  evaluate_prog_with_clock st env k0 prog = (ffi0, r0) ∧
  r0 ≠ Rerr (Rabort Rtimeout_error) ⇒
  ∀k. (SND (evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtimeout_error) ∧
       (FST (evaluate_prog_with_clock st env k prog)).io_events ≼ ffi0.io_events) ∨
      evaluate_prog_with_clock st env k prog = (ffi0, r0)
Proof
  rw[evaluate_prog_with_clock_def] >>
  Cases_on ‘evaluate_decs (st with clock := k0) env prog’ >> gvs[] >>
  Cases_on ‘evaluate_decs (st with clock := k) env prog’ >> gvs[] >>
  rename1 ‘evaluate_decs (st with clock := k) env prog = (s1, r1)’ >>
  rename1 ‘evaluate_decs (st with clock := k0) env prog = (s0', r0)’ >>
  Cases_on ‘k ≤ k0’
  >- (Cases_on ‘r1 = Rerr (Rabort Rtimeout_error)’
      >- (disj1_tac >> simp[] >>
          qspecl_then [‘k’, ‘k0’, ‘st’, ‘env’, ‘prog’] mp_tac evaluate_decs_ffi_mono_clock >>
          simp[io_events_mono_def])
      >> disj2_tac >>
      drule_all evaluate_decs_add_to_clock >>
      disch_then (qspec_then ‘k0 − k’ mp_tac) >> simp[])
  >> disj2_tac >>
  drule_all evaluate_decs_add_to_clock >>
  disch_then (qspec_then ‘k − k0’ mp_tac) >> simp[]
QED

Theorem final_call_len[local]:
  LENGTH (final_call r) ≤ 1
Proof
  rw[final_call_def, final_err_def] >> every_case_tac >> simp[] >>
  TRY (rename1 ‘final_ffi fe’ >> Cases_on ‘fe’ >> simp[final_ffi_def])
QED

(* MAIN (behaviours): every clocked run of a run_ok behaviour makes only
   allowed calls *)
Theorem clock_calls_ok:
  semantics_prog st env prog b ∧ run_ok lfd b ⇒
  ∀k. calls_ok lfd (FST (evaluate_prog_with_clock st env k prog)).io_events ∧
      ∀n c bb. MEM (n, c, bb) (final_call (SND (evaluate_prog_with_clock st env k prog))) ⇒
               call_ok lfd (FST (evaluate_prog_with_clock st env k prog)).io_events n c
Proof
  Cases_on ‘b’ >> simp[run_ok_def, semantics_prog_def] >> rpt strip_tac
  (* diverges: the events *)
  >- (first_x_assum irule >>
      gvs[lprefix_lubTheory.lprefix_lub_def] >> first_x_assum irule >> simp[] >>
      metis_tac[])
  (* diverges: no final call *)
  >- (qpat_x_assum ‘∀k. ∃ffi. _’ (qspec_then ‘k’ strip_assume_tac) >>
      gvs[final_call_def, final_err_def])
  (* terminates: the events *)
  >- (drule clocked_vs_terminating >> impl_tac >- (every_case_tac >> gvs[]) >>
      qmatch_goalsub_rename_tac ‘evaluate_prog_with_clock st env kk prog’ >>
      disch_then (qspec_then ‘kk’ strip_assume_tac) >> gvs[]
      >- (irule calls_ok_prefix >> metis_tac[]))
  (* terminates: the final call *)
  >> drule clocked_vs_terminating >> impl_tac >- (every_case_tac >> gvs[]) >>
  qmatch_goalsub_rename_tac ‘evaluate_prog_with_clock st env kk prog’ >>
  disch_then (qspec_then ‘kk’ strip_assume_tac) >> gvs[final_call_def] >>
  gvs[final_err_def] >> every_case_tac >> gvs[final_ffi_def] >>
  rename1 ‘final_ffi fe’ >> Cases_on ‘fe’ >> gvs[final_ffi_def]
QED

(* ------------------------------------------------------------------------
   The core world is fair
   ------------------------------------------------------------------------ *)

Theorem arrival_ok_lsim0:
  lsim0 sk lfd s1 s2 ∧ arrival_ok2 s2 a ⇒
  arrival_ok s1 (core_arrival sk (LENGTH s2.clients) a)
Proof
  Cases_on ‘a’ >> simp[arrival_ok2_def, core_arrival_def] >> strip_tac
  >- (‘room sk (SUC (LENGTH s2.clients))’ by gvs[lsim0_def, room_def] >>
      ‘alloc_ok sk.alloc ∧ MEM lfd (MAP FST sk.listening)’ by gvs[lsim0_def] >>
      ‘core_fd sk (LENGTH s2.clients) ≠ lfd’
        by (qspecl_then [‘sk’, ‘SUC (LENGTH s2.clients)’, ‘LENGTH s2.clients’, ‘lfd’] mp_tac
              (Q.GENL [‘sk’, ‘n’, ‘j’, ‘l’] core_fd_not_listener) >>
            asm_rewrite_tac[] >> simp[]) >>
      ‘∀j. j < LENGTH s2.clients ⇒ core_fd sk (LENGTH s2.clients) ≠ core_fd sk j’
        by (rpt strip_tac >>
            qspecl_then [‘sk’, ‘SUC (LENGTH s2.clients)’, ‘LENGTH s2.clients’, ‘j’] mp_tac
              (Q.GENL [‘sk’, ‘n’, ‘i’, ‘j’] core_fd_11) >>
            asm_rewrite_tac[] >> simp[]) >>
      ‘ALOOKUP (conns_of sk s2.clients) (core_fd sk (LENGTH s2.clients)) = NONE’
        by (irule ALOOKUP_conns_of_NONE >> metis_tac[]) >>
      gvs[lsim0_def, arrival_ok_def, is_listener_def, is_conn_def])
  >> gvs[lsim0_def, arrival_ok_def] >>
  drule_all ALOOKUP_conns_of >> simp[]
QED

Theorem step_ok_lsim0:
  ∀st s1 s2. lsim0 sk lfd s1 s2 ∧ step_ok2 s2 st ⇒
             step_ok s1 (core_step sk (LENGTH s2.clients) st)
Proof
  Induct >> simp[core_step_def, step_ok_def, step_ok2_def] >> rpt gen_tac >> strip_tac >>
  drule_all arrival_ok_lsim0 >> strip_tac >> simp[] >>
  drule_all deliver_lsim0 >> strip_tac >>
  first_x_assum drule_all >> simp[] >>
  Cases_on ‘is_connect2 h’ >> gvs[ADD1]
QED

Theorem ticks_lsim:
  ∀n s1 s2. lsim sk lfd s1 s2 ⇒ step_ok (ticks n s1) (next_step (ticks n s1))
Proof
  Induct >> simp[ticks_def]
  >- (rw[lsim_def, next_step_def, core_sched_LHD] >>
      Cases_on ‘LHD s2.future’ >> simp[step_ok_def] >>
      drule lifetime_fair_tick >> simp[next_step2_def] >> strip_tac >>
      drule_all step_ok_lsim0 >> simp[])
  >> rpt strip_tac >> first_x_assum irule >> qexists_tac ‘tick2 s2’ >>
  irule tick_lsim >> simp[]
QED

(* ------------------------------------------------------------------------
   THE LINK
   ------------------------------------------------------------------------ *)

Theorem lsim_init:
  lifetime_world lfd sk ⇒ lsim sk lfd (core_of sk) sk
Proof
  rw[lifetime_world_def, lsim_def, lsim0_def, core_of_def, room_def] >>
  simp[open_of_def]
QED

Theorem init_state_ffi_field[local,simp]:
  (init_state f).ffi = f
Proof
  simp[ml_progTheory.init_state_def]
QED

Theorem init_state_ffi[local]:
  (init_state f1 with ffi := f2) = init_state f2
Proof
  simp[ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality]
QED

(* The clocked runs of a run_ok behaviour make ok_calls, with their own
   answers (any FFI) *)
Theorem clock_ok_calls:
  f.io_events = [] ∧ semantics_prog (init_state f) env prog b ∧ run_ok lfd b ⇒
  ∀k. ok_calls lfd [] (clock_calls (init_state f) env prog k)
                     (ffi_answers f (clock_calls (init_state f) env prog k))
Proof
  rpt strip_tac >>
  drule_all clock_calls_ok >> disch_then (qspec_then ‘k’ mp_tac) >>
  Cases_on ‘evaluate_prog_with_clock (init_state f) env k prog’ >>
  rename1 ‘_ = (ffik, rk)’ >> simp[ext_def] >> strip_tac >>
  ‘RTC call_FFI_rel f ffik’
    by (gvs[evaluate_prog_with_clock_def] >> pairarg_tac >> gvs[] >>
        qspecl_then [‘init_state f with clock := k’, ‘env’, ‘prog’] mp_tac
          (CONJUNCT2 (CONJUNCT2 evaluate_call_FFI_rel)) >>
        simp[ml_progTheory.init_state_def]) >>
  drule call_FFI_rel_answers >> strip_tac >> gvs[] >>
  simp[] >> irule ok_of_calls_ok >>
  simp[final_call_len] >> rpt strip_tac >>
  TRY (first_x_assum drule >> simp[call_ok_allowed] >> NO_TAC) >>
  gvs[calls_ok_CONS] >> first_x_assum irule >> metis_tac[]
QED

(* MAIN: conservativity *)
Theorem lifetime_core_link_thm:
  lifetime_core_link
Proof
  rw[lifetime_core_link_def]
  (* the core world of sk is a fair server world *)
  >- (drule lsim_init >> strip_tac >>
      gvs[lifetime_world_def, server_world_def, core_of_def, sched_wf_def] >>
      rpt strip_tac >> drule ticks_lsim >> simp[])
  (* the same behaviour, in both directions *)
  >> drule lsim_init >> strip_tac >>
  ‘(socket_ffi (core_of sk)).io_events = [] ∧ (lifetime_ffi sk).io_events = [] ∧
   sk.open_fds = []’
    by gvs[socket_ffi_def, lifetime_ffi_def, lifetime_world_def] >>
  eq_tac >> strip_tac
  >- (‘init_state (lifetime_ffi sk) = init_state (socket_ffi (core_of sk)) with ffi := lifetime_ffi sk’
        by simp[init_state_ffi] >>
      pop_assum SUBST1_TAC >> irule semantics_prog_upto >>
      simp[] >>
      gen_tac >> simp[agree_upto_def] >> rpt strip_tac >>
      drule_all clock_ok_calls >> disch_then (qspec_then ‘k’ assume_tac) >>
      qspecl_then [‘clock_calls (init_state (socket_ffi (core_of sk))) init_env prog k’,
                   ‘[]’, ‘core_of sk’, ‘sk’,
                   ‘ffi_answers (socket_ffi (core_of sk))
                      (clock_calls (init_state (socket_ffi (core_of sk))) init_env prog k)’]
        mp_tac answers_agree >>
      simp[] >> disch_then (qspec_then ‘cs’ mp_tac) >> simp[]) >>
  ‘init_state (socket_ffi (core_of sk)) = init_state (lifetime_ffi sk) with ffi := socket_ffi (core_of sk)’
    by simp[init_state_ffi] >>
  pop_assum SUBST1_TAC >> irule semantics_prog_upto >>
  simp[] >>
  gen_tac >> simp[agree_upto_def] >> rpt strip_tac >>
  drule_all clock_ok_calls >> disch_then (qspec_then ‘k’ assume_tac) >>
  qspecl_then [‘clock_calls (init_state (lifetime_ffi sk)) init_env prog k’,
               ‘[]’, ‘core_of sk’, ‘sk’,
               ‘ffi_answers (lifetime_ffi sk)
                  (clock_calls (init_state (lifetime_ffi sk)) init_env prog k)’]
    mp_tac answers_agree >>
  simp[] >> disch_then (qspec_then ‘cs’ mp_tac) >> simp[]
QED
