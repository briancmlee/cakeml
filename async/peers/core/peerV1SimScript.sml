(*
  Version 1 as version 2, for fd-disciplined programs (design/35 §4,
  option A; toward v1_instance_disc).

  From a version-1 server world sk, the version-2 world v2of1 lfd sk:
   - the schedule, renamed (rn1_sched): Connect l c becomes Connect2 l and c
     is the next client; Data c bs and Eof c go to c's client number (its
     position in connect order);
   - the allocation gives client j the fd of the j-th connect (conn_fd), or
     the lowest free fd if that one is in use (so alloc_ok holds).
  A program that only touches the listener and connections it has accepted
  cannot tell the two worlds apart.
*)
Theory peerV1Sim
Ancestors
  llist alist words rich_list indexedLists socketWorld socketFair
  lifetimeWorld lifetimeFair EchoSpec EchoEpisodesSpec EchoEpisodesSpecBite
Libs
  preamble

(* ------------------------------------------------------------------------
   The renamed schedule
   ------------------------------------------------------------------------ *)

(* cs: the connections so far, in connect order *)
Definition rn1_arr_def:
  rn1_arr (cs : word64 list) (Connect l c) = (cs ++ [c], Connect2 l) ∧
  rn1_arr cs (Data c bs) = (cs, Data2 (findi c cs) bs) ∧
  rn1_arr cs (Eof c) = (cs, Eof2 (findi c cs))
End

Definition rn1_step_def:
  rn1_step cs [] = (cs, []) ∧
  rn1_step cs (a :: as) =
    let (cs1, b) = rn1_arr cs a;
        (cs2, bs) = rn1_step cs1 as
    in (cs2, b :: bs)
End

Definition rn1_sched_def:
  rn1_sched cs ll =
    LUNFOLD (λ(cs, ll). case LHD ll of
                        | NONE => NONE
                        | SOME st => SOME ((FST (rn1_step cs st), THE (LTL ll)),
                                           SND (rn1_step cs st))) (cs, ll)
End

Theorem rn1_sched_LHD:
  LHD (rn1_sched cs ll) = OPTION_MAP (λst. SND (rn1_step cs st)) (LHD ll)
Proof
  simp[rn1_sched_def, Once LUNFOLD] >> CASE_TAC >> simp[]
QED

Theorem rn1_sched_LTL:
  LHD ll = SOME st ⇒
  LTL (rn1_sched cs ll) = SOME (rn1_sched (FST (rn1_step cs st)) (THE (LTL ll)))
Proof
  simp[rn1_sched_def, Once LUNFOLD]
QED

(* The connections of a step's arrivals, in order *)
Definition step_conns_def:
  step_conns st = FLAT (MAP (λa. case a of Connect l c => [c] | _ => []) st)
End

Theorem rn1_step_conns:
  ∀st cs. FST (rn1_step cs st) = cs ++ step_conns st
Proof
  Induct >> simp[rn1_step_def, step_conns_def] >> Cases >>
  simp[rn1_arr_def] >> rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  fs[step_conns_def] >> metis_tac[FST, APPEND_ASSOC]
QED

Theorem step_conns_cons:
  step_conns (Connect l c :: as) = c :: step_conns as ∧
  step_conns (Data c bs :: as) = step_conns as ∧
  step_conns (Eof c :: as) = step_conns as
Proof
  simp[step_conns_def]
QED

Theorem rn1_step_cons:
  rn1_step cs (a :: as) =
    (FST (rn1_step (FST (rn1_arr cs a)) as),
     SND (rn1_arr cs a) :: SND (rn1_step (FST (rn1_arr cs a)) as))
Proof
  simp[rn1_step_def] >> rpt (pairarg_tac >> gvs[])
QED

(* The connections of the first n steps of a schedule *)
Definition sched_conns_def:
  sched_conns 0 ll = [] ∧
  sched_conns (SUC n) ll =
    case LHD ll of
    | NONE => []
    | SOME st => step_conns st ++ sched_conns n (THE (LTL ll))
End

(* The fd of the j-th connect of the schedule (0w if there is none) *)
Definition conn_fd_def:
  conn_fd ll j =
    if ∃n. j < LENGTH (sched_conns n ll)
    then EL j (sched_conns (LEAST n. j < LENGTH (sched_conns n ll)) ll)
    else 0w
End

(* The allocation: client j gets the fd of the j-th connect, unless it is
   in use *)
Definition alloc1_def:
  alloc1 ll j used = let c = conn_fd ll j in if MEM c used then lowest_free used else c
End

Theorem alloc1_ok:
  alloc_ok (alloc1 ll)
Proof
  rw[alloc_ok_def, alloc1_def] >>
  mp_tac lowest_free_alloc_ok >> rw[alloc_ok_def]
QED

(* The version-2 world of a version-1 world *)
Definition v2of1_def:
  v2of1 lfd (sk : sockets) =
    <| listening := [(lfd, [])]; clients := []; open_fds := []; reserved := [];
       alloc := alloc1 sk.sched; future := rn1_sched [] sk.sched |>
End

(* ------------------------------------------------------------------------
   The relation
   ------------------------------------------------------------------------ *)

(* cs: the connections so far, in connect order (client j is EL j cs); the
   first k are accepted, on their own fds; the rest are pending, in order *)
Definition v12core_def:
  v12core lfd cs k (s1 : sockets) (s2 : sockets2) ⇔
    ALL_DISTINCT cs ∧ ¬MEM lfd cs ∧ k ≤ LENGTH cs ∧
    MAP FST s1.conns = REVERSE cs ∧
    s1.listeners = [(lfd, DROP k cs)] ∧
    s2.listening = [(lfd, GENLIST (λi. k + i) (LENGTH cs − k))] ∧
    LENGTH s2.clients = LENGTH cs ∧
    (∀j. j < LENGTH cs ⇒
         ∃cn. ALOOKUP s1.conns (EL j cs) = SOME cn ∧
              cn.incoming = (EL j s2.clients).incoming ∧
              cn.peer_closed = (EL j s2.clients).peer_closed) ∧
    s2.open_fds = REVERSE (GENLIST (λj. (EL j cs, j)) k)
End

Theorem ALOOKUP_conns_MEM[local]:
  MAP FST l = REVERSE cs ⇒ (ALOOKUP l c ≠ NONE ⇔ MEM c cs)
Proof
  rw[ALOOKUP_NONE] >> metis_tac[MEM_REVERSE]
QED

Theorem findi_EL[local]:
  ALL_DISTINCT cs ∧ j < LENGTH cs ⇒ findi (EL j cs) cs = j
Proof
  metis_tac[findi_EL]
QED

(* MAIN (arrivals): an effective version-1 arrival and its renaming keep
   the relation *)
Theorem v12core_deliver:
  v12core lfd cs k s1 s2 ∧ arrival_ok s1 a ⇒
  v12core lfd (FST (rn1_arr cs a)) k (deliver1 s1 a)
              (deliver2 s2 (SND (rn1_arr cs a)))
Proof
  Cases_on ‘a’ >> simp[rn1_arr_def, arrival_ok_def] >> strip_tac
  >- ((* a connection *)
      rename [‘Connect l c’] >>
      ‘l = lfd’ by (gvs[v12core_def, is_listener_def] >> Cases_on ‘lfd = l’ >> gvs[]) >>
      ‘¬MEM c cs ∧ c ≠ lfd’
        by (fs[v12core_def, is_listener_def, is_conn_def] >>
            metis_tac[ALOOKUP_conns_MEM]) >>
      fs[v12core_def, deliver1_def, deliver2_def, is_listener_def, is_conn_def,
         AFUPDKEY_def, ALL_DISTINCT_APPEND, DROP_APPEND1] >>
      rpt conj_tac >>
      TRY (rw[LIST_EQ_REWRITE, EL_GENLIST] >> ‘x < LENGTH cs’ by decide_tac >>
           simp[EL_APPEND1] >> NO_TAC) >>
      TRY (rpt strip_tac >> Cases_on ‘j = LENGTH cs’
           >- (‘LENGTH s2.clients = j’ by decide_tac >>
               ‘(cs ++ [c])❲j❳ = c’ by gvs[EL_APPEND2] >>
               ‘(s2.clients ++ [empty_conn])❲j❳ = empty_conn’ by gvs[EL_APPEND2] >>
               simp[]) >>
           ‘j < LENGTH cs’ by decide_tac >>
           qpat_x_assum ‘∀j. j < LENGTH cs ⇒ _’ drule >> strip_tac >>
           ‘j < LENGTH s2.clients’ by decide_tac >>
           simp[EL_APPEND1] >> ‘EL j cs ≠ c’ by metis_tac[MEM_EL] >> simp[] >> NO_TAC) >>
      ‘LENGTH cs + 1 − k = SUC (LENGTH cs − k)’ by decide_tac >>
      pop_assum SUBST1_TAC >> simp[GENLIST, SNOC_APPEND] >> decide_tac)
  (* data or EOF on a connection *)
  >> rename1 ‘ALOOKUP s1.conns c = SOME cn’ >>
  ‘MEM c cs’ by (fs[v12core_def] >> metis_tac[ALOOKUP_conns_MEM, NOT_NONE_SOME]) >>
  ‘∃j. j < LENGTH cs ∧ c = EL j cs’ by metis_tac[MEM_EL] >>
  ‘findi c cs = j’ by (fs[v12core_def] >> simp[findi_EL]) >>
  fs[v12core_def, deliver1_def, deliver2_def] >>
  first_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  simp[update_client_def, MAP_FST_AFUPDKEY, AFUPDKEY_ALOOKUP] >>
  rw[] >> first_x_assum drule >> strip_tac >> simp[EL_LUPDATE] >>
  rw[] >> gvs[] >> metis_tac[ALL_DISTINCT_EL_IMP]
QED

Theorem v12core_sched[simp]:
  v12core lfd cs k (s1 with sched := x) (s2 with <| future := y |>) ⇔ v12core lfd cs k s1 s2
Proof
  simp[v12core_def]
QED

Theorem deliver1_sched[local]:
  (deliver1 s a).sched = s.sched
Proof
  Cases_on ‘a’ >> rw[deliver1_def]
QED

Theorem FOLDL_deliver1_sched:
  ∀st s. (FOLDL deliver1 s st).sched = s.sched
Proof
  Induct >> simp[deliver1_sched]
QED

Theorem FOLDL_deliver2_fields[local]:
  ∀st s. (FOLDL deliver2 s st).future = s.future ∧ (FOLDL deliver2 s st).alloc = s.alloc ∧
         (FOLDL deliver2 s st).reserved = s.reserved
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >>
  rw[deliver2_def, update_client_def]
QED

Theorem step_ok_with_sched:
  ∀st s. step_ok (s with sched := x) st ⇔ step_ok s st
Proof
  ‘∀a s. deliver1 (s with sched := x) a = (deliver1 s a) with sched := x’
    by (Cases >> rw[deliver1_def, is_listener_def, is_conn_def]) >>
  Induct >> simp[step_ok_def] >> Cases >>
  simp[arrival_ok_def, is_listener_def, is_conn_def]
QED

(* A whole step of effective arrivals keeps the relation *)
Theorem v12core_step:
  ∀st cs s1 s2.
    v12core lfd cs k s1 s2 ∧ step_ok s1 st ⇒
    v12core lfd (FST (rn1_step cs st)) k (FOLDL deliver1 s1 st)
                (FOLDL deliver2 s2 (SND (rn1_step cs st)))
Proof
  Induct >> simp[rn1_step_def, step_ok_def] >> rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all v12core_deliver >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

(* The fds in use when client j is accepted, in a disciplined run without
   close: the process's other fds, the listener, and the earlier clients'
   fds, newest first *)
Definition exp_used_def:
  exp_used res lfd cs j = res ++ [lfd] ++ REVERSE (TAKE j cs)
End

(* The relation, with the schedules: version 2's future is version 1's
   schedule renamed, and the allocation gives each client the fd of its
   connect (whatever the allocation policy and the other fds) *)
Definition v12rel_def:
  v12rel lfd ll0 (s1 : sockets) (s2 : sockets2) ⇔
    ∃cs k. v12core lfd cs k s1 s2 ∧ s2.future = rn1_sched cs s1.sched ∧
           (∀m j. j < LENGTH (cs ++ sched_conns m s1.sched) ⇒
                  conn_fd ll0 j = EL j (cs ++ sched_conns m s1.sched)) ∧
           (∀m j. j < LENGTH (cs ++ sched_conns m s1.sched) ⇒
                  s2.alloc j (exp_used s2.reserved lfd (cs ++ sched_conns m s1.sched) j) =
                  EL j (cs ++ sched_conns m s1.sched)) ∧
           (* non-saturation: fewer than 2^64 - 3 fds in use, ever *)
           ∀m. LENGTH s2.reserved + LENGTH (cs ++ sched_conns m s1.sched) + 3 < dimword (:64)
End

(* MAIN: a tick of effective arrivals keeps the relation *)
Theorem v12rel_tick:
  v12rel lfd ll0 s1 s2 ∧ step_ok s1 (next_step s1) ⇒ v12rel lfd ll0 (tick s1) (tick2 s2)
Proof
  rw[v12rel_def] >>
  Cases_on ‘LHD s1.sched’
  >- (‘LHD s2.future = NONE’ by (asm_rewrite_tac[rn1_sched_LHD] >> simp[]) >>
      simp[tick_def, tick2_def] >> metis_tac[]) >>
  rename1 ‘LHD s1.sched = SOME st’ >>
  ‘LHD s2.future = SOME (SND (rn1_step cs st))’ by (asm_rewrite_tac[rn1_sched_LHD] >> simp[]) >>
  ‘THE (LTL s2.future) = rn1_sched (FST (rn1_step cs st)) (THE (LTL s1.sched))’
    by (drule rn1_sched_LTL >> simp[]) >>
  simp[tick_def, tick2_def, deliver_def, FOLDL_deliver1_sched, FOLDL_deliver2_fields] >>
  qexistsl_tac [‘FST (rn1_step cs st)’, ‘k’] >>
  ‘step_ok (s1 with sched := THE (LTL s1.sched)) st’
    by fs[next_step_def, step_ok_with_sched] >>
  conj_tac
  >- (irule v12core_step >> simp[]) >>
  rw[rn1_step_conns] >>
  TRY (qpat_x_assum ‘∀m j. _ ⇒ conn_fd _ _ = _’ (qspecl_then [‘SUC m’, ‘j’] mp_tac) >>
       simp[sched_conns_def] >> NO_TAC) >>
  TRY (qpat_x_assum ‘∀m j. _ ⇒ s2.alloc _ _ = _’ (qspecl_then [‘SUC m’, ‘j’] mp_tac) >>
       simp[sched_conns_def] >> NO_TAC) >>
  qpat_x_assum ‘∀m. LENGTH cs + _ < _’ (qspec_then ‘SUC m’ mp_tac) >> simp[sched_conns_def]
QED

(* ------------------------------------------------------------------------
   The calls, on the listener and on accepted connections
   ------------------------------------------------------------------------ *)

(* The fds a disciplined program may name: the listener and the accepted
   connections *)
Definition v12ok_def:
  v12ok lfd (s2 : sockets2) f ⇔ f = lfd ∨ MEM f (MAP FST s2.open_fds)
End

Theorem v12core_open:
  v12core lfd cs k s1 s2 ⇒
  (MEM f (MAP FST s2.open_fds) ⇔ ∃j. j < k ∧ f = EL j cs) ∧
  (∀j. j < k ⇒ client_of s2 (EL j cs) = SOME j)
Proof
  strip_tac >> fs[v12core_def] >>
  ‘GENLIST (λj. EL j cs) k = TAKE k cs’ by simp[LIST_EQ_REWRITE, EL_TAKE] >>
  ‘ALL_DISTINCT (MAP FST s2.open_fds)’
    by simp[MAP_REVERSE, MAP_GENLIST, combinTheory.o_DEF, ALL_DISTINCT_TAKE] >>
  conj_tac >- (simp[MEM_MAP, MEM_GENLIST, PULL_EXISTS] >> metis_tac[]) >>
  rw[client_of_def] >>
  ‘ALOOKUP s2.open_fds (EL j cs) = SOME j’
    by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[MEM_GENLIST] >> metis_tac[]) >>
  qpat_x_assum ‘s2.open_fds = _’ (fn th => fs[GSYM th])
QED

(* MAIN: readiness agrees on the listener and accepted connections *)
Theorem v12core_ready:
  v12core lfd cs k s1 s2 ∧ v12ok lfd s2 f ⇒ (is_ready s1 f ⇔ is_ready2 s2 f)
Proof
  strip_tac >> drule v12core_open >> strip_tac >>
  qpat_x_assum ‘v12core _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [v12core_def]) >>
  qpat_x_assum ‘v12ok _ _ _’ (strip_assume_tac o REWRITE_RULE [v12ok_def])
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      ‘ALOOKUP s1.conns lfd = NONE’ by metis_tac[ALOOKUP_conns_MEM] >>
      ‘¬MEM lfd (MAP FST s2.open_fds)’
        by (strip_tac >> ‘∃j. j < k ∧ lfd = EL j cs’ by metis_tac[] >>
            ‘j < LENGTH cs’ by decide_tac >> metis_tac[MEM_EL]) >>
      ‘client_of s2 lfd = NONE’
        by (‘ALOOKUP s2.open_fds lfd = NONE’ by simp[ALOOKUP_NONE] >>
            simp[client_of_def] >> qpat_x_assum ‘s2.open_fds = _’ (fn th => fs[GSYM th])) >>
      asm_rewrite_tac[is_ready_def, is_ready2_def] >> simp[] >>
      simp[DROP_EQ_NIL, GENLIST_EQ_NIL] >> decide_tac) >>
  ‘∃j. j < k ∧ f = EL j cs’ by metis_tac[] >>
  qpat_x_assum ‘f = _’ SUBST_ALL_TAC >>
  ‘j < LENGTH cs’ by decide_tac >>
  ‘EL j cs ≠ lfd’ by metis_tac[MEM_EL] >>
  ‘client_of s2 (EL j cs) = SOME j’ by metis_tac[] >>
  qpat_x_assum ‘∀j. j < LENGTH cs ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  asm_rewrite_tac[is_ready_def, is_ready2_def] >> simp[]
QED

Theorem sched_conns_0[simp]:
  sched_conns 0 ll = []
Proof
  simp[sched_conns_def]
QED

(* MAIN: accept agrees (on any fd) *)
Theorem v12rel_accept:
  v12rel lfd ll0 s1 s2 ⇒
  (sock_accept l s1 = NONE ⇔ sock_accept2 l s2 = NONE) ∧
  ∀r s1'. sock_accept l s1 = SOME (r, s1') ⇒
          ∃s2'. sock_accept2 l s2 = SOME (r, s2') ∧ v12rel lfd ll0 s1' s2'
Proof
  strip_tac >> fs[v12rel_def] >>
  ‘s1.listeners = [(lfd, DROP k cs)] ∧
   s2.listening = [(lfd, GENLIST (λi. k + i) (LENGTH cs − k))] ∧
   k ≤ LENGTH cs ∧ ALL_DISTINCT cs ∧ ¬MEM lfd cs ∧
   s2.open_fds = REVERSE (GENLIST (λj. (EL j cs, j)) k)’
    by fs[v12core_def] >>
  reverse (Cases_on ‘l = lfd’)
  >- simp[sock_accept_def, sock_accept2_def] >>
  qpat_x_assum ‘l = lfd’ SUBST_ALL_TAC >>
  Cases_on ‘k = LENGTH cs’
  >- (simp[sock_accept_def, sock_accept2_def, DROP_LENGTH_NIL] >>
      rw[] >> metis_tac[]) >>
  ‘k < LENGTH cs’ by decide_tac >>
  ‘DROP k cs = EL k cs :: DROP (k + 1) cs’
    by (irule DROP_EL_CONS >> first_assum ACCEPT_TAC) >>
  ‘GENLIST (λi. k + i) (LENGTH cs − k) =
   k :: GENLIST (λi. (k + 1) + i) (LENGTH cs − (k + 1))’
    by (‘LENGTH cs − k = SUC (LENGTH cs − (k + 1))’ by decide_tac >>
        pop_assum (fn th => REWRITE_TAC[th, GENLIST_CONS]) >>
        simp[combinTheory.o_DEF] >> simp[GENLIST_FUN_EQ]) >>
  ‘used_fds s2 = exp_used s2.reserved lfd cs k’
    by (simp[used_fds_def, exp_used_def, MAP_REVERSE, MAP_GENLIST, combinTheory.o_DEF] >>
        simp[LIST_EQ_REWRITE, EL_TAKE]) >>
  ‘LENGTH (used_fds s2) = LENGTH s2.reserved + k + 1’
    by simp[exp_used_def, LENGTH_TAKE] >>
  ‘LENGTH s2.reserved + LENGTH cs + 3 < dimword (:64)’
    by (qpat_x_assum ‘∀m. LENGTH cs + _ < _’ (qspec_then ‘0’ mp_tac) >> simp[]) >>
  ‘s2.alloc k (used_fds s2) = EL k cs’
    by (qpat_x_assum ‘∀m j. _ ⇒ s2.alloc _ _ = _’ (qspecl_then [‘0’, ‘k’] mp_tac) >>
        simp[]) >>
  ‘s2.alloc k (exp_used s2.reserved lfd cs k) = EL k cs’ by metis_tac[] >>
  simp[sock_accept_def, sock_accept2_def, AFUPDKEY_def] >>
  rw[] >>
  TRY (fs[] >> NO_TAC) >>
  qexistsl_tac [‘cs’, ‘k + 1’] >> fs[v12core_def] >>
  simp[GSYM ADD1, GENLIST, REVERSE_SNOC]
QED

(* The connection of an fd a disciplined program may name *)
Theorem v12_conn_of[local]:
  v12core lfd cs k s1 s2 ∧ v12ok lfd s2 f ⇒
  (f = lfd ∧ ALOOKUP s1.conns f = NONE ∧ client_of s2 f = NONE) ∨
  (∃j cn. j < k ∧ f = EL j cs ∧ client_of s2 f = SOME j ∧
          ALOOKUP s1.conns f = SOME cn ∧ cn.incoming = (EL j s2.clients).incoming ∧
          cn.peer_closed = (EL j s2.clients).peer_closed)
Proof
  strip_tac >> drule v12core_open >> strip_tac >>
  qpat_x_assum ‘v12core _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [v12core_def]) >>
  qpat_x_assum ‘v12ok _ _ _’ (strip_assume_tac o REWRITE_RULE [v12ok_def])
  >- (disj1_tac >> qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >> simp[] >>
      conj_tac >- metis_tac[ALOOKUP_conns_MEM] >>
      ‘¬MEM lfd (MAP FST s2.open_fds)’
        by (strip_tac >> ‘∃j. j < k ∧ lfd = EL j cs’ by metis_tac[] >>
            ‘j < LENGTH cs’ by decide_tac >> metis_tac[MEM_EL]) >>
      ‘ALOOKUP s2.open_fds lfd = NONE’ by simp[ALOOKUP_NONE] >>
      simp[client_of_def] >> qpat_x_assum ‘s2.open_fds = _’ (fn th => fs[GSYM th])) >>
  disj2_tac >>
  ‘∃j. j < k ∧ f = EL j cs’ by metis_tac[] >>
  qexists_tac ‘j’ >> simp[] >>
  ‘j < LENGTH cs’ by decide_tac >>
  qpat_x_assum ‘∀j. j < LENGTH cs ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >> metis_tac[]
QED

(* MAIN: read agrees on the listener and accepted connections *)
Theorem v12rel_read:
  v12rel lfd ll0 s1 s2 ∧ v12ok lfd s2 f ⇒
  (sock_read f n s1 = NONE ⇔ sock_read2 f n s2 = NONE) ∧
  ∀r s1'. sock_read f n s1 = SOME (r, s1') ⇒
          ∃s2'. sock_read2 f n s2 = SOME (r, s2') ∧ v12rel lfd ll0 s1' s2'
Proof
  strip_tac >> fs[v12rel_def] >>
  drule_all v12_conn_of >> strip_tac
  >- simp[sock_read_def, sock_read2_def] >>
  simp[sock_read_def, sock_read2_def] >>
  rw[] >> qexistsl_tac [‘cs’, ‘k’] >> simp[] >>
  fs[v12core_def, update_client_def, MAP_FST_AFUPDKEY] >>
  rw[] >> rename1 ‘j' < LENGTH cs’ >>
  qpat_x_assum ‘∀j. j < LENGTH cs ⇒ ∃cn. _’ (qspec_then ‘j'’ mp_tac) >> simp[] >> strip_tac >>
  simp[AFUPDKEY_ALOOKUP, EL_LUPDATE] >>
  Cases_on ‘j' = j’ >> gvs[] >>
  ‘EL j' cs ≠ EL j cs’ by metis_tac[ALL_DISTINCT_EL_IMP, LESS_LESS_EQ_TRANS] >> simp[]
QED

(* MAIN: write agrees on the listener and accepted connections *)
Theorem v12rel_write:
  v12rel lfd ll0 s1 s2 ∧ v12ok lfd s2 f ⇒
  (sock_write f bs s1 = NONE ⇔ sock_write2 f bs s2 = NONE) ∧
  ∀s1'. sock_write f bs s1 = SOME s1' ⇒
        ∃s2'. sock_write2 f bs s2 = SOME s2' ∧ v12rel lfd ll0 s1' s2'
Proof
  strip_tac >> fs[v12rel_def] >>
  drule_all v12_conn_of >> strip_tac
  >- simp[sock_write_def, sock_write2_def] >>
  simp[sock_write_def, sock_write2_def] >>
  rw[] >> qexistsl_tac [‘cs’, ‘k’] >> simp[] >>
  fs[v12core_def, update_client_def, MAP_FST_AFUPDKEY] >>
  rw[] >> rename1 ‘j' < LENGTH cs’ >>
  qpat_x_assum ‘∀j. j < LENGTH cs ⇒ ∃cn. _’ (qspec_then ‘j'’ mp_tac) >> simp[] >> strip_tac >>
  simp[AFUPDKEY_ALOOKUP, EL_LUPDATE] >>
  Cases_on ‘j' = j’ >> gvs[] >>
  ‘EL j' cs ≠ EL j cs’ by metis_tac[ALL_DISTINCT_EL_IMP, LESS_LESS_EQ_TRANS] >> simp[]
QED

(* ------------------------------------------------------------------------
   One FFI call
   ------------------------------------------------------------------------ *)

(* The fds a call names (peerInstances' event_fds, for calls) *)
Definition call_fds_def:
  call_fds n conf =
    if n = «sock_poll» then bytes_fds conf
    else if n = «sock_write» then [bytes_fd (TAKE 8 conf)]
    else [bytes_fd conf]
End

Theorem tick2_open_fds[local]:
  (tick2 s).open_fds = s.open_fds
Proof
  ‘∀as s. (FOLDL deliver2 s as).open_fds = s.open_fds’
    by (Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def]) >>
  rw[tick2_def] >> CASE_TAC >> simp[]
QED

(* MAIN: a version-1 call on disciplined fds is answered alike by both
   worlds, which stay related *)
Theorem v12_call:
  v12rel lfd ll0 s1 s2 ∧ socket_fn n ≠ NONE ∧
  EVERY (v12ok lfd s2) (call_fds n conf) ∧
  (n = «sock_poll» ⇒ step_ok s1 (next_step s1)) ⇒
  (socket_oracle (ExtCall n) s1 conf bytes = Oracle_final FFI_failed ∧
   socket2_oracle (ExtCall n) s2 conf bytes = Oracle_final FFI_failed) ∨
  ∃out s1' s2'. socket_oracle (ExtCall n) s1 conf bytes = Oracle_return s1' out ∧
                socket2_oracle (ExtCall n) s2 conf bytes = Oracle_return s2' out ∧
                v12rel lfd ll0 s1' s2'
Proof
  strip_tac >>
  ‘n = «sock_poll» ∨ n = «sock_accept» ∨ n = «sock_read» ∨ n = «sock_write»’
    by (fs[socket_fn_def] >> rw[] >> fs[]) >>
  gvs[socket_oracle_def, socket2_oracle_def, socket_fn_def, socket2_fn_def, call_fds_def]
  >- ((* poll *)
      simp[ffi_sock_poll_def, ffi_sock_poll2_def] >> IF_CASES_TAC >> simp[] >>
      ‘v12rel lfd ll0 (tick s1) (tick2 s2)’ by metis_tac[v12rel_tick] >>
      ‘∃cs k. v12core lfd cs k (tick s1) (tick2 s2)’ by metis_tac[v12rel_def] >>
      ‘∀fd. v12ok lfd s2 fd ⇒ v12ok lfd (tick2 s2) fd’ by simp[v12ok_def, tick2_open_fds] >>
      simp[MAP_EQ_f] >> rw[] >> fs[EVERY_MEM] >> metis_tac[v12core_ready])
  >- ((* accept *)
      simp[ffi_sock_accept_def, ffi_sock_accept2_def] >> IF_CASES_TAC >> simp[] >>
      drule v12rel_accept >> disch_then (qspec_then ‘bytes_fd conf’ strip_assume_tac) >>
      Cases_on ‘sock_accept (bytes_fd conf) s1’ >> gvs[] >>
      rename1 ‘SOME p’ >> PairCases_on ‘p’ >> fs[] >>
      Cases_on ‘p0’ >> simp[])
  >- ((* read *)
      simp[ffi_sock_read_def, ffi_sock_read2_def] >> IF_CASES_TAC >> simp[] >>
      drule_all v12rel_read >> disch_then (qspec_then ‘LENGTH bytes − 9’ strip_assume_tac) >>
      Cases_on ‘sock_read (bytes_fd conf) (LENGTH bytes − 9) s1’ >> gvs[] >>
      rename1 ‘SOME p’ >> PairCases_on ‘p’ >> fs[] >>
      Cases_on ‘p0’ >> simp[] >> rw[])
  >> (* write *)
  simp[ffi_sock_write_def, ffi_sock_write2_def] >> IF_CASES_TAC >> simp[] >>
  drule_all v12rel_write >> disch_then (qspec_then ‘DROP 8 conf’ strip_assume_tac) >>
  Cases_on ‘sock_write (bytes_fd (TAKE 8 conf)) (DROP 8 conf) s1’ >> gvs[]
QED

(* Every call keeps sched_wf *)
Theorem socket_oracle_sched_wf:
  sched_wf s ∧ socket_oracle (ExtCall n) s conf bytes = Oracle_return s' out ⇒
  sched_wf s'
Proof
  strip_tac >> drule sched_wf_preserved >> strip_tac >>
  qpat_x_assum ‘socket_oracle _ _ _ _ = _’ mp_tac >>
  simp[socket_oracle_def, socket_fn_def] >>
  rw[ffi_sock_poll_def, ffi_sock_accept_def, ffi_sock_read_def, ffi_sock_write_def] >>
  gvs[sock_poll_def, AllCaseEqs()] >> res_tac
QED

(* The same, with sched_wf (kept by every call) for the poll hypothesis *)
Theorem v12_call_wf:
  v12rel lfd ll0 s1 s2 ∧ sched_wf s1 ∧ socket_fn n ≠ NONE ∧
  EVERY (v12ok lfd s2) (call_fds n conf) ⇒
  (socket_oracle (ExtCall n) s1 conf bytes = Oracle_final FFI_failed ∧
   socket2_oracle (ExtCall n) s2 conf bytes = Oracle_final FFI_failed) ∨
  ∃out s1' s2'. socket_oracle (ExtCall n) s1 conf bytes = Oracle_return s1' out ∧
                socket2_oracle (ExtCall n) s2 conf bytes = Oracle_return s2' out ∧
                v12rel lfd ll0 s1' s2' ∧ sched_wf s1'
Proof
  strip_tac >>
  ‘n = «sock_poll» ⇒ step_ok s1 (next_step s1)’
    by (fs[sched_wf_def] >> first_x_assum (qspec_then ‘0’ mp_tac) >> simp[ticks_def]) >>
  drule_all v12_call >> disch_then (qspec_then ‘bytes’ strip_assume_tac) >> simp[] >>
  metis_tac[socket_oracle_sched_wf]
QED

(* ------------------------------------------------------------------------
   The start, and the version-2 world's fairness
   ------------------------------------------------------------------------ *)

Theorem sched_conns_prefix[local]:
  ∀m n ll. m ≤ n ⇒ sched_conns m ll ≼ sched_conns n ll
Proof
  Induct >> simp[sched_conns_def] >> Cases_on ‘n’ >> simp[sched_conns_def] >>
  rpt strip_tac >> CASE_TAC >> simp[]
QED

Theorem sched_conns_EL:
  j < LENGTH (sched_conns m ll) ∧ j < LENGTH (sched_conns n ll) ⇒
  EL j (sched_conns m ll) = EL j (sched_conns n ll)
Proof
  ‘m ≤ n ∨ n ≤ m’ by decide_tac >>
  imp_res_tac sched_conns_prefix >>
  metis_tac[IS_PREFIX_LENGTH, is_prefix_el]
QED

(* The fd of the j-th connect is the j-th connection of any long enough
   prefix of the schedule *)
Theorem conn_fd_sched:
  j < LENGTH (sched_conns m ll) ⇒ conn_fd ll j = EL j (sched_conns m ll)
Proof
  rw[conn_fd_def]
  >- (numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
      rw[] >> metis_tac[sched_conns_EL])
  >> metis_tac[]
QED

(* Left alone, a fair world's connections stay distinct and are never the
   listener *)
Theorem core_conns_distinct:
  ∀n cs k s1 s2. v12core lfd cs k s1 s2 ∧ sched_wf s1 ⇒
                 ALL_DISTINCT (cs ++ sched_conns n s1.sched) ∧
                 ¬MEM lfd (cs ++ sched_conns n s1.sched)
Proof
  Induct >- (simp[sched_conns_def] >> rw[v12core_def]) >>
  rpt gen_tac >> strip_tac >> simp[sched_conns_def] >>
  Cases_on ‘LHD s1.sched’ >> simp[] >- fs[v12core_def] >>
  rename1 ‘LHD s1.sched = SOME st’ >>
  ‘step_ok (s1 with sched := THE (LTL s1.sched)) st’
    by (fs[sched_wf_def] >> first_x_assum (qspec_then ‘0’ mp_tac) >>
        simp[ticks_def, next_step_def, step_ok_with_sched]) >>
  ‘v12core lfd cs k (s1 with sched := THE (LTL s1.sched)) s2’ by fs[v12core_def] >>
  drule_all v12core_step >> simp[rn1_step_conns] >> strip_tac >>
  ‘sched_wf (FOLDL deliver1 (s1 with sched := THE (LTL s1.sched)) st)’
    by (‘FOLDL deliver1 (s1 with sched := THE (LTL s1.sched)) st = tick s1’
          by simp[tick_def, deliver_def] >>
        metis_tac[sched_wf_tick]) >>
  qpat_x_assum ‘∀cs k s1 s2. _’ drule_all >> simp[FOLDL_deliver1_sched]
QED

(* MAIN: a version-1 server world and its version-2 world are related *)
Theorem v12rel_init:
  sk.listeners = [(lfd, [])] ∧ sk.conns = [] ∧ sched_wf sk ∧
  (∀m. LENGTH (sched_conns m sk.sched) + 3 < dimword (:64)) ⇒
  v12rel lfd sk.sched sk (v2of1 lfd sk)
Proof
  strip_tac >>
  ‘v12core lfd [] 0 sk (v2of1 lfd sk)’ by simp[v12core_def, v2of1_def] >>
  ‘∀m. ALL_DISTINCT (sched_conns m sk.sched) ∧ ¬MEM lfd (sched_conns m sk.sched)’
    by metis_tac[core_conns_distinct, APPEND] >>
  ‘∀m j. j < LENGTH (sched_conns m sk.sched) ⇒
         conn_fd sk.sched j = EL j (sched_conns m sk.sched)’ by metis_tac[conn_fd_sched] >>
  simp[v12rel_def] >> qexistsl_tac [‘[]’, ‘0’] >> simp[] >>
  simp[v2of1_def] >> reverse conj_tac >- fs[] >> rpt strip_tac >>
  qabbrev_tac ‘cl = sched_conns m sk.sched’ >>
  ‘conn_fd sk.sched j = EL j cl’ by fs[Abbr ‘cl’] >>
  ‘ALL_DISTINCT cl ∧ ¬MEM lfd cl’ by simp[Abbr ‘cl’] >>
  ‘MEM (EL j cl) (DROP j cl)’ by (simp[MEM_EL] >> qexists_tac ‘0’ >> simp[EL_DROP]) >>
  ‘ALL_DISTINCT (TAKE j cl ++ DROP j cl)’ by simp[TAKE_DROP] >>
  ‘¬MEM (EL j cl) (TAKE j cl)’ by (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘EL j cl ≠ lfd’ by metis_tac[MEM_EL] >>
  simp[alloc1_def, exp_used_def]
QED

Theorem v12core_arrival_ok2[local]:
  v12core lfd cs k s1 s2 ∧ arrival_ok s1 a ∧
  LENGTH s2.reserved + LENGTH (FST (rn1_arr cs a)) + 3 < dimword (:64) ⇒
  arrival_ok2 s2 (SND (rn1_arr cs a))
Proof
  Cases_on ‘a’ >> simp[rn1_arr_def, arrival_ok_def, arrival_ok2_def] >> strip_tac
  >- (gvs[v12core_def, is_listener_def] >> Cases_on ‘lfd = c’ >> gvs[])
  >> rename1 ‘ALOOKUP s1.conns c = SOME cn’ >>
  ‘MEM c cs’ by (fs[v12core_def] >> metis_tac[ALOOKUP_conns_MEM, NOT_NONE_SOME]) >>
  ‘∃j. j < LENGTH cs ∧ c = EL j cs’ by metis_tac[MEM_EL] >>
  ‘findi c cs = j’ by (fs[v12core_def] >> simp[findi_EL]) >>
  fs[v12core_def] >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem rn1_arr_conns[local]:
  FST (rn1_arr cs a) ++ step_conns as = cs ++ step_conns (a :: as)
Proof
  Cases_on ‘a’ >> simp[rn1_arr_def, step_conns_def]
QED

Theorem deliver2_reserved[local]:
  (deliver2 s b).reserved = s.reserved
Proof
  Cases_on ‘b’ >> rw[deliver2_def, update_client_def]
QED

Theorem v12core_step_ok2[local]:
  ∀st cs s1 s2.
    v12core lfd cs k s1 s2 ∧ step_ok s1 st ∧
    LENGTH s2.reserved + LENGTH (cs ++ step_conns st) + 3 < dimword (:64) ⇒
    step_ok2 s2 (SND (rn1_step cs st))
Proof
  Induct >> simp[rn1_step_def, step_ok_def, step_ok2_def] >> rpt gen_tac >> strip_tac >>
  ‘LENGTH s2.reserved + LENGTH (FST (rn1_arr cs h) ++ step_conns st) + 3 < dimword (:64)’
    by (simp_tac std_ss [rn1_arr_conns] >> fs[]) >>
  Cases_on ‘rn1_arr cs h’ >> rename1 ‘rn1_arr cs h = (cs1, b)’ >>
  Cases_on ‘rn1_step cs1 st’ >> simp[step_ok2_def] >> fs[] >>
  conj_tac
  >- (‘b = SND (rn1_arr cs h)’ by simp[] >> pop_assum SUBST1_TAC >>
      irule v12core_arrival_ok2 >> simp[] >> metis_tac[]) >>
  drule_all v12core_deliver >> simp[] >> strip_tac >>
  qpat_x_assum ‘∀cs' s1' s2'. _’ (qspecl_then [‘cs1’, ‘deliver1 s1 h’, ‘deliver2 s2 b’] mp_tac) >>
  simp[deliver2_reserved]
QED

(* MAIN: the related version-2 world is fair *)
Theorem v12rel_sched_wf2:
  v12rel lfd ll0 s1 s2 ∧ sched_wf s1 ⇒ lifetime_fair s2
Proof
  ‘∀n s1 s2. v12rel lfd ll0 s1 s2 ∧ sched_wf s1 ⇒
             v12rel lfd ll0 (ticks n s1) (ticks2 n s2) ∧ sched_wf (ticks n s1)’
    by (Induct >> simp[ticks_def, ticks2_def] >> rpt gen_tac >> strip_tac >>
        first_x_assum irule >> simp[sched_wf_tick] >>
        irule v12rel_tick >> simp[] >>
        fs[sched_wf_def] >> first_x_assum (qspec_then ‘0’ mp_tac) >> simp[ticks_def]) >>
  rw[lifetime_fair_def] >> first_x_assum drule_all >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qabbrev_tac ‘t1 = ticks n s1’ >> qabbrev_tac ‘t2 = ticks2 n s2’ >>
  ‘step_ok t1 (next_step t1)’
    by (fs[sched_wf_def] >> first_x_assum (qspec_then ‘0’ mp_tac) >> simp[ticks_def]) >>
  fs[v12rel_def] >>
  simp[next_step2_def, rn1_sched_LHD] >>
  Cases_on ‘LHD t1.sched’ >> simp[step_ok2_def] >>
  irule v12core_step_ok2 >> fs[next_step_def] >>
  ‘sched_conns 1 t1.sched = step_conns x’
    by (REWRITE_TAC[ONE] >> asm_simp_tac (srw_ss()) [sched_conns_def]) >>
  conj_tac >- (qpat_x_assum ‘∀m. LENGTH cs' + _ < _’ (qspec_then ‘1’ mp_tac) >>
               asm_rewrite_tac[] >> simp[]) >>
  metis_tac[]
QED
