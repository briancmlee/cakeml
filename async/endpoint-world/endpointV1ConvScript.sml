(*
  Version 2 as version 1 (the converse of endpointV1Sim; toward the ⇒
  directions of the disciplined sym_equiv claims).

  From a version-2 server world sk2 that connects at most M clients
  (LENGTH reserved + M + 3 < 2^64), the version-1 world v1of2 lfd sk2:
   - client j's fd is the fd sk2's allocation gives it when it is accepted
     in a disciplined run without close, in order (cfds): the allocation's
     argument is then known in advance (exp_used);
   - the schedule is sk2's, with each client named by its fd (rn2_sched).
  It is a version-1 server world connecting at most M clients, related to
  sk2 by endpointV1Sim's v12rel (v1of2_props).
*)
Theory endpointV1Conv
Ancestors
  llist ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec socketV2FFI socketV2Fair
  EchoSpec2 endpointV2Sim endpointEcho2 endpointV1Sim
Libs
  preamble

(* ------------------------------------------------------------------------
   The clients' fds
   ------------------------------------------------------------------------ *)

Definition cfds_def:
  cfds al res lfd 0 = [] ∧
  cfds al res lfd (SUC n) =
    cfds al res lfd n ++ [al n (exp_used res lfd (cfds al res lfd n) n)]
End

Theorem LENGTH_cfds[simp]:
  ∀n. LENGTH (cfds al res lfd n) = n
Proof
  Induct >> simp[cfds_def]
QED

Theorem cfds_prefix[local]:
  ∀n m. m ≤ n ⇒ cfds al res lfd m ≼ cfds al res lfd n
Proof
  Induct >> simp[cfds_def] >> rpt strip_tac >>
  Cases_on ‘m = SUC n’ >> simp[cfds_def] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘cfds al res lfd n’ >> simp[]
QED

(* Client j's fd *)
Definition cfd_def:
  cfd al res lfd j = EL j (cfds al res lfd (SUC j))
End

Theorem cfds_GENLIST:
  cfds al res lfd n = GENLIST (cfd al res lfd) n
Proof
  simp[LIST_EQ_REWRITE, cfd_def] >> rpt strip_tac >>
  ‘cfds al res lfd (SUC x) ≼ cfds al res lfd n’ by simp[cfds_prefix] >>
  metis_tac[is_prefix_el, LENGTH_cfds, DECIDE “x < SUC x”]
QED

Theorem cfd_alloc:
  cfd al res lfd j = al j (exp_used res lfd (GENLIST (cfd al res lfd) j) j)
Proof
  simp[cfd_def, cfds_def, EL_APPEND2, GSYM cfds_GENLIST]
QED

(* With room, the kernel gives distinct fds, none the listener or reserved *)
Theorem cfds_fresh:
  ∀n. alloc_ok al ∧ LENGTH res + n + 1 < dimword (:64) ⇒
      ALL_DISTINCT (cfds al res lfd n) ∧ ¬MEM lfd (cfds al res lfd n) ∧
      ∀c. MEM c res ⇒ ¬MEM c (cfds al res lfd n)
Proof
  Induct >> simp[cfds_def] >> strip_tac >> fs[] >>
  ‘LENGTH (exp_used res lfd (cfds al res lfd n) n) < dimword (:64)’
    by simp[exp_used_def, LENGTH_TAKE] >>
  ‘¬MEM (al n (exp_used res lfd (cfds al res lfd n) n))
        (exp_used res lfd (cfds al res lfd n) n)’ by fs[alloc_ok_def] >>
  ‘TAKE n (cfds al res lfd n) = cfds al res lfd n’ by metis_tac[TAKE_LENGTH_ID, LENGTH_cfds] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th, exp_used_def]) >>
                      REWRITE_TAC [th, exp_used_def]) >>
  fs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The schedule, with clients named by their fds
   ------------------------------------------------------------------------ *)

(* n: the clients so far *)
Definition rn2_arr_def:
  rn2_arr fdf n (Connect2 l) = (n + 1, Connect l (fdf n)) ∧
  rn2_arr fdf n (Data2 j bs) = (n, Data (fdf j) bs) ∧
  rn2_arr fdf n (Eof2 j) = (n, Eof (fdf j))
End

Definition rn2_step_def:
  rn2_step fdf n [] = (n, []) ∧
  rn2_step fdf n (a :: as) =
    let (n1, b) = rn2_arr fdf n a;
        (n2, bs) = rn2_step fdf n1 as
    in (n2, b :: bs)
End

Theorem rn2_step_cons:
  rn2_step fdf n (a :: as) =
    (FST (rn2_step fdf (FST (rn2_arr fdf n a)) as),
     SND (rn2_arr fdf n a) :: SND (rn2_step fdf (FST (rn2_arr fdf n a)) as))
Proof
  simp[rn2_step_def] >> rpt (pairarg_tac >> gvs[])
QED

Definition rn2_sched_def:
  rn2_sched fdf n ll =
    LUNFOLD (λ(n, ll). case LHD ll of
                       | NONE => NONE
                       | SOME st => SOME ((FST (rn2_step fdf n st), THE (LTL ll)),
                                          SND (rn2_step fdf n st))) (n, ll)
End

Theorem rn2_sched_LHD:
  LHD (rn2_sched fdf n ll) = OPTION_MAP (λst. SND (rn2_step fdf n st)) (LHD ll)
Proof
  simp[rn2_sched_def, Once LUNFOLD] >> CASE_TAC >> simp[]
QED

Theorem rn2_sched_LTL:
  LHD ll = SOME st ⇒
  LTL (rn2_sched fdf n ll) = SOME (rn2_sched fdf (FST (rn2_step fdf n st)) (THE (LTL ll)))
Proof
  simp[rn2_sched_def, Once LUNFOLD]
QED

(* A version-2 step's client numbers are clients so far *)
Definition ix_ok_def:
  ix_ok n [] = T ∧
  ix_ok n (Connect2 l :: as) = ix_ok (n + 1) as ∧
  ix_ok n (Data2 j bs :: as) = (j < n ∧ ix_ok n as) ∧
  ix_ok n (Eof2 j :: as) = (j < n ∧ ix_ok n as)
End

Theorem rn2_step_count[local]:
  ∀st n. FST (rn2_step fdf n st) = n + LENGTH (FILTER is_conn2 st)
Proof
  Induct >- simp[rn2_step_def] >> Cases >>
  simp[rn2_step_cons, rn2_arr_def, is_conn2_def]
QED

Theorem rn2_step_mono[local]:
  n ≤ FST (rn2_step fdf n st)
Proof
  simp[rn2_step_count]
QED

Theorem findi_GENLIST[local]:
  (∀i i'. i < N ∧ i' < N ∧ fdf i = fdf i' ⇒ i = i') ∧ j < n ∧ n ≤ N ⇒
  findi (fdf j) (GENLIST fdf n) = j
Proof
  strip_tac >>
  ‘ALL_DISTINCT (GENLIST fdf n)’
    by (simp[ALL_DISTINCT_GENLIST] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  ‘fdf j = EL j (GENLIST fdf n)’ by simp[EL_GENLIST] >>
  pop_assum SUBST1_TAC >> irule findi_EL >> simp[]
QED

(* MAIN: naming the clients by their fds, then numbering the connections
   in connect order, gives the step back *)
Theorem rn1_rn2_step:
  ∀st n. (∀i i'. i < N ∧ i' < N ∧ fdf i = fdf i' ⇒ i = i') ∧ ix_ok n st ∧
         FST (rn2_step fdf n st) ≤ N ⇒
         rn1_step (GENLIST fdf n) (SND (rn2_step fdf n st)) =
           (GENLIST fdf (FST (rn2_step fdf n st)), st)
Proof
  Induct >- simp[rn2_step_def, rn1_step_def] >> Cases >> rpt gen_tac >> strip_tac >>
  fs[ix_ok_def, rn2_step_cons, rn1_step_cons, rn2_arr_def, rn1_arr_def]
  >- (‘GENLIST fdf n ++ [fdf n] = GENLIST fdf (n + 1)’ by simp[GSYM ADD1, GENLIST, SNOC_APPEND] >>
      first_x_assum (qspec_then ‘n + 1’ mp_tac) >> simp[])
  >> (rename1 ‘ix_ok m st’ >> rename1 ‘j < m’ >>
      ‘findi (fdf j) (GENLIST fdf m) = j’
        by (irule findi_GENLIST >> simp[] >> qexists_tac ‘N’ >> simp[] >>
            ‘m ≤ FST (rn2_step fdf m st)’ by simp[rn2_step_mono] >> decide_tac) >>
      first_x_assum (qspec_then ‘m’ mp_tac) >> simp[])
QED

(* ------------------------------------------------------------------------
   Left alone
   ------------------------------------------------------------------------ *)

Theorem step_ok2_ix[local]:
  ∀st s. step_ok2 s st ⇒ ix_ok (LENGTH s.clients) st
Proof
  Induct >> simp[ix_ok_def, step_ok2_def] >> Cases >>
  simp[ix_ok_def, arrival_ok2_def] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[deliver2_def, update_client_def] >> rw[] >> fs[]
QED

(* The fds of a renamed step's connections *)
Theorem rn2_step_conns[local]:
  ∀st n. step_conns (SND (rn2_step fdf n st)) =
         GENLIST (λi. fdf (n + i)) (LENGTH (FILTER is_conn2 st))
Proof
  Induct >- simp[rn2_step_def, step_conns_def] >> Cases >> rpt gen_tac >>
  simp[rn2_step_cons, rn2_arr_def, is_conn2_def, step_conns_cons]
  >- (first_x_assum (qspec_then ‘n + 1’ mp_tac) >> simp[] >> strip_tac >>
      simp[GENLIST_CONS, combinTheory.o_DEF] >> AP_THM_TAC >> AP_TERM_TAC >>
      rw[FUN_EQ_THM] >> AP_TERM_TAC >> decide_tac)
QED

(* The version-1 world of a version-2 world *)
Definition v1of2_def:
  v1of2 lfd (sk2 : sockets2) =
    <| listeners := [(lfd, [])]; conns := [];
       sched := rn2_sched (cfd sk2.alloc sk2.reserved lfd) 0 sk2.future |>
End

Overload F2 = “λlfd (sk2:sockets2). cfd sk2.alloc sk2.reserved lfd”

(* The clients' fds are distinct, up to the bound *)
Theorem F2_inj[local]:
  alloc_ok sk2.alloc ∧ LENGTH sk2.reserved + M + 3 < dimword (:64) ⇒
  ∀i i'. i < M + 1 ∧ i' < M + 1 ∧ F2 lfd sk2 i = F2 lfd sk2 i' ⇒ i = i'
Proof
  rpt strip_tac >>
  ‘ALL_DISTINCT (GENLIST (F2 lfd sk2) (M + 1))’
    by (‘LENGTH sk2.reserved + (M + 1) + 1 < dimword (:64)’ by decide_tac >>
        drule_all (cj 1 (Q.SPEC ‘M + 1’ cfds_fresh)) >> simp[cfds_GENLIST]) >>
  fs[ALL_DISTINCT_GENLIST]
QED

(* MAIN: renamed back, the version-1 schedule is version 2's *)
Theorem v1of2_sched:
  server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ⇒
  rn1_sched [] (v1of2 lfd sk2).sched = sk2.future
Proof
  strip_tac >> simp[v1of2_def] >>
  ‘∀n. LENGTH (ticks2 n sk2).clients ≤ M’
    by (gen_tac >> fs[server_world2_def] >> drule ticks2_clients >>
        disch_then (qspec_then ‘n’ SUBST1_TAC) >> fs[]) >>
  REWRITE_TAC[rn1_sched_def] >> irule LUNFOLD_EQ >>
  qexists_tac ‘λ(cs, L) ll. ∃n. cs = GENLIST (F2 lfd sk2) (LENGTH (ticks2 n sk2).clients) ∧
                                L = rn2_sched (F2 lfd sk2) (LENGTH (ticks2 n sk2).clients)
                                      (ticks2 n sk2).future ∧
                                ll = (ticks2 n sk2).future’ >>
  reverse conj_tac >- (simp[] >> qexists_tac ‘0’ >> fs[ticks2_def, server_world2_def]) >>
  simp[FORALL_PROD] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qabbrev_tac ‘s = ticks2 n sk2’ >>
  Cases_on ‘LHD s.future’ >> simp[rn2_sched_LHD]
  >- (Cases_on ‘s.future’ >> fs[]) >>
  rename1 ‘LHD s.future = SOME st’ >>
  ‘step_ok2 s st’
    by (fs[server_world2_def, sched_wf2_def] >>
        qpat_x_assum ‘∀n. step_ok2 _ _’ (qspec_then ‘n’ mp_tac) >>
        fs[Abbr ‘s’, next_step2_def]) >>
  ‘LENGTH (ticks2 (SUC n) sk2).clients = FST (rn2_step (F2 lfd sk2) (LENGTH s.clients) st)’
    by (simp[ticks2_SUC', rn2_step_count, Abbr ‘s’] >>
        simp[tick2_def] >>
        ‘step_ok2 (ticks2 n sk2 with future := THE (LTL (ticks2 n sk2).future)) st’
          by fs[step_ok2_with_future] >>
        drule step_ok2_clients >> simp[]) >>
  ‘rn1_step (GENLIST (F2 lfd sk2) (LENGTH s.clients))
     (SND (rn2_step (F2 lfd sk2) (LENGTH s.clients) st)) =
   (GENLIST (F2 lfd sk2) (FST (rn2_step (F2 lfd sk2) (LENGTH s.clients) st)), st)’
    by (‘∀i i'. i < M + 1 ∧ i' < M + 1 ∧ F2 lfd sk2 i = F2 lfd sk2 i' ⇒ i = i'’
          by (mp_tac F2_inj >> impl_tac >- fs[server_world2_def] >> simp[]) >>
        irule rn1_rn2_step >> reverse conj_tac >- metis_tac[step_ok2_ix] >>
        qexists_tac ‘M + 1’ >> simp[] >>
        qpat_x_assum ‘LENGTH (ticks2 (SUC n) sk2).clients = _’ (SUBST1_TAC o SYM) >>
        qpat_x_assum ‘∀n. LENGTH _ ≤ M’ (qspec_then ‘SUC n’ mp_tac) >> decide_tac) >>
  simp[] >>
  ‘∃ll'. s.future = st ::: ll'’ by (Cases_on ‘s.future’ >> fs[]) >>
  simp[rn2_sched_LTL] >>
  qexists_tac ‘SUC n’ >>
  simp[ticks2_SUC', Abbr ‘s’] >> simp[tick2_def] >>
  simp[deliver2_future] >>
  mp_tac (Q.INST [‘ll’ |-> ‘st ::: ll'’, ‘fdf’ |-> ‘F2 lfd sk2’,
                  ‘n’ |-> ‘LENGTH (ticks2 n sk2).clients’] rn2_sched_LTL) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The version-1 world is fair
   ------------------------------------------------------------------------ *)

(* MAIN (arrivals, the converse of v12core_deliver's premise): an effective
   version-2 step, its clients named by their (fresh) fds, is an effective
   version-1 step, and the relation follows it *)
Theorem v12core_step_rev:
  ∀st2 n s1 s2.
    v12core lfd (GENLIST fdf n) k s1 s2 ∧ step_ok2 s2 st2 ∧
    (∀i i'. i < N ∧ i' < N ∧ fdf i = fdf i' ⇒ i = i') ∧ (∀i. i < N ⇒ fdf i ≠ lfd) ∧
    FST (rn2_step fdf n st2) ≤ N ⇒
    step_ok s1 (SND (rn2_step fdf n st2))
Proof
  Induct >- simp[rn2_step_def, step_ok_def] >>
  Cases >> rpt gen_tac >> strip_tac
  >- ((* a connect: the next client, on its fresh fd *)
      fs[rn2_step_cons, rn2_arr_def, step_ok_def, step_ok2_def] >>
      rename1 ‘arrival_ok2 s2 (Connect2 l)’ >>
      ‘n < N’ by (‘n + 1 ≤ FST (rn2_step fdf (n + 1) st2)’ by simp[rn2_step_mono] >>
                  decide_tac) >>
      ‘¬MEM (fdf n) (GENLIST fdf n)’
        by (simp[MEM_GENLIST] >> rpt strip_tac >> rename1 ‘fdf n = fdf q’ >>
            ‘q < N’ by decide_tac >> ‘n = q’ by metis_tac[] >> fs[]) >>
      ‘arrival_ok s1 (Connect l (fdf n))’
        by (fs[arrival_ok2_def, v12core_def, arrival_ok_def, is_listener_def, is_conn_def,
               ALOOKUP_NONE] >> gvs[AllCaseEqs()] >> rw[] >> metis_tac[MEM_REVERSE]) >>
      simp[] >>
      drule_all v12core_deliver >> simp[rn1_arr_def] >> strip_tac >>
      ‘GENLIST fdf n ++ [fdf n] = GENLIST fdf (n + 1)’
        by simp[GSYM ADD1, GENLIST, SNOC_APPEND] >>
      fs[] >> first_x_assum irule >> simp[] >> metis_tac[])
  >- ((* data from a client *)
      fs[rn2_step_cons, rn2_arr_def, step_ok_def, step_ok2_def] >>
      rename1 ‘arrival_ok2 s2 (Data2 j bs)’ >> rename1 ‘v12core lfd (GENLIST fdf m) k s1 s2’ >>
      ‘j < m’ by fs[arrival_ok2_def, v12core_def] >>
      ‘findi (fdf j) (GENLIST fdf m) = j’
        by (irule findi_GENLIST >> conj_tac >- first_assum ACCEPT_TAC >>
            qexists_tac ‘N’ >> simp[] >>
            ‘m ≤ FST (rn2_step fdf m st2)’ by simp[rn2_step_mono] >> decide_tac) >>
      ‘arrival_ok s1 (Data (fdf j) bs)’
        by (fs[arrival_ok2_def, arrival_ok_def, v12core_def] >>
            qpat_x_assum ‘∀j. j < m ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[EL_GENLIST] >>
            TRY (impl_tac >- fs[]) >> strip_tac >> qexists_tac ‘cn’ >> fs[]) >>
      simp[] >>
      drule_all v12core_deliver >> simp[rn1_arr_def] >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> (* EOF from a client *)
  fs[rn2_step_cons, rn2_arr_def, step_ok_def, step_ok2_def] >>
  rename1 ‘arrival_ok2 s2 (Eof2 j)’ >> rename1 ‘v12core lfd (GENLIST fdf m) k s1 s2’ >>
  ‘j < m’ by fs[arrival_ok2_def, v12core_def] >>
  ‘findi (fdf j) (GENLIST fdf m) = j’
    by (irule findi_GENLIST >> conj_tac >- first_assum ACCEPT_TAC >>
        qexists_tac ‘N’ >> simp[] >>
        ‘m ≤ FST (rn2_step fdf m st2)’ by simp[rn2_step_mono] >> decide_tac) >>
  ‘arrival_ok s1 (Eof (fdf j))’
    by (fs[arrival_ok2_def, arrival_ok_def, v12core_def] >>
        qpat_x_assum ‘∀j. j < m ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[EL_GENLIST] >>
            TRY (impl_tac >- fs[]) >> strip_tac >> qexists_tac ‘cn’ >> fs[]) >>
  simp[] >>
  drule_all v12core_deliver >> simp[rn1_arr_def] >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* The clients after a tick of the world left alone *)
Theorem ticks2_count:
  server_world2 lfd sk2 ∧ LHD (ticks2 n sk2).future = SOME st ⇒
  LENGTH (ticks2 (SUC n) sk2).clients = FST (rn2_step fdf (LENGTH (ticks2 n sk2).clients) st)
Proof
  strip_tac >>
  ‘step_ok2 (ticks2 n sk2) st’
    by (fs[server_world2_def, sched_wf2_def] >>
        qpat_x_assum ‘∀n. step_ok2 _ _’ (qspec_then ‘n’ mp_tac) >> fs[next_step2_def]) >>
  simp[ticks2_SUC', rn2_step_count, tick2_def] >>
  ‘step_ok2 (ticks2 n sk2 with future := THE (LTL (ticks2 n sk2).future)) st’
    by fs[step_ok2_with_future] >>
  drule step_ok2_clients >> simp[]
QED

(* The clients' fds are fresh, up to the bound *)
Theorem F2_fresh:
  alloc_ok sk2.alloc ∧ LENGTH sk2.reserved + M + 3 < dimword (:64) ⇒
  (∀i i'. i < M + 1 ∧ i' < M + 1 ∧ F2 lfd sk2 i = F2 lfd sk2 i' ⇒ i = i') ∧
  (∀i. i < M + 1 ⇒ F2 lfd sk2 i ≠ lfd)
Proof
  strip_tac >> conj_tac >- (mp_tac F2_inj >> simp[]) >>
  rpt strip_tac >>
  ‘LENGTH sk2.reserved + (M + 1) + 1 < dimword (:64)’ by decide_tac >>
  drule_all (cj 2 (Q.SPEC ‘M + 1’ cfds_fresh)) >> simp[cfds_GENLIST, MEM_GENLIST] >>
  metis_tac[]
QED

(* MAIN: left alone, the version-1 world follows the version-2 world, and
   every step it takes is effective *)
Theorem v1of2_ticks:
  server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ⇒
  ∀m. v12core lfd (GENLIST (F2 lfd sk2) (LENGTH (ticks2 m sk2).clients)) 0
               (ticks m (v1of2 lfd sk2)) (ticks2 m sk2) ∧
      (ticks m (v1of2 lfd sk2)).sched =
        rn2_sched (F2 lfd sk2) (LENGTH (ticks2 m sk2).clients) (ticks2 m sk2).future ∧
      step_ok (ticks m (v1of2 lfd sk2)) (next_step (ticks m (v1of2 lfd sk2)))
Proof
  strip_tac >>
  ‘∀n. LENGTH (ticks2 n sk2).clients ≤ M’
    by (gen_tac >> fs[server_world2_def] >> drule ticks2_clients >>
        disch_then (qspec_then ‘n’ SUBST1_TAC) >> fs[]) >>
  ‘(∀i i'. i < M + 1 ∧ i' < M + 1 ∧ F2 lfd sk2 i = F2 lfd sk2 i' ⇒ i = i') ∧
   (∀i. i < M + 1 ⇒ F2 lfd sk2 i ≠ lfd)’
    by (irule F2_fresh >> fs[server_world2_def]) >>
  qabbrev_tac ‘s1 = v1of2 lfd sk2’ >>
  (* the step is effective, given the relation *)
  ‘∀m. v12core lfd (GENLIST (F2 lfd sk2) (LENGTH (ticks2 m sk2).clients)) 0
            (ticks m s1) (ticks2 m sk2) ∧
       (ticks m s1).sched =
         rn2_sched (F2 lfd sk2) (LENGTH (ticks2 m sk2).clients) (ticks2 m sk2).future ⇒
       step_ok (ticks m s1) (next_step (ticks m s1))’
    by (rpt strip_tac >> simp[next_step_def, rn2_sched_LHD] >>
        Cases_on ‘LHD (ticks2 m sk2).future’ >> simp[step_ok_def] >>
        rename1 ‘LHD (ticks2 m sk2).future = SOME st2’ >>
        qspecl_then [‘st2’, ‘LENGTH (ticks2 m sk2).clients’, ‘ticks m s1’, ‘ticks2 m sk2’]
          mp_tac (Q.INST [‘k’ |-> ‘0’, ‘N’ |-> ‘M + 1’, ‘fdf’ |-> ‘F2 lfd sk2’]
                    v12core_step_rev) >>
        impl_tac >- (
          simp[] >> conj_tac
          >- (fs[server_world2_def, sched_wf2_def] >>
              qpat_x_assum ‘∀n. step_ok2 _ _’ (qspec_then ‘m’ mp_tac) >> fs[next_step2_def]) >>
          drule_all (Q.INST [‘fdf’ |-> ‘F2 lfd sk2’] ticks2_count) >>
          disch_then (SUBST1_TAC o SYM) >>
          qpat_x_assum ‘∀n. LENGTH _ ≤ M’ (qspec_then ‘SUC m’ mp_tac) >> decide_tac) >>
        simp[]) >>
  Induct
  >- (simp[ffiSpikeSocketFairTheory.ticks_def, ticks2_def] >>
      ‘v12core lfd [] 0 s1 sk2 ∧
       s1.sched = rn2_sched (F2 lfd sk2) 0 sk2.future’
        by fs[server_world2_def, v12core_def, Abbr ‘s1’, v1of2_def] >>
      fs[server_world2_def] >>
      first_x_assum (qspec_then ‘0’ mp_tac) >>
      fs[ffiSpikeSocketFairTheory.ticks_def, ticks2_def]) >>
  strip_tac >>
  qabbrev_tac ‘t1 = ticks m s1’ >> qabbrev_tac ‘t2 = ticks2 m sk2’ >>
  ‘v12core lfd (GENLIST (F2 lfd sk2) (LENGTH (ticks2 (SUC m) sk2).clients)) 0
          (ticks (SUC m) s1) (ticks2 (SUC m) sk2) ∧
   (ticks (SUC m) s1).sched =
     rn2_sched (F2 lfd sk2) (LENGTH (ticks2 (SUC m) sk2).clients) (ticks2 (SUC m) sk2).future’
    by (simp[ffiSpikeSocketFairTheory.ticks_SUC, ticks2_SUC'] >>
  Cases_on ‘LHD t2.future’
  >- (‘LHD t1.sched = NONE’
        by (‘t1.sched = rn2_sched (F2 lfd sk2) (LENGTH t2.clients) t2.future’ by metis_tac[] >>
            pop_assum SUBST1_TAC >> REWRITE_TAC[rn2_sched_LHD] >>
            qpat_x_assum ‘LHD t2.future = _’ SUBST1_TAC >> simp[]) >>
      simp[tick_def, tick2_def]) >>
  rename1 ‘LHD t2.future = SOME st2’ >>
  qabbrev_tac ‘n = LENGTH t2.clients’ >>
  ‘t1.sched = rn2_sched (F2 lfd sk2) n t2.future’ by (simp[Abbr ‘n’] >> metis_tac[]) >>
  ‘LHD t1.sched = SOME (SND (rn2_step (F2 lfd sk2) n st2))’
    by (qpat_x_assum ‘t1.sched = _’ SUBST1_TAC >> REWRITE_TAC[rn2_sched_LHD] >>
        qpat_x_assum ‘LHD t2.future = _’ SUBST1_TAC >> simp[]) >>
  ‘LENGTH (tick2 t2).clients = FST (rn2_step (F2 lfd sk2) n st2)’
    by (simp[Abbr ‘t2’, Abbr ‘n’, GSYM ticks2_SUC'] >>
        drule_all (Q.INST [‘fdf’ |-> ‘F2 lfd sk2’] ticks2_count) >> simp[]) >>
  ‘step_ok t1 (SND (rn2_step (F2 lfd sk2) n st2))’
    by (‘next_step t1 = SND (rn2_step (F2 lfd sk2) n st2)’ by fs[next_step_def] >>
        metis_tac[]) >>
  ‘rn1_step (GENLIST (F2 lfd sk2) n) (SND (rn2_step (F2 lfd sk2) n st2)) =
   (GENLIST (F2 lfd sk2) (FST (rn2_step (F2 lfd sk2) n st2)), st2)’
    by (‘LENGTH (tick2 t2).clients ≤ M’
          by (qpat_x_assum ‘∀n. LENGTH _ ≤ M’ (qspec_then ‘SUC m’ mp_tac) >>
              simp[ticks2_SUC', Abbr ‘t2’]) >>
        ‘step_ok2 t2 st2’
          by (fs[server_world2_def, sched_wf2_def] >>
              qpat_x_assum ‘∀n. step_ok2 _ _’ (qspec_then ‘m’ mp_tac) >>
              fs[next_step2_def, Abbr ‘t2’]) >>
        irule rn1_rn2_step >> conj_tac
        >- (qexists_tac ‘M + 1’ >> simp[] >> decide_tac) >>
        simp[Abbr ‘n’] >> metis_tac[step_ok2_ix]) >>
  ‘step_ok (t1 with sched := THE (LTL t1.sched)) (SND (rn2_step (F2 lfd sk2) n st2))’
    by fs[step_ok_with_sched] >>
  ‘v12core lfd (GENLIST (F2 lfd sk2) n) 0 (t1 with sched := THE (LTL t1.sched))
           (t2 with future := THE (LTL t2.future))’ by (REWRITE_TAC[v12core_sched] >> fs[]) >>
  drule_all v12core_step >> asm_rewrite_tac[] >> strip_tac >>
  ‘tick t1 = FOLDL deliver1 (t1 with sched := THE (LTL t1.sched))
                           (SND (rn2_step (F2 lfd sk2) n st2))’
    by (qpat_x_assum ‘LHD t1.sched = _’ (fn th => simp[tick_def, deliver_def, th])) >>
  ‘tick2 t2 = FOLDL deliver2 (t2 with future := THE (LTL t2.future)) st2’
    by (qpat_x_assum ‘LHD t2.future = _’ (fn th => simp[tick2_def, th])) >>
  ‘∃ll'. t2.future = st2 ::: ll'’ by (Cases_on ‘t2.future’ >> fs[]) >>
  ‘THE (LTL t1.sched) = rn2_sched (F2 lfd sk2) (FST (rn2_step (F2 lfd sk2) n st2)) ll'’
    by (qpat_x_assum ‘t1.sched = _’ SUBST1_TAC >>
        qpat_x_assum ‘t2.future = _’ SUBST1_TAC >>
        mp_tac (Q.INST [‘ll’ |-> ‘st2 ::: ll'’, ‘fdf’ |-> ‘F2 lfd sk2’, ‘st’ |-> ‘st2’] rn2_sched_LTL) >>
        simp[]) >>
  ‘LENGTH (FOLDL deliver2 (t2 with future := THE (LTL t2.future)) st2).clients =
   FST (rn2_step (F2 lfd sk2) n st2)’ by metis_tac[] >>
  qpat_x_assum ‘tick t1 = _’ SUBST1_TAC >> qpat_x_assum ‘tick2 t2 = _’ SUBST1_TAC >>
  qpat_x_assum ‘v12core _ (GENLIST _ (FST _)) _ _ _’ mp_tac >>
  qpat_x_assum ‘t1.sched = rn2_sched _ _ _’ (fn th => REWRITE_TAC[SYM th]) >>
  strip_tac >> asm_rewrite_tac[] >>
  simp[FOLDL_deliver1_sched, deliver2_future]) >>
  qpat_assum ‘∀m. _ ⇒ step_ok _ _’ (qspec_then ‘SUC m’ mp_tac) >> fs[]
QED

(* The connections of the renamed schedule: the clients' fds, in order *)
Theorem rn2_sched_conns[local]:
  ∀m n ll. sched_conns m (rn2_sched fdf n ll) =
           GENLIST (λi. fdf (n + i)) (LENGTH (FILTER is_conn2 (arrivals2_upto m ll)))
Proof
  Induct >> simp[sched_conns_def, arrivals2_upto_def, rn2_sched_LHD] >>
  rpt gen_tac >> Cases_on ‘LHD ll’ >> simp[] >>
  rename1 ‘LHD ll = SOME st’ >>
  imp_res_tac rn2_sched_LTL >> simp[] >>
  simp[rn2_step_conns, rn2_step_count, FILTER_APPEND] >>
  rw[LIST_EQ_REWRITE, EL_APPEND_EQN] >> AP_TERM_TAC >> decide_tac
QED

Theorem v1of2_conns:
  sched_conns m (v1of2 lfd sk2).sched = GENLIST (F2 lfd sk2) (nconn sk2 m)
Proof
  simp[v1of2_def, rn2_sched_conns, nconn_def, LIST_EQ_REWRITE]
QED

(* MAIN: the version-1 world is a server world connecting at most M
   clients, related to the version-2 world *)
Theorem v1of2_props:
  server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ⇒
  server_world lfd (v1of2 lfd sk2) ∧
  (∀m. LENGTH (sched_conns m (v1of2 lfd sk2).sched) ≤ M) ∧
  v12rel lfd (v1of2 lfd sk2).sched (v1of2 lfd sk2) sk2
Proof
  strip_tac >> drule_all v1of2_ticks >> strip_tac >>
  simp[v1of2_conns] >> rpt conj_tac
  >- (rewrite_tac[server_world_def, sched_wf_def] >>
      conj_tac >- simp[v1of2_def] >> conj_tac >- simp[v1of2_def] >> metis_tac[]) >>
  TRY (fs[] >> NO_TAC) >>
  simp[v12rel_def] >> qexistsl_tac [‘[]’, ‘0’] >>
  ‘rn1_sched [] (v1of2 lfd sk2).sched = sk2.future’ by metis_tac[v1of2_sched] >>
  pop_assum (fn th => simp[v1of2_conns, th]) >> rpt conj_tac
  >- fs[server_world2_def, v12core_def, v1of2_def]
  >- (rpt strip_tac >>
      mp_tac (Q.INST [‘ll’ |-> ‘(v1of2 lfd sk2).sched’] conn_fd_sched) >>
      simp[v1of2_conns])
  >- (rpt strip_tac >> simp[EL_GENLIST] >>
      CONV_TAC (LHS_CONV (REWRITE_CONV [exp_used_def])) >>
      simp[TAKE_GENLIST, MIN_DEF] >>
      CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [cfd_alloc])) >> simp[exp_used_def, TAKE_GENLIST])
  >> gen_tac >> qpat_x_assum ‘∀n. nconn _ _ ≤ _’ (qspec_then ‘m’ mp_tac) >> fs[]
QED
