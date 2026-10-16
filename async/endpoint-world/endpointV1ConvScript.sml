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
  qabbrev_tac ‘cs = cfds al res lfd n’ >>
  ‘LENGTH (exp_used res lfd cs n) < dimword (:64)’
    by simp[exp_used_def, Abbr ‘cs’, LENGTH_TAKE] >>
  ‘¬MEM (al n (exp_used res lfd cs n)) (exp_used res lfd cs n)’ by fs[alloc_ok_def] >>
  fs[exp_used_def, Abbr ‘cs’, TAKE_LENGTH_ID, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The schedule, with clients named by their fds
   ------------------------------------------------------------------------ *)

(* n: the clients so far *)
Definition rn2_arr_def:
  rn2_arr F n (Connect2 l) = (n + 1, Connect l (F n)) ∧
  rn2_arr F n (Data2 j bs) = (n, Data (F j) bs) ∧
  rn2_arr F n (Eof2 j) = (n, Eof (F j))
End

Definition rn2_step_def:
  rn2_step F n [] = (n, []) ∧
  rn2_step F n (a :: as) =
    let (n1, b) = rn2_arr F n a;
        (n2, bs) = rn2_step F n1 as
    in (n2, b :: bs)
End

Definition rn2_sched_def:
  rn2_sched F n ll =
    LUNFOLD (λ(n, ll). case LHD ll of
                       | NONE => NONE
                       | SOME st => SOME ((FST (rn2_step F n st), THE (LTL ll)),
                                          SND (rn2_step F n st))) (n, ll)
End

Theorem rn2_sched_LHD:
  LHD (rn2_sched F n ll) = OPTION_MAP (λst. SND (rn2_step F n st)) (LHD ll)
Proof
  simp[rn2_sched_def, Once LUNFOLD] >> CASE_TAC >> simp[]
QED

Theorem rn2_sched_LTL:
  LHD ll = SOME st ⇒
  LTL (rn2_sched F n ll) = SOME (rn2_sched F (FST (rn2_step F n st)) (THE (LTL ll)))
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

Theorem rn2_step_mono[local]:
  ∀st n. n ≤ FST (rn2_step F n st)
Proof
  Induct >> simp[rn2_step_def] >> Cases >> simp[rn2_arr_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  TRY (first_x_assum (qspec_then ‘n + 1’ mp_tac) >> simp[] >> NO_TAC) >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED

Theorem findi_GENLIST[local]:
  (∀i i'. i < N ∧ i' < N ∧ F i = F i' ⇒ i = i') ∧ j < n ∧ n ≤ N ⇒
  findi (F j) (GENLIST F n) = j
Proof
  strip_tac >>
  ‘ALL_DISTINCT (GENLIST F n)’
    by (simp[ALL_DISTINCT_GENLIST] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  ‘F j = EL j (GENLIST F n)’ by simp[EL_GENLIST] >>
  pop_assum SUBST1_TAC >> irule findi_EL >> simp[]
QED

(* MAIN: naming the clients by their fds, then numbering the connections
   in connect order, gives the step back *)
Theorem rn1_rn2_step:
  ∀st n. (∀i i'. i < N ∧ i' < N ∧ F i = F i' ⇒ i = i') ∧ ix_ok n st ∧
         FST (rn2_step F n st) ≤ N ⇒
         rn1_step (GENLIST F n) (SND (rn2_step F n st)) =
           (GENLIST F (FST (rn2_step F n st)), st)
Proof
  Induct >> simp[rn2_step_def, rn1_step_def] >> Cases >>
  simp[ix_ok_def, rn2_arr_def, rn1_arr_def] >> rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[])
  >- (‘GENLIST F n ++ [F n] = GENLIST F (n + 1)’ by simp[GSYM ADD1, GENLIST, SNOC_APPEND] >>
      gvs[] >> first_x_assum (qspec_then ‘n + 1’ mp_tac) >> simp[])
  >> (‘n ≤ FST (rn2_step F n st)’ by simp[rn2_step_mono] >>
      first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
      simp[findi_GENLIST])
QED

(* ------------------------------------------------------------------------
   Left alone
   ------------------------------------------------------------------------ *)

Theorem rn2_step_count[local]:
  ∀st n. FST (rn2_step F n st) = n + LENGTH (FILTER is_conn2 st)
Proof
  Induct >> simp[rn2_step_def] >> Cases >> simp[rn2_arr_def, is_conn2_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  TRY (first_x_assum (qspec_then ‘n + 1’ mp_tac) >> simp[] >> NO_TAC) >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED

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
  ∀st n. step_conns (SND (rn2_step F n st)) =
         GENLIST (λi. F (n + i)) (LENGTH (FILTER is_conn2 st))
Proof
  Induct >> simp[rn2_step_def, step_conns_def] >> Cases >>
  simp[rn2_arr_def, is_conn2_def] >> rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  fs[GSYM step_conns_def]
  >- (first_x_assum (qspec_then ‘n + 1’ mp_tac) >> simp[] >> strip_tac >>
      simp[GENLIST_CONS, combinTheory.o_DEF, ADD1])
  >> first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
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
