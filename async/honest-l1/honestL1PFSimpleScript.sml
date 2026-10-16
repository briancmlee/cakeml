(*
  R2′ (design/36 §6), l1pf_simple: in simple L0 worlds, the version-2
  world R1-safe builds from the prefetching L1's own run (psk) is a DELAY
  of the kernel's schedule (sk_of's): at the end of each round, what psk
  has delivered is, per client, within what the kernel had delivered by
  then (never ahead).

  The vocabulary (upto, conns_of, data_of, within, kernel_steps,
  round_instant) is a verbatim copy of L3-00's kernelStatements
  (final/L3-00-statements); the copy goes when the layer is folded.
*)
Theory honestL1PFSimple
Ancestors
  honestL1PFConnRun honestL1PFClient honestL1PFStream honestL1PFConn honestL1PFLive honestL1PFRound
  honestL1PFInv honestL1PFRefine honestL1PFModel honestL1Refine honestL1Simple
  honestL1Steps honestL1Inv honestL1Model honestL0WorldInv honestL0WorldProps
  honestL0Rely honestL0World honestL0 socketV2FFI socketV2Fair ffiSpikeSocketFFI
  llist alist
Libs
  preamble

(* ========================================================================
   The statement's vocabulary (copied from kernelStatements)
   ======================================================================== *)

Definition upto_def:
  upto (g : num -> arrival2 list) n = FLAT (GENLIST g n)
End

Definition conns_of_def:
  conns_of (as : arrival2 list) = LENGTH (FILTER (λa. ∃l. a = Connect2 l) as)
End

Definition data_of_def:
  data_of j (as : arrival2 list) =
    FLAT (MAP (λa. case a of Data2 j' bs => if j' = j then bs else [] | _ => []) as)
End

Definition within_def:
  within as' as ⇔
    conns_of as' ≤ conns_of as ∧
    ∀j. data_of j as' ≼ data_of j as ∧ (MEM (Eof2 j) as' ⇒ MEM (Eof2 j) as)
End

Definition kernel_steps_def:
  kernel_steps p lfd sched (w1 : l0world) =
    λi. conv_step p lfd (sched (npolls w1.hist + i))
End

Definition round_instant_def:
  round_instant lfd hw ifds m w1 n =
    npolls (rworld lfd hw ifds m w1 (SUC n)).hist − npolls w1.hist
End

(* ========================================================================
   A. The kernel's version-2 world, left alone
   ======================================================================== *)

Theorem conns_of_simps[simp]:
  conns_of [] = 0 ∧
  conns_of (l1 ++ l2) = conns_of l1 + conns_of l2 ∧
  conns_of [Connect2 l] = 1 ∧ conns_of [Data2 j bs] = 0 ∧ conns_of [Eof2 j] = 0
Proof
  simp[conns_of_def, FILTER_APPEND]
QED

Theorem data_of_simps[simp]:
  data_of j [] = [] ∧
  data_of j (l1 ++ l2) = data_of j l1 ++ data_of j l2 ∧
  data_of j [Connect2 l] = [] ∧
  data_of j [Data2 i bs] = (if i = j then bs else []) ∧ data_of j [Eof2 i] = []
Proof
  simp[data_of_def]
QED

Theorem upto_SUC:
  upto g (SUC n) = upto g n ++ g n
Proof
  simp[upto_def, GENLIST, FLAT_SNOC]
QED

Theorem upto_0[simp]:
  upto g 0 = []
Proof
  simp[upto_def]
QED

Theorem ticks2_SUC:
  ∀n s. ticks2 (SUC n) s = tick2 (ticks2 n s)
Proof
  Induct >- simp[ticks2_def] >>
  rpt gen_tac >> once_rewrite_tac[ticks2_def] >> simp[]
QED

Theorem deliver2_future[simp]:
  (deliver2 s a).future = s.future
Proof
  Cases_on ‘a’ >> rw[deliver2_def, update_client_def]
QED

Theorem FOLDL_deliver2_future[simp]:
  ∀as s. (FOLDL deliver2 s as).future = s.future
Proof
  Induct >> simp[]
QED

(* The future of the world left alone for n steps *)
Theorem ticks2_future:
  ∀n s. s.future = LGENLIST g NONE ⇒
        (ticks2 n s).future = LGENLIST (λi. g (n + i)) NONE
Proof
  Induct >- simp[ticks2_def, ETA_THM] >>
  rpt strip_tac >> simp[ticks2_SUC] >> first_x_assum drule >> strip_tac >>
  simp[tick2_def, LGENLIST_EQ_CONS, LHD_LGENLIST, LTL_LGENLIST] >>
  simp[combinTheory.o_DEF, ADD1] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem tick2_LGENLIST:
  s.future = LGENLIST g NONE ⇒
  tick2 s = FOLDL deliver2 (s with future := LGENLIST (λi. g (SUC i)) NONE) (g 0)
Proof
  rw[tick2_def, LHD_LGENLIST, LTL_LGENLIST, combinTheory.o_DEF]
QED

(* What the world left alone holds: the clients connected so far, their
   data and their EOF, as in the arrivals so far *)
Definition vinv_def:
  vinv lfd s (as : arrival2 list) ⇔
    ALOOKUP s.listening lfd ≠ NONE ∧ (∀l. MEM (Connect2 l) as ⇒ l = lfd) ∧
    LENGTH s.clients = conns_of as ∧
    (∀j. j < LENGTH s.clients ⇒
         (EL j s.clients).incoming = data_of j as ∧
         ((EL j s.clients).peer_closed ⇔ MEM (Eof2 j) as)) ∧
    (∀j. LENGTH s.clients ≤ j ⇒ data_of j as = [] ∧ ¬MEM (Eof2 j) as)
End

Theorem ALOOKUP_AFUPDKEY_NONE:
  ∀ls. ALOOKUP (AFUPDKEY k g ls) l = NONE ⇔ ALOOKUP ls l = NONE
Proof
  Induct >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[] >> rw[]
QED

Theorem vinv_deliver2:
  vinv lfd s as ∧ arrival_ok2 s a ∧ (∀l. a = Connect2 l ⇒ l = lfd) ⇒
  vinv lfd (deliver2 s a) (as ++ [a])
Proof
  Cases_on ‘a’ >> simp[deliver2_def, arrival_ok2_def] >> strip_tac
  >- (fs[vinv_def, ALOOKUP_AFUPDKEY_NONE] >> rpt conj_tac
      >- (simp[] >> metis_tac[])
      >- (rpt strip_tac >>
          (Cases_on ‘j < LENGTH s.clients’
           >- (first_x_assum (qspec_then ‘j’ mp_tac) >> simp[EL_APPEND1])
           >> ‘j = LENGTH s.clients’ by fs[] >>
           qpat_x_assum ‘∀j. LENGTH _ ≤ j ⇒ _’ (qspec_then ‘j’ mp_tac) >>
           simp[EL_APPEND2, empty_conn_def]))
      >> rpt strip_tac >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[])
  >- (rename1 ‘Data2 i bs’ >> qpat_x_assum ‘vinv _ _ _’ mp_tac >>
      simp_tac std_ss [vinv_def] >> strip_tac >>
      simp_tac std_ss [vinv_def, update_client_def, LENGTH_LUPDATE] >>
      simp[] >>
      qpat_x_assum ‘LENGTH _ = conns_of _’ (SUBST_ALL_TAC o SYM) >>
      rpt strip_tac >>
      TRY (qpat_x_assum ‘∀j. j < _ ⇒ _’ (qspec_then ‘j’ mp_tac) >>
           impl_tac >- simp[] >> strip_tac >>
           simp_tac std_ss [EL_LUPDATE] >> IF_CASES_TAC >> gvs[] >> NO_TAC) >>
      TRY (qpat_x_assum ‘∀l. MEM _ _ ⇒ _’ drule >> simp[] >> NO_TAC) >>
      qpat_x_assum ‘∀j. _ ≤ j ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >>
      ‘j ≠ i’ by decide_tac >> simp[])
  >> rename1 ‘Eof2 i’ >> qpat_x_assum ‘vinv _ _ _’ mp_tac >>
  simp_tac std_ss [vinv_def] >> strip_tac >>
  simp_tac std_ss [vinv_def, update_client_def, LENGTH_LUPDATE] >>
      simp[] >>
      qpat_x_assum ‘LENGTH _ = conns_of _’ (SUBST_ALL_TAC o SYM) >>
      rpt strip_tac >>
      TRY (qpat_x_assum ‘∀j. j < _ ⇒ _’ (qspec_then ‘j’ mp_tac) >>
           impl_tac >- simp[] >> strip_tac >>
           simp_tac std_ss [EL_LUPDATE] >> IF_CASES_TAC >> gvs[] >> NO_TAC) >>
      TRY (qpat_x_assum ‘∀l. MEM _ _ ⇒ _’ drule >> simp[] >> NO_TAC) >>
      qpat_x_assum ‘∀j. _ ≤ j ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >>
      ‘j ≠ i’ by decide_tac >> simp[]
QED

Theorem vinv_FOLDL:
  ∀l s as. vinv lfd s as ∧ step_ok2 s l ∧ (∀x. MEM (Connect2 x) l ⇒ x = lfd) ⇒
           vinv lfd (FOLDL deliver2 s l) (as ++ l)
Proof
  Induct >> simp[step_ok2_def] >> rpt strip_tac >>
  ‘vinv lfd (deliver2 s h) (as ++ [h])’ by (irule vinv_deliver2 >> simp[]) >>
  first_x_assum (qspecl_then [‘deliver2 s h’, ‘as ++ [h]’] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] >> rewrite_tac[APPEND]
QED

Theorem vinv_with[simp]:
  vinv lfd (s with future := f) as ⇔ vinv lfd s as
Proof
  simp[vinv_def]
QED

Theorem conv_step_conn:
  MEM (Connect2 x) (conv_step p lfd as) ⇒ x = lfd
Proof
  simp[conv_step_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> Cases_on ‘y’ >>
  rw[conv_arr_def] >> gvs[]
QED

(* The kernel's world after n steps *)
Definition kworld_def:
  kworld p lfd sched w1 n = ticks2 n (sk_of p lfd sched w1)
End

Theorem sk_of_future:
  (sk_of p lfd sched w1).future = LGENLIST (kernel_steps p lfd sched w1) NONE
Proof
  simp[sk_of_def, fut_of_def, kernel_steps_def]
QED

Theorem kworld_SUC:
  kworld p lfd sched w1 (SUC n) =
  FOLDL deliver2 ((kworld p lfd sched w1 n) with
                    future := LGENLIST (λi. kernel_steps p lfd sched w1 (SUC n + i)) NONE)
        (kernel_steps p lfd sched w1 n)
Proof
  simp[kworld_def, ticks2_SUC] >>
  ‘(ticks2 n (sk_of p lfd sched w1)).future =
     LGENLIST (λi. kernel_steps p lfd sched w1 (n + i)) NONE’
    by (irule ticks2_future >> simp[sk_of_future]) >>
  drule tick2_LGENLIST >> simp[ADD_CLAUSES]
QED

Theorem kworld_future:
  (kworld p lfd sched w1 n).future = LGENLIST (λi. kernel_steps p lfd sched w1 (n + i)) NONE
Proof
  simp[kworld_def] >>
  mp_tac (Q.SPECL [‘n’, ‘sk_of p lfd sched w1’]
            (Q.INST [‘g’ |-> ‘kernel_steps p lfd sched w1’] ticks2_future)) >>
  simp[sk_of_future]
QED

(* MAIN (A): with a well-formed kernel schedule, the world left alone holds
   exactly the arrivals so far *)
Theorem kworld_vinv:
  w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧
  sched_wf2 (sk_of p lfd sched w1) ⇒
  ∀n. vinv lfd (kworld p lfd sched w1 n) (upto (kernel_steps p lfd sched w1) n)
Proof
  strip_tac >> Induct
  >- simp[kworld_def, ticks2_def, vinv_def, sk_of_def] >>
  simp[kworld_SUC, upto_SUC] >> irule vinv_FOLDL >> simp[] >>
  conj_tac >- (simp[kernel_steps_def] >> metis_tac[conv_step_conn]) >>
  fs[sched_wf2_def] >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[next_step2_def, GSYM kworld_def, kworld_future, LHD_LGENLIST] >>
  ‘∀s f. step_ok2 (s with future := f) = step_ok2 s’ suffices_by simp[] >>
  ‘∀l s f. step_ok2 (s with future := f) l = step_ok2 s l’ suffices_by
    (rpt strip_tac >> simp[FUN_EQ_THM]) >>
  Induct >> simp[step_ok2_def] >> rpt gen_tac >>
  ‘arrival_ok2 (s with future := f) h = arrival_ok2 s h ∧
   deliver2 (s with future := f) h = deliver2 s h with future := f’
    by (Cases_on ‘h’ >> rw[arrival_ok2_def, deliver2_def, update_client_def]) >>
  simp[]
QED

Theorem kworld_step_ok:
  sched_wf2 (sk_of p lfd sched w1) ⇒
  ∀n. step_ok2 (kworld p lfd sched w1 n) (kernel_steps p lfd sched w1 n)
Proof
  rw[sched_wf2_def] >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[next_step2_def, GSYM kworld_def, kworld_future, LHD_LGENLIST]
QED

Theorem step_ok2_with:
  ∀l s f. step_ok2 (s with future := f) l = step_ok2 s l
Proof
  Induct >> simp[step_ok2_def] >> rpt gen_tac >>
  ‘arrival_ok2 (s with future := f) h = arrival_ok2 s h ∧
   deliver2 (s with future := f) h = deliver2 s h with future := f’
    by (Cases_on ‘h’ >> rw[arrival_ok2_def, deliver2_def, update_client_def]) >>
  simp[]
QED

Theorem step_ok2_append:
  ∀l1 s. step_ok2 s (l1 ++ l2) ⇔ step_ok2 s l1 ∧ step_ok2 (FOLDL deliver2 s l1) l2
Proof
  Induct >> simp[step_ok2_def] >> metis_tac[]
QED

(* ========================================================================
   B. The L0 world against the kernel's world, and L1's fetches against
      the L0 world
   ======================================================================== *)

(* One channel against its kernel client: established, not broken, the
   peer's EOF and data are the client's *)
Definition wch_def:
  wch (a : lchan) (v : conn) ⇔
    ¬a.connecting ∧ ¬a.broken ∧ a.err = NONE ∧ (a.peer_eof ⇔ v.peer_closed) ∧
    a.peer_sent = v.incoming ∧ (a.shut ⇒ a.closed)
End

(* One channel against L1's fetches from it: d, the data fetched, then the
   kernel inbox, is the data its peer sent; e (an EOF was fetched) only
   after the peer's EOF, with nothing left in the inbox; and the program
   closes a channel only once its EOF was fetched (L1 closes on EOF only) *)
Definition dch_def:
  dch d e (a : lchan) ⇔
    d ++ a.inbox = a.peer_sent ∧ (e ⇒ a.peer_eof ∧ a.inbox = []) ∧ (a.closed ⇒ e)
End

(* The L0 world mirrors the kernel's world s *)
Definition wk_def:
  wk lfd p s (w : l0world) ⇔
    (∃q. w.listeners = [(lfd, p, q)]) ∧ LENGTH w.chans = LENGTH s.clients ∧
    ∀c. c < LENGTH w.chans ⇒ wch (EL c w.chans) (EL c s.clients)
End

(* L1's fetches so far against the L0 world: a channels have been accepted
   (the queue holds the rest, in order); an open fd's channel is its
   client in cm *)
Definition lk_def:
  lk lfd a cm D E (w : l0world) ⇔
    qof w lfd = GENLIST (λi. a + i) (LENGTH w.chans − a) ∧ a ≤ LENGTH w.chans ∧
    (∀f c. ALOOKUP w.open_fds f = SOME c ⇒
           ALOOKUP cm f = SOME c ∧ c < a ∧ ¬(EL c w.chans).closed ∧ f ≠ lfd) ∧
    (∀f g c. ALOOKUP w.open_fds f = SOME c ∧ ALOOKUP w.open_fds g = SOME c ⇒ f = g) ∧
    (∀c. c < LENGTH w.chans ⇒ dch (D c) (E c) (EL c w.chans)) ∧
    (∀c. a ≤ c ⇒ D c = [] ∧ ¬E c) ∧
    (∀c. c < a ⇒ (EL c w.chans).closed ∨ ∃f. ALOOKUP w.open_fds f = SOME c)
End

Definition sinv_def:
  sinv lfd p a cm D E s w ⇔ wk lfd p s w ∧ lk lfd a cm D E w
End

Theorem sinv_simple[simp]:
  (sinv lfd p a cm D E (s with future := f) w ⇔ sinv lfd p a cm D E s w) ∧
  (sinv lfd p a cm D E s (w with clock := k) ⇔ sinv lfd p a cm D E s w) ∧
  (sinv lfd p a cm D E s (w with hist := h) ⇔ sinv lfd p a cm D E s w)
Proof
  simp[sinv_def, wk_def, lk_def, qof_def]
QED

Theorem prefix_append_r:
  x ≼ y ⇒ x ≼ y ++ z
Proof
  rw[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem GENLIST_plus_SNOC:
  a ≤ n ⇒ GENLIST (λi. a + i) (n − a) ++ [n] = GENLIST (λi. a + i) (n + 1 − a)
Proof
  strip_tac >> ‘n + 1 − a = SUC (n − a)’ by simp[] >>
  simp[GENLIST, SNOC_APPEND]
QED

(* Per channel: the arrivals *)
Theorem ch_data:
  wch a v ∧ dch d e a ∧ ¬v.peer_closed ⇒
  wch (if a.closed then a with aborted := T
       else a with <| inbox := a.inbox ++ bs; peer_sent := a.peer_sent ++ bs |>)
      (v with incoming := v.incoming ++ bs) ∧
  dch d e (if a.closed then a with aborted := T
           else a with <| inbox := a.inbox ++ bs; peer_sent := a.peer_sent ++ bs |>)
Proof
  strip_tac >> Cases_on ‘a.closed’ >> fs[wch_def, dch_def] >> metis_tac[]
QED

Theorem ch_eof:
  wch a v ∧ dch d e a ⇒
  wch (a with peer_eof := T) (v with peer_closed := T) ∧ dch d e (a with peer_eof := T)
Proof
  rw[wch_def, dch_def]
QED

Theorem ch_drain:
  wch a v ∧ dch d e a ⇒
  wch (a with <| inflight := x; drained := y |>) v ∧
  dch d e (a with <| inflight := x; drained := y |>)
Proof
  simp[wch_def, dch_def] >> metis_tac[]
QED

Theorem ch_fresh:
  wch fresh_lchan empty_conn ∧ dch [] F fresh_lchan
Proof
  EVAL_TAC
QED

(* One arrival *)
Theorem sinv_deliver:
  sinv lfd p a cm D E s w ∧ (∀x. conv_arr p lfd ar = [x] ⇒ arrival_ok2 s x) ∧
  (∀j e k. ar ≠ LBreak j e k) ⇒
  sinv lfd p a cm D E (FOLDL deliver2 s (conv_arr p lfd ar)) (l0_deliver w ar)
Proof
  Cases_on ‘ar’ >> simp_tac std_ss [conv_arr_def] >> strip_tac >>
  qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def])
  >- ((* LIncoming *)
      reverse (Cases_on ‘n = p’)
      >- (simp[l0_deliver_def] >>
          ‘FILTER (λ(l,p',q). p' = n) w.listeners = []’ by simp[] >>
          simp[sinv_def, wk_def, lk_def] >> metis_tac[]) >>
      gvs[] >>
      ‘ALOOKUP s.listening lfd ≠ NONE’
        by fs[arrival_ok2_def] >>
      simp[l0_deliver_def, deliver2_def, AFUPDKEY_def] >>
      simp_tac std_ss [sinv_def, wk_def, lk_def] >>
      simp[qof_def, GENLIST_plus_SNOC] >> rpt conj_tac
      >- (rpt strip_tac >> Cases_on ‘c < LENGTH w.chans’
          >- gvs[EL_APPEND1]
          >> ‘c = LENGTH w.chans’ by simp[] >> gvs[EL_APPEND2, ch_fresh])
      >- (‘q = GENLIST (λi. a + i) (LENGTH s.clients − a)’ by gvs[qof_def] >>
          simp[GENLIST_plus_SNOC])
      >- (rpt strip_tac >> res_tac >> ‘c < LENGTH w.chans’ by simp[] >> gvs[EL_APPEND1])
      >> (rpt strip_tac >> Cases_on ‘c < LENGTH w.chans’
          >- (gvs[EL_APPEND1] >> metis_tac[])
          >> ‘c = LENGTH w.chans’ by fs[] >> simp[EL_APPEND2] >>
          ‘D c = [] ∧ ¬E c’ by gvs[] >> gvs[ch_fresh]))
  >- ((* LData *)
      rename1 ‘LData j bs’ >>
      ‘arrival_ok2 s (Data2 j bs)’ by (first_x_assum irule >> simp[]) >>
      pop_assum (strip_assume_tac o SIMP_RULE std_ss [arrival_ok2_def]) >>
      ‘j < LENGTH w.chans’ by simp[] >>
      ‘wch (EL j w.chans) (EL j s.clients) ∧ dch (D j) (E j) (EL j w.chans)’ by simp[] >>
      ‘¬(EL j w.chans).peer_eof ∧ ¬(EL j w.chans).broken ∧ ¬(EL j w.chans).connecting’
        by gvs[wch_def] >>
      drule_all ch_data >> disch_then (qspec_then ‘bs’ strip_assume_tac) >>
      simp[l0_deliver_def, deliver2_def, upd_lchan_def, update_client_def] >>
      simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[qof_def] >>
      rpt conj_tac
      >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[])
      >- (rpt strip_tac >> res_tac >> fs[EL_LUPDATE] >> every_case_tac >> gvs[])
      >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[])
      >> (rpt strip_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[] >> metis_tac[]))
  >- ((* LEof *)
      rename1 ‘LEof j’ >>
      ‘arrival_ok2 s (Eof2 j)’ by (first_x_assum irule >> simp[]) >>
      pop_assum (strip_assume_tac o SIMP_RULE std_ss [arrival_ok2_def]) >>
      ‘j < LENGTH w.chans’ by simp[] >>
      ‘wch (EL j w.chans) (EL j s.clients) ∧ dch (D j) (E j) (EL j w.chans)’ by simp[] >>
      ‘¬(EL j w.chans).broken ∧ ¬(EL j w.chans).connecting’ by gvs[wch_def] >>
      drule_all ch_eof >> strip_tac >>
      simp[l0_deliver_def, deliver2_def, upd_lchan_def, update_client_def] >>
      simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[qof_def] >>
      rpt conj_tac
      >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[])
      >- (rpt strip_tac >> res_tac >> fs[EL_LUPDATE] >> every_case_tac >> gvs[])
      >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[])
      >> (rpt strip_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[] >> metis_tac[]))
  >- ((* LBreak: excluded *) fs[])
  >- ((* LDrain *)
      rename1 ‘LDrain j k’ >>
      simp[l0_deliver_def] >> IF_CASES_TAC
      >- (simp[upd_lchan_def] >> simp_tac std_ss [sinv_def, wk_def, lk_def] >>
          simp[qof_def] >> rpt conj_tac
          >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[] >>
              metis_tac[ch_drain])
          >- (rpt strip_tac >> res_tac >> fs[EL_LUPDATE] >> every_case_tac >> gvs[])
          >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[] >>
              metis_tac[ch_drain])
          >> (rpt strip_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[] >> metis_tac[]))
      >> simp_tac std_ss [sinv_def, wk_def, lk_def] >> metis_tac[])
  >- ((* LConnUp *)
      rename1 ‘LConnUp j’ >> simp[l0_deliver_def] >>
      ‘j < LENGTH w.chans ⇒ ¬(EL j w.chans).connecting’ by (strip_tac >> gvs[wch_def]) >>
      simp_tac std_ss [sinv_def, wk_def, lk_def] >> rw[] >> metis_tac[])
  >> (* LConnFail *)
  rename1 ‘LConnFail j e’ >> simp[l0_deliver_def] >>
  ‘j < LENGTH w.chans ⇒ ¬(EL j w.chans).connecting’ by (strip_tac >> gvs[wch_def]) >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> rw[] >> metis_tac[]
QED

Theorem sinv_FOLDL_deliver:
  ∀l s w. sinv lfd p a cm D E s w ∧ step_ok2 s (FLAT (MAP (conv_arr p lfd) l)) ∧
          (∀j e k. ¬MEM (LBreak j e k) l) ⇒
          sinv lfd p a cm D E (FOLDL deliver2 s (FLAT (MAP (conv_arr p lfd) l)))
               (FOLDL l0_deliver w l)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  fs[step_ok2_append, FOLDL_APPEND] >> first_x_assum irule >> simp[] >>
  irule sinv_deliver >> rpt conj_tac
  >- (rpt strip_tac >> fs[step_ok2_def])
  >- metis_tac[]
  >> simp[]
QED

Theorem deliver_open_fds[simp]:
  (l0_deliver w a).open_fds = w.open_fds
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_open_fds[simp]:
  ∀as w. (FOLDL l0_deliver w as).open_fds = w.open_fds
Proof
  Induct >> simp[]
QED

Theorem ticks_open_fds[simp]:
  ∀k w. (l0_tick nm w).open_fds = w.open_fds ∧ (l0_ticks nm k w).open_fds = w.open_fds
Proof
  Induct >> simp[l0_ticks_def, l0_tick_def]
QED

(* ========================================================================
   C. One call
   ======================================================================== *)

(* The invariant at a world reached from w1: the kernel's world is the one
   after the polls made since w1 *)
Definition kinv_def:
  kinv p lfd sched w1 a cm D E w ⇔
    simple_v2 p lfd sched w ∧ (∀h. ¬w.ch.emfile_drops h) ∧
    npolls w1.hist ≤ npolls w.hist ∧
    sinv lfd p a cm D E (kworld p lfd sched w1 (npolls w.hist − npolls w1.hist)) w
End

Theorem npolls_snoc:
  npolls (h ++ [(n, c, b)]) = npolls h + (if n = «sys_poll» then 1 else 0)
Proof
  rw[npolls_def, FILTER_APPEND]
QED

(* The step of time before a call *)
Theorem sinv_tick:
  simple_v2 p lfd sched w ∧ npolls w1.hist ≤ npolls w.hist ∧
  sched_wf2 (sk_of p lfd sched w1) ∧
  sinv lfd p a cm D E (kworld p lfd sched w1 (npolls w.hist − npolls w1.hist)) w ⇒
  sinv lfd p a cm D E
       (kworld p lfd sched w1 (npolls w.hist − npolls w1.hist +
                                (if nm = «sys_poll» then 1 else 0)))
       (l0_tick nm w)
Proof
  strip_tac >> reverse (Cases_on ‘nm = «sys_poll»’)
  >- (drule_all tick_simple_v2 >> simp[]) >>
  simp[GSYM ADD1, kworld_SUC] >>
  ‘kernel_steps p lfd sched w1 (npolls w.hist − npolls w1.hist) =
   FLAT (MAP (conv_arr p lfd) (w.env w.clock w.hist «sys_poll»))’
    by gvs[kernel_steps_def, simple_v2_def, conv_step_def] >>
  simp[l0_tick_def] >> irule sinv_FOLDL_deliver >> simp[step_ok2_with] >>
  rpt conj_tac >>
  TRY (fs[simple_v2_def, simple0_def, env_simple_def] >> NO_TAC) >>
  qpat_x_assum ‘kernel_steps _ _ _ _ _ = _’ (SUBST1_TAC o SYM) >>
  metis_tac[kworld_step_ok]
QED

Theorem call_poll_same:
  l0_call «sys_poll» conf bytes w = SOME (FFIreturn out w') ∧ conf ≠ [] ∧ HD conf = 0w ⇒
  w' = w
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()]
QED

(* A change to one channel that keeps wch and dch keeps the invariant *)
Theorem sinv_upd:
  sinv lfd p a cm D E s w ∧
  (∀v. wch (EL j w.chans) v ∧ dch (D j) (E j) (EL j w.chans) ⇒
       wch (g (EL j w.chans)) v ∧ dch (D j) (E j) (g (EL j w.chans))) ∧
  ((g (EL j w.chans)).closed ⇒ (EL j w.chans).closed ∨ ∀f. ALOOKUP w.open_fds f ≠ SOME j) ∧
  ((EL j w.chans).closed ⇒ (g (EL j w.chans)).closed) ⇒
  sinv lfd p a cm D E s (upd_lchan j g w)
Proof
  rpt strip_tac >> qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[upd_lchan_def, qof_def] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (res_tac >> NO_TAC) >>
  TRY (gvs[qof_def] >> NO_TAC) >>
  TRY (Cases_on ‘c = j’
       >- (pop_assum SUBST_ALL_TAC >> simp[EL_LUPDATE] >>
           ‘j < LENGTH w.chans’ by fs[] >>
           first_x_assum (qspec_then ‘EL j s.clients’ mp_tac) >> simp[]) >>
       simp[EL_LUPDATE] >> NO_TAC) >>
  TRY (qpat_x_assum ‘_.closed’ mp_tac >> simp[EL_LUPDATE] >> rw[] >> res_tac >> fs[] >>
       metis_tac[] >> NO_TAC) >>
  simp[EL_LUPDATE] >> rw[] >> metis_tac[]
QED


Theorem sinv_send:
  sinv lfd p a cm D E s w ∧ l0_send f bs w = (r, w') ⇒ sinv lfd p a cm D E s w'
Proof
  simp[l0_send_def] >> every_case_tac >> rw[] >> simp[] >>
  irule sinv_upd >> simp[wch_def, dch_def] >> metis_tac[]
QED

Theorem ALOOKUP_ADELKEY_SOME:
  ALOOKUP (ADELKEY f l) g = SOME c ⇒ ALOOKUP l g = SOME c
Proof
  simp[ALOOKUP_ADELKEY] >> rw[]
QED

Theorem ch_close:
  wch a v ∧ dch d e a ∧ e ⇒
  wch (a with <| shut := T; closed := T; aborted := x |>) v ∧
  dch d e (a with <| shut := T; closed := T; aborted := x |>)
Proof
  strip_tac >> gvs[wch_def, dch_def]
QED

Theorem sinv_reserved[simp]:
  sinv lfd p a cm D E s (w with reserved := r) ⇔ sinv lfd p a cm D E s w
Proof
  simp[sinv_def, wk_def, lk_def, qof_def]
QED

Theorem sinv_close_fd:
  sinv lfd p a cm D E s w ∧ f ≠ lfd ∧ (∀c. ALOOKUP w.open_fds f = SOME c ⇒ E c) ⇒
  sinv lfd p a cm D E s (close_fd f w)
Proof
  strip_tac >>
  ‘FILTER (λ(l,p,q). l = f) w.listeners = []’ by fs[sinv_def, wk_def] >>
  simp[close_fd_def] >> Cases_on ‘l0_chan_of w f’ >> fs[] >>
  TRY (qpat_x_assum ‘l0_chan_of _ _ = NONE’ kall_tac >> metis_tac[sinv_reserved] >> NO_TAC) >>
  rename1 ‘l0_chan_of w f = SOME x’ >>
  ‘ALOOKUP w.open_fds f = SOME x ∧ x < LENGTH w.chans’ by fs[l0_chan_of_def, AllCaseEqs()] >>
  ‘E x’ by res_tac >>
  qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[upd_lchan_def, qof_def] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[ALOOKUP_ADELKEY, AllCaseEqs()] >>
  TRY (res_tac >> fs[] >> NO_TAC) >>
  TRY (Cases_on ‘c = x’
       >- (pop_assum SUBST_ALL_TAC >> simp[EL_LUPDATE] >>
           ‘wch (EL x w.chans) (EL x s.clients) ∧ dch (D x) (E x) (EL x w.chans)’ by fs[] >>
           drule_all ch_close >> simp[]) >>
       simp[EL_LUPDATE] >> NO_TAC) >>
  TRY (qpat_x_assum ‘_.closed’ mp_tac >> simp[EL_LUPDATE] >> rw[] >> res_tac >> fs[] >>
       metis_tac[] >> NO_TAC) >>
  simp[EL_LUPDATE] >> rw[] >> metis_tac[SOME_11]
QED

Theorem sinv_close:
  sinv lfd p a cm D E s w ∧ f ≠ lfd ∧ (∀c. ALOOKUP w.open_fds f = SOME c ⇒ E c) ∧
  l0_close f w = (r, w') ⇒ sinv lfd p a cm D E s w'
Proof
  simp[l0_close_def] >> strip_tac >> every_case_tac >> gvs[] >>
  metis_tac[sinv_close_fd]
QED

Theorem call_send:
  sinv lfd p a cm D E s w ∧ l0_call «sys_send» conf bytes w = SOME (FFIreturn out w') ⇒
  sinv lfd p a cm D E s w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  metis_tac[sinv_send]
QED

Theorem call_close:
  sinv lfd p a cm D E s w ∧ bytes_fd conf ≠ lfd ∧
  (∀c. ALOOKUP w.open_fds (bytes_fd conf) = SOME c ⇒ E c) ∧
  l0_call «sys_close» conf bytes w = SOME (FFIreturn out w') ⇒
  sinv lfd p a cm D E s w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  metis_tac[sinv_close]
QED

(* The quiet steps: polls, sends and closes of fds other than the listener
   keep the invariant *)
(* The quiet calls: non-blocking polls, sends, closes of fds other than
   the listener *)
Definition quiet_call_def:
  quiet_call lfd E (w : l0world) n (conf : word8 list) ⇔
    (n = «sys_poll» ∧ conf ≠ [] ∧ HD conf = 0w) ∨ n = «sys_send» ∨
    (n = «sys_close» ∧ bytes_fd conf ≠ lfd ∧
     ∀c. ALOOKUP w.open_fds (bytes_fd conf) = SOME c ⇒ E c)
End

Theorem kinv_do_quiet:
  kinv p lfd sched w1 a cm D E w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  l0_do n conf alen w = SOME (out, w', ev) ∧ quiet_call lfd E w n conf ⇒
  kinv p lfd sched w1 a cm D E w'
Proof
  strip_tac >> drule l0_do_env >> strip_tac >>
  drule l0_do_cases >> strip_tac >>
  qpat_x_assum ‘w' = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘kinv _ _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [kinv_def]) >>
  drule_all sinv_tick >> disch_then (qspec_then ‘n’ assume_tac) >>
  simp_tac std_ss [kinv_def] >> rpt conj_tac
  >- (‘simple_v2 p lfd sched (w1' with hist := w.hist ++ [(n,conf,REPLICATE alen 0w)]) ⇔
       simple_v2 p lfd sched w’ by (irule simple_v2_same >> simp[]) >>
      simp[])
  >- fs[]
  >- (rw[npolls_snoc] >> fs[])
  >> simp[npolls_snoc] >>
  ‘npolls w.hist + (if n = «sys_poll» then 1 else 0) − npolls w1.hist =
   npolls w.hist − npolls w1.hist + (if n = «sys_poll» then 1 else 0)’ by (rw[] >> fs[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum ‘quiet_call _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [quiet_call_def]) >> gvs[]
  >- (drule_all call_poll_same >> strip_tac >> gvs[])
  >- (drule_all call_send >> simp[])
  >> ‘∀c. ALOOKUP (l0_tick «sys_close» w).open_fds (bytes_fd conf) = SOME c ⇒ E c’
       by fs[] >>
  drule_all call_close >> simp[]
QED

Theorem kinv_sys_quiet:
  kinv p lfd sched w1 a cm D E w ∧ sched_wf2 (sk_of p lfd sched w1) ⇒
  (sys_poll fes w = SOME (out, w', ev) ⇒ kinv p lfd sched w1 a cm D E w') ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ kinv p lfd sched w1 a cm D E w') ∧
  (f ≠ lfd ∧ (∀c. ALOOKUP w.open_fds f = SOME c ⇒ E c) ∧ sys_close f w = SOME (out, w', ev) ⇒
   kinv p lfd sched w1 a cm D E w')
Proof
  rw[sys_poll_def, sys_send_def, sys_close_def] >>
  drule_at (Pos (el 3)) kinv_do_quiet >> simp[poll_conf_def, quiet_call_def]
QED

(* ========================================================================
   D. The fetch: accepts and recvs
   ======================================================================== *)

(* A change to one channel that L1 fetched from, with its new fetched data *)
Theorem sinv_upd_D:
  sinv lfd p a cm D E s w ∧ c < a ∧
  (∀v. wch (EL c w.chans) v ⇒ wch (g (EL c w.chans)) v) ∧ dch x (E c) (g (EL c w.chans)) ∧
  ((g (EL c w.chans)).closed ⇔ (EL c w.chans).closed) ⇒
  sinv lfd p a cm ((c =+ x) D) E s (upd_lchan c g w)
Proof
  rpt strip_tac >> qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[upd_lchan_def, qof_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC
      >- (gvs[] >> qpat_x_assum ‘∀v. wch _ v ⇒ _’ irule >> fs[])
      >> fs[])
  >- (rpt strip_tac >> res_tac >> fs[EL_LUPDATE] >> every_case_tac >> gvs[])
  >- (rpt strip_tac >> simp[EL_LUPDATE, APPLY_UPDATE_THM] >> IF_CASES_TAC >> gvs[])
  >> (rpt strip_tac >> simp[APPLY_UPDATE_THM, EL_LUPDATE] >> rw[] >> gvs[] >> metis_tac[])
QED

(* The peer's EOF fetched *)
Theorem sinv_E:
  sinv lfd p a cm D E s w ∧ c < LENGTH w.chans ∧ c < a ∧ (EL c w.chans).peer_eof ∧
  (EL c w.chans).inbox = [] ⇒
  sinv lfd p a cm D ((c =+ T) E) s w
Proof
  rpt strip_tac >> qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[APPLY_UPDATE_THM] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (res_tac >> NO_TAC) >>
  TRY (Cases_on ‘c = c'’
       >- (gvs[] >> ‘dch (D c) (E c) (EL c w.chans)’ by fs[] >> fs[dch_def])
       >> fs[] >> NO_TAC) >>
  fs[]
QED

Theorem GENLIST_plus_CONS:
  a < n ⇒ GENLIST (λi. a + i) (n − a) = a :: GENLIST (λi. a + 1 + i) (n − (a + 1))
Proof
  strip_tac >> ‘n − a = SUC (n − (a + 1))’ by simp[] >>
  pop_assum SUBST1_TAC >> rewrite_tac[GENLIST_CONS] >>
  simp[combinTheory.o_DEF] >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

(* An accept on the listener: nothing changes, or the next queued channel
   (number a) is opened on a fresh fd *)
Theorem used_open_fds:
  ALOOKUP w.open_fds g = SOME c ⇒ MEM g (l0_used w)
Proof
  rw[l0_used_def] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[FST]
QED

Theorem sinv_accept:
  sinv lfd p a cm D E s w ∧ (∀h. w.ch.transient h = NONE) ∧
  (∀h. ¬w.ch.emfile_drops h) ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧
  l0_accept lfd w = (r, w') ⇒
  (sinv lfd p a cm D E s w' ∧ (∀k. r ≠ Ok k) ∧ w'.open_fds = w.open_fds) ∨
  (∃f. r = Ok (w2n f) ∧ ¬MEM f (l0_used w) ∧ w'.open_fds = (f, a) :: w.open_fds ∧
       sinv lfd p (a + 1) ((f, a) :: cm) D E s w')
Proof
  strip_tac >>
  qpat_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  ‘q = GENLIST (λi. a + i) (LENGTH w.chans − a)’
    by (qpat_x_assum ‘qof _ _ = _’ (SUBST1_TAC o SYM) >> fs[qof_def]) >>
  qpat_x_assum ‘l0_accept _ _ = _’ mp_tac >>
  qpat_x_assum ‘(w:l0world).listeners = _’ (fn th => simp[l0_accept_def, th]) >>
  reverse (Cases_on ‘a < LENGTH w.chans’)
  >- (‘LENGTH s.clients − a = 0’ by fs[] >>
      pop_assum (fn th => simp[th, fail_def]) >> strip_tac >> gvs[]) >>
  ‘GENLIST (λi. a + i) (LENGTH w.chans − a) =
   a :: GENLIST (λi. a + 1 + i) (LENGTH w.chans − (a + 1))’ by simp[GENLIST_plus_CONS] >>
  simp[] >>
  ‘¬(EL a w.chans).broken’ by (‘wch (EL a w.chans) (EL a s.clients)’ by fs[] >> fs[wch_def]) >>
  simp[l0_alloc_def] >> IF_CASES_TAC >> simp[fail_def]
  >- (strip_tac >> gvs[] >>
      conj_tac >- (irule lowest_fd_fresh >> simp[]) >>
      simp_tac std_ss [sinv_def, wk_def, lk_def] >>
      ‘¬(EL a w.chans).closed’
        by (‘dch (D a) (E a) (EL a w.chans) ∧ ¬E a’ by fs[] >> fs[dch_def]) >>
      ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_fresh >> simp[]) >>
      ‘lowest_fd w ≠ lfd’ by (strip_tac >> gvs[sinv_def, wk_def, l0_used_def]) >>
      simp[AFUPDKEY_def, qof_def] >> rpt conj_tac >> rpt strip_tac >>
      TRY (Cases_on ‘c = a’ >- (disj2_tac >> qexists_tac ‘lowest_fd w’ >> simp[]) >>
           ‘c < a’ by simp[] >>
           ‘(EL c w.chans).closed ∨ ∃f. ALOOKUP w.open_fds f = SOME c’ by fs[] >> fs[] >>
           disj2_tac >> qexists_tac ‘f’ >> rw[] >> metis_tac[used_open_fds] >> NO_TAC) >>
      TRY (Cases_on ‘f = lowest_fd w’ >> gvs[] >> res_tac >> simp[] >> NO_TAC) >>
      TRY (Cases_on ‘f = lowest_fd w’ >> Cases_on ‘g = lowest_fd w’ >> gvs[] >>
           res_tac >> fs[] >> NO_TAC) >>
      fs[])
  >> strip_tac >> gvs[] >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[qof_def]
QED

Theorem ch_recv:
  dch d e a ∧ a.inbox ≠ [] ⇒ dch (d ++ TAKE k a.inbox) e (a with inbox := DROP k a.inbox)
Proof
  rw[dch_def] >> gvs[] >> metis_tac[TAKE_DROP, APPEND_ASSOC]
QED

(* A recv on an open fd of channel c: EOF, a retried failure, or data, which
   L1's fetched data for c gains *)
Theorem sinv_recv:
  sinv lfd p a cm D E s w ∧ (∀h. w.ch.transient h = NONE) ∧ (∀j h x. w.ch.short j h x = x) ∧
  ALOOKUP w.open_fds g = SOME c ∧ 0 < n ∧ l0_recv g n w = (r, d, w') ⇒
  (r = Ok 0 ∧ d = [] ∧ w' = w ∧ c < LENGTH w.chans ∧ c < a ∧ (EL c w.chans).peer_eof ∧
   (EL c w.chans).inbox = []) ∨
  (∃e x. r = Fail e x ∧ l1_transient e ∧ d = [] ∧ w' = w) ∨
  (∃k. r = Ok k ∧ 0 < k ∧ LENGTH d = k ∧ w'.open_fds = w.open_fds ∧
       sinv lfd p a cm ((c =+ D c ++ d) D) E s w')
Proof
  strip_tac >>
  qpat_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  ‘ALOOKUP cm g = SOME c ∧ c < a’ by metis_tac[] >>
  ‘c < LENGTH w.chans’ by simp[] >>
  ‘l0_chan_of w g = SOME c’ by simp[l0_chan_of_def] >>
  ‘wch (EL c w.chans) (EL c s.clients) ∧ dch (D c) (E c) (EL c w.chans)’ by fs[] >>
  ‘¬(EL c w.chans).connecting ∧ ¬(EL c w.chans).broken ∧ (EL c w.chans).err = NONE’
    by fs[wch_def] >>
  qpat_x_assum ‘l0_recv _ _ _ = _’ mp_tac >> simp[l0_recv_def] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[] >> conj_tac
      >- (Cases_on ‘(EL c w.chans).inbox’ >> gvs[])
      >> TRY (conj_tac >- simp[upd_lchan_def])
      >> irule sinv_upd_D >> simp[] >> rpt conj_tac >>
      TRY (simp[wch_def] >> NO_TAC) >> irule ch_recv >> fs[])
  >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[fail_def, l1_transient_def]
QED

Theorem kinv_sys_close:
  kinv p lfd sched w1 a cm D E w ∧ sched_wf2 (sk_of p lfd sched w1) ∧ f ≠ lfd ∧
  (∀c. ALOOKUP w.open_fds f = SOME c ⇒ E c) ∧ sys_close f w = SOME (out, w', ev) ⇒
  kinv p lfd sched w1 a cm D E w'
Proof
  rw[sys_close_def] >> drule_at (Pos (el 3)) kinv_do_quiet >> simp[quiet_call_def]
QED

(* The invariant's world facts at the world with the clock advanced *)
Theorem kinv_tick_clock:
  kinv p lfd sched w1 a cm D E w ∧ nm ≠ «sys_poll» ⇒
  l0_tick nm w = w with clock := w.clock + 1 ∧
  sinv lfd p a cm D E (kworld p lfd sched w1 (npolls w.hist − npolls w1.hist))
       (w with clock := w.clock + 1) ∧
  (∀h. w.ch.transient h = NONE) ∧ (∀j h x. w.ch.short j h x = x) ∧
  (∀h. ¬w.ch.emfile_drops h)
Proof
  simp_tac std_ss [kinv_def] >> strip_tac >>
  ‘l0_tick nm w = w with clock := w.clock + 1’ by metis_tac[tick_simple_v2] >>
  simp[] >> fs[simple_v2_def, simple0_def]
QED

Theorem kinv_after:
  kinv p lfd sched w1 a cm D E w ∧ w1'.ch = w.ch ∧ w1'.env = w.env ∧
  w1'.fd_limit = w.fd_limit ∧ n ≠ «sys_poll» ∧
  sinv lfd p a' cm' D' E' (kworld p lfd sched w1 (npolls w.hist − npolls w1.hist)) w1' ⇒
  kinv p lfd sched w1 a' cm' D' E' (w1' with hist := w.hist ++ [(n, conf, b)])
Proof
  strip_tac >>
  ‘simple_v2 p lfd sched (w1' with hist := w.hist ++ [(n, conf, b)]) ⇔
   simple_v2 p lfd sched w’ by (irule simple_v2_same >> simp[]) >>
  fs[kinv_def, npolls_snoc]
QED

(* A call that changed nothing but time and the history *)
Theorem kinv_clock_hist:
  kinv p lfd sched w1 a cm D E w ∧ n ≠ «sys_poll» ⇒
  kinv p lfd sched w1 a cm D E (w with <| clock := k; hist := w.hist ++ [(n, conf, b)] |>)
Proof
  strip_tac >>
  ‘simple_v2 p lfd sched (w with <| clock := k; hist := w.hist ++ [(n, conf, b)] |>) ⇔
   simple_v2 p lfd sched w’ by (irule simple_v2_same >> simp[]) >>
  fs[kinv_def, npolls_snoc]
QED

(* L1's accept on the listener *)
Theorem kinv_sys_accept:
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sys_accept lfd w = SOME (out, w', ev) ⇒
  (kinv p lfd sched w1 a cm D E w' ∧ (∀k. l0_res_of out ≠ Ok k) ∧
   w'.open_fds = w.open_fds) ∨
  (∃k. l0_res_of out = Ok k ∧ ¬MEM (n2w k : word64) (l0_used w) ∧
       w'.open_fds = (n2w k, a) :: w.open_fds ∧
       kinv p lfd sched w1 (a + 1) ((n2w k, a) :: cm) D E w')
Proof
  rw[sys_accept_def] >> drule l0_do_env >> strip_tac >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  drule_then (qspec_then ‘«sys_accept»’ mp_tac) kinv_tick_clock >> simp[] >> strip_tac >>
  gvs[] >> drule qof_call_accept >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_rely (w with clock := w.clock + 1)’
    by (fs[winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_all l0_accept_res >> strip_tac >>
  ‘l0_res_of (enc_res r) = r’ by (irule l0_res_of_enc >> simp[]) >>
  ‘fds_lt (w with clock := w.clock + 1) ∧ (w with clock := w.clock + 1).fd_limit ≤ 2 ** 31’
    by (fs[winv_def] >> fs[l0_rely_def] >> fs[fds_lt_def, l0_used_def] >>
        first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [‘w’ |-> ‘w with clock := w.clock + 1’, ‘w'’ |-> ‘w1'’,
                  ‘s’ |-> ‘kworld p lfd sched w1 (npolls w.hist − npolls w1.hist)’]
                 sinv_accept) >>
  impl_tac >- simp[] >> strip_tac >> gvs[]
  >- (TRY disj1_tac >> irule kinv_after >> simp[] >> metis_tac[])
  >> TRY disj2_tac >> fs[l0_used_def] >> irule kinv_after >> simp[] >> metis_tac[]
QED

(* L1's recv on an open fd of channel c *)
Theorem kinv_sys_recv:
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ ALOOKUP w.open_fds g = SOME c ∧
  sys_recv g pf_chunk w = SOME (out, w', ev) ⇒
  w'.open_fds = w.open_fds ∧
  ((l0_res_of out = Ok 0 ∧ c < a ∧ c < LENGTH w'.chans ∧ (EL c w'.chans).peer_eof ∧
    (EL c w'.chans).inbox = [] ∧
    kinv p lfd sched w1 a cm D E w') ∨
   (∃e x. l0_res_of out = Fail e x ∧ l1_transient e ∧ kinv p lfd sched w1 a cm D E w') ∨
   (∃k. l0_res_of out = Ok k ∧ 0 < k ∧ TAKE k (DROP 13 out) ≠ [] ∧
        kinv p lfd sched w1 a cm ((c =+ D c ++ TAKE k (DROP 13 out)) D) E w'))
Proof
  rw[sys_recv_def] >> drule l0_do_env >> strip_tac >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  drule_then (qspec_then ‘«sys_recv»’ mp_tac) kinv_tick_clock >> simp[] >> strip_tac >>
  gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def, l0_hdr_def, fd_ok_def] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >>
  ‘l0_rely (w with clock := w.clock + 1)’
    by (fs[winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘pf_chunk < 256 ** 8’ by simp[pf_chunk_def] >>
  ‘l0_res_ok r’ by metis_tac[recv_res_ok] >>
  ‘∀rest. l0_res_of (enc_res r ++ rest) = r’
    by (rpt strip_tac >> irule l0_res_of_enc_app >> simp[]) >>
  ‘∀rest. TAKE (LENGTH d) (DROP 13 (enc_res r ++ (d ++ rest))) = d’
    by (rpt strip_tac >> drule LENGTH_enc_res >> strip_tac >>
        ‘DROP 13 (enc_res r ++ d ++ rest) = d ++ rest’
          by (rewrite_tac[GSYM APPEND_ASSOC] >> metis_tac[DROP_LENGTH_APPEND]) >>
        simp[TAKE_LENGTH_APPEND]) >>
  ‘0 < pf_chunk’ by simp[pf_chunk_def] >>
  mp_tac (Q.INST [‘w’ |-> ‘w with clock := w.clock + 1’, ‘n’ |-> ‘pf_chunk’,
                  ‘s’ |-> ‘kworld p lfd sched w1 (npolls w.hist − npolls w1.hist)’]
                 sinv_recv) >>
  impl_tac >- simp[] >> strip_tac >> gvs[]
  >- (TRY disj1_tac >> irule kinv_clock_hist >> simp[])
  >- (TRY disj1_tac >> irule kinv_clock_hist >> simp[])
  >> qpat_x_assum ‘∀rest. l0_res_of _ = _’
       (qspec_then ‘d ++ REPLICATE (pf_chunk − LENGTH d) 0w’ assume_tac) >>
  qpat_x_assum ‘∀rest. TAKE _ _ = _’
       (qspec_then ‘REPLICATE (pf_chunk − LENGTH d) 0w’ assume_tac) >>
  fs[APPEND_ASSOC] >> disj2_tac >> conj_tac >- (Cases_on ‘d’ >> fs[]) >>
  irule kinv_after >> simp[] >> metis_tac[]
QED

(* The fds L1 has seen the end of (its EOF list and the closing fds) are
   channels whose EOF was fetched: L1 closes only those *)
Definition eown_def:
  eown (E : num -> bool) (ps : l1p) (w : l0world) ⇔
    ∀f c. (MEM f ps.eof ∨ MEM f ps.b.closing) ∧ ALOOKUP w.open_fds f = SOME c ⇒ E c
End

(* ... and they are in use (so an accept never returns one of them) *)
Definition eused_def:
  eused (ps : l1p) (w : l0world) ⇔
    ∀f. MEM f ps.eof ∨ MEM f ps.b.closing ⇒ MEM f (l0_used w)
End

Theorem kinv_E:
  kinv p lfd sched w1 a cm D E w ∧ c < LENGTH w.chans ∧ c < a ∧ (EL c w.chans).peer_eof ∧
  (EL c w.chans).inbox = [] ⇒
  kinv p lfd sched w1 a cm D ((c =+ T) E) w
Proof
  rw[kinv_def] >> irule sinv_E >> simp[]
QED

Theorem kinv_cl:
  kinv p lfd sched w1 a cm D E w ∧ ALOOKUP w.open_fds g = SOME c ⇒
  ALOOKUP cm g = SOME c ∧ cl cm g = c ∧ c < a
Proof
  rw[kinv_def, sinv_def, lk_def] >> res_tac >> simp[cl_def]
QED


(* The fetch, against the client numbering: the fetched data and EOFs are
   psk's arrivals of the round *)
Theorem kinv_fetch:
  ∀fs w ps w' ps' log evs a cm D E.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧ eown E ps w ∧ eused ps w ∧
    (∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP w.open_fds g = SOME c) ⇒
    ∃as cm' a'.
      arrs lfd (cm, a) log = (as, (cm', a')) ∧
      kinv p lfd sched w1 a' cm' (λj. D j ++ data_of j as) (λj. E j ∨ MEM (Eof2 j) as) w' ∧
      winv w' ∧ eown (λj. E j ∨ MEM (Eof2 j) as) ps' w' ∧
      (∀g c. ALOOKUP w.open_fds g = SOME c ⇒ ALOOKUP w'.open_fds g = SOME c)
Proof
  Induct
  >- (simp[pf_fetch_def] >> rpt strip_tac >> gvs[arrs_def, data_of_def] >>
      ‘(λj. E j) = E’ by simp[FUN_EQ_THM] >> simp[ETA_THM]) >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> simp[Once pf_fetch_def] >>
  reverse (Cases_on ‘wants_input lfd hw ps g’) >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      disch_then (qspecl_then [‘a’, ‘cm’, ‘D’, ‘E’] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  IF_CASES_TAC
  >- ((* an accept *)
      pop_assum SUBST_ALL_TAC >> strip_tac >>
      qpat_x_assum ‘option_CASE (sys_accept _ _) _ _ = _’ mp_tac >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, wa, ev)’ >>
      pairarg_tac >> simp[] >>
      Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
      rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
      strip_tac >> rveq >>
      drule_all (el 4 (CONJUNCTS sys_winv)) >> strip_tac >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used wa)’
        by (qpat_x_assum ‘sys_accept _ _ = _’ mp_tac >> simp[sys_accept_def] >>
            strip_tac >> drule l0_do_used >> simp[]) >>
      drule_all kinv_sys_accept >> strip_tac
      >- ((* failed: nothing logged *)
          ‘fl' = [] ∧ ps1.eof = ps.eof ∧ ps1.b = ps.b’
            by (Cases_on ‘l0_res_of out’ >> fs[] >> rw[] >> fs[]) >> rveq >>
          ‘eown E ps1 wa ∧ eused ps1 wa’ by (fs[eown_def, eused_def] >> metis_tac[]) >>
          first_x_assum (qspecl_then [‘wa’, ‘ps1’, ‘w'’, ‘ps'’, ‘y2’, ‘y3’, ‘a’, ‘cm’, ‘D’, ‘E’]
                          mp_tac) >>
          impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >> simp[] >> metis_tac[])
      >> (* a new connection *)
      ‘fl' = [FConn (n2w k)] ∧ ps1.eof = ps.eof ∧ ps1.b = ps.b’ by (fs[] >> rw[]) >>
      rveq >>
      ‘eown E ps1 wa ∧ eused ps1 wa’
        by (fs[eown_def, eused_def] >> rpt strip_tac >> gvs[] >> res_tac >>
            TRY (‘f ≠ n2w k’ by (strip_tac >> gvs[])) >> gvs[]) >>
      first_x_assum (qspecl_then [‘wa’, ‘ps1’, ‘w'’, ‘ps'’, ‘y2’, ‘y3’, ‘a + 1’,
                                  ‘(n2w k, a) :: cm’, ‘D’, ‘E’] mp_tac) >>
      impl_tac
      >- (simp[] >> rpt strip_tac >>
          ‘∃c. ALOOKUP w.open_fds g = SOME c’ by metis_tac[] >>
          qexists_tac ‘c’ >> simp[] >> rw[] >> metis_tac[used_open_fds]) >>
      strip_tac >> simp[arrs_def] >>
      ‘(λj. D j ++ data_of j (Connect2 lfd :: as)) = (λj. D j ++ data_of j as) ∧
       (λj. E j ∨ MEM (Eof2 j) (Connect2 lfd :: as)) = (λj. E j ∨ MEM (Eof2 j) as)’
        by simp[FUN_EQ_THM, data_of_def] >>
      asm_rewrite_tac[] >>
      rpt strip_tac >> first_x_assum irule >> simp[] >> rw[] >> metis_tac[used_open_fds])
  >> (* a recv *)
  strip_tac >>
  qpat_x_assum ‘option_CASE (sys_recv _ _ _) _ _ = _’ mp_tac >>
  Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME (out, wa, ev)’ >>
  pairarg_tac >> simp[] >>
  Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
  rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
  strip_tac >> rveq >>
  drule_all (el 3 (CONJUNCTS sys_winv)) >> strip_tac >>
  ‘∃c. ALOOKUP w.open_fds g = SOME c’ by metis_tac[] >>
  drule_all kinv_cl >> strip_tac >>
  ‘l0_used wa = l0_used w’
    by (qpat_x_assum ‘sys_recv _ _ _ = _’ mp_tac >> simp[sys_recv_def] >>
        strip_tac >> drule l0_do_used >> simp[]) >>
  drule_all kinv_sys_recv >> strip_tac
  >- ((* EOF *)
      ‘fl' = [FEof g] ∧ ps1 = ps with eof := g :: ps.eof’ by fs[] >> rveq >>
      ‘kinv p lfd sched w1 a cm D ((cl cm g =+ T) E) wa’ by (irule kinv_E >> fs[]) >>
      ‘eown ((cl cm g =+ T) E) (ps with eof := g :: ps.eof) wa ∧
       eused (ps with eof := g :: ps.eof) wa’
        by (fs[eown_def, eused_def, APPLY_UPDATE_THM] >> rpt strip_tac >> gvs[] >>
            TRY (metis_tac[used_open_fds]) >> rw[] >> metis_tac[]) >>
      first_x_assum (qspecl_then [‘wa’, ‘ps with eof := g :: ps.eof’, ‘w'’, ‘ps'’, ‘y2’, ‘y3’,
                                  ‘a’, ‘cm’, ‘D’, ‘(cl cm g =+ T) E’] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
      simp[arrs_def] >>
      ‘(λj. D j ++ data_of j (Eof2 (cl cm g) :: as)) = (λj. D j ++ data_of j as) ∧
       (λj. E j ∨ j = cl cm g ∨ MEM (Eof2 j) as) =
       (λj. (cl cm g =+ T) E j ∨ MEM (Eof2 j) as)’
        by (simp[FUN_EQ_THM, APPLY_UPDATE_THM, data_of_def] >> rw[] >> metis_tac[]) >>
      asm_rewrite_tac[] >> metis_tac[])
  >- ((* a retried failure *)
      ‘fl' = [] ∧ ps1 = ps’ by (Cases_on ‘l0_res_of out’ >> fs[]) >> rveq >>
      ‘eown E ps wa ∧ eused ps wa’ by (fs[eown_def, eused_def] >> metis_tac[]) >>
      first_x_assum (qspecl_then [‘wa’, ‘ps’, ‘w'’, ‘ps'’, ‘y2’, ‘y3’, ‘a’, ‘cm’, ‘D’, ‘E’]
                      mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >> simp[] >> metis_tac[])
  >> (* data *)
  ‘fl' = [FData g (TAKE k (DROP 13 out))] ∧ ps1.eof = ps.eof ∧ ps1.b = ps.b’
    by (fs[] >> rw[]) >> rveq >>
  ‘eown E ps1 wa ∧ eused ps1 wa’ by (fs[eown_def, eused_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [‘wa’, ‘ps1’, ‘w'’, ‘ps'’, ‘y2’, ‘y3’, ‘a’, ‘cm’,
                              ‘(cl cm g =+ D (cl cm g) ++ TAKE k (DROP 13 out)) D’, ‘E’] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  simp[arrs_def] >>
  ‘(λj. D j ++ data_of j (Data2 (cl cm g) (TAKE k (DROP 13 out)) :: as)) =
   (λj. (cl cm g =+ D (cl cm g) ++ TAKE k (DROP 13 out)) D j ++ data_of j as)’
    by (simp[FUN_EQ_THM, APPLY_UPDATE_THM, data_of_def] >> rw[]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* The fetch's accepted fds: fresh, and open (in a world that keeps open fds
   open: wmono, pf_fetch_queue) *)
Theorem pf_fetch_acq:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ⇒
    (∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w')) ∧
    ∀f. MEM f ps'.acq ⇒ MEM f ps.acq ∨ (¬MEM f (l0_used w) ∧ ∃c. ALOOKUP w'.open_fds f = SOME c)
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> simp[Once pf_fetch_def] >>
  reverse (Cases_on ‘wants_input lfd hw ps g’) >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (pop_assum SUBST_ALL_TAC >> strip_tac >>
      qpat_x_assum ‘option_CASE (sys_accept _ _) _ _ = _’ mp_tac >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, wa, ev)’ >>
      pairarg_tac >> simp[] >>
      Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
      rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
      strip_tac >> rveq >>
      drule_all (el 4 (CONJUNCTS sys_winv)) >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      drule_all pf_fetch_queue >> strip_tac >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used wa)’
        by (qpat_x_assum ‘sys_accept _ _ = _’ mp_tac >> simp[sys_accept_def] >>
            strip_tac >> drule l0_do_used >> simp[]) >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >> qpat_x_assum ‘∀f. MEM f ps'.acq ⇒ _’ drule >> strip_tac
      >- (Cases_on ‘MEM f ps.acq’ >> simp[] >>
          ‘∃k. l0_res_of out = Ok k ∧ f = n2w k’
            by (Cases_on ‘l0_res_of out’ >> fs[] >> rveq >> fs[] >>
                every_case_tac >> fs[] >> rveq >> fs[]) >>
          rveq >>
          ‘l0_rely w ∧ fds_lt w’ by fs[winv_def] >>
          conj_tac >- (drule_all sys_accept_fresh >> simp[]) >>
          drule_all sys_accept_queue >> strip_tac >> gvs[] >>
          fs[wmono_def] >> res_tac >> metis_tac[])
      >> disj2_tac >> conj_tac >- (strip_tac >> res_tac) >> simp[])
  >> strip_tac >>
  qpat_x_assum ‘option_CASE (sys_recv _ _ _) _ _ = _’ mp_tac >>
  Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME (out, wa, ev)’ >>
  pairarg_tac >> simp[] >>
  Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
  rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
  strip_tac >> rveq >>
  drule_all (el 3 (CONJUNCTS sys_winv)) >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  ‘l0_used wa = l0_used w’
    by (qpat_x_assum ‘sys_recv _ _ _ = _’ mp_tac >> simp[sys_recv_def] >>
        strip_tac >> drule l0_do_used >> simp[]) >>
  ‘ps1.acq = ps.acq’ by (every_case_tac >> fs[] >> rveq >> simp[]) >>
  fs[] >> metis_tac[]
QED

(* ========================================================================
   E. A round
   ======================================================================== *)

(* L1's handles and queued fds are open channel fds *)
Definition chown_def:
  chown (ps : l1p) (w : l0world) ⇔
    ∀f. MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.acq ⇒ ∃c. ALOOKUP w.open_fds f = SOME c
End


(* Polls and sends keep the open fds *)
Theorem sys_quiet_open:
  (sys_poll fes w = SOME (out, w', ev) ⇒ w'.open_fds = w.open_fds) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ w'.open_fds = w.open_fds)
Proof
  rw[sys_poll_def, sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  gvs[l0_call_def, AllCaseEqs()] >> TRY (pairarg_tac >> gvs[]) >>
  gvs[l0_send_def, AllCaseEqs(), upd_lchan_def]
QED

Theorem sys_close_open:
  sys_close f w = SOME (out, w', ev) ∧ ALOOKUP w.open_fds g = SOME c ∧ g ≠ f ⇒
  ALOOKUP w'.open_fds g = SOME c
Proof
  strip_tac >> drule sys_close_wkeep >> simp[wkeep_def]
QED

Theorem adelkey_snd:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l c = SOME f ∧ MEM g (MAP SND (ADELKEY c l)) ⇒
      MEM g (MAP SND l) ∧ g ≠ f
Proof
  Induct >> simp[FORALL_PROD, ADELKEY_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), MEM_MAP, MEM_FILTER, EXISTS_PROD] >> rw[] >> gvs[] >>
  TRY (metis_tac[]) >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[]
QED

(* One action of the server *)
Theorem upd_lchan_open_fds[simp]:
  (upd_lchan j g w).open_fds = w.open_fds
Proof
  simp[upd_lchan_def]
QED

Theorem FOLDL_upd_open_fds[simp]:
  ∀q w0. (FOLDL (λw j. upd_lchan j g w) w0 q).open_fds = w0.open_fds
Proof
  Induct >> simp[] >> simp[upd_lchan_def]
QED

Theorem sys_close_open_back:
  sys_close f w = SOME (out, w', ev) ∧ ALOOKUP w'.open_fds g = SOME c ⇒
  ALOOKUP w.open_fds g = SOME c
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[l0_call_def] >>
  pairarg_tac >> gvs[] >>
  gvs[l0_close_def, AllCaseEqs()] >>
  gvs[close_fd_def] >> qpat_x_assum ‘ALOOKUP _ _ = SOME _’ mp_tac >>
  rpt (CASE_TAC >> simp[]) >> strip_tac >> imp_res_tac ALOOKUP_ADELKEY_SOME >> fs[]
QED

Theorem pdo_kinv:
  pdo lfd (w, ps) act = SOME (r, (w', ps'), evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  pown lfd ps ∧ chown ps w ∧ eown E ps w ⇒
  kinv p lfd sched w1 a cm D E w' ∧ winv w' ∧ chown ps' w' ∧ eown E ps' w'
Proof
  Cases_on ‘act’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept *)
      gvs[AllCaseEqs()] >> fs[chown_def, eown_def] >> metis_tac[MEM])
  >- ((* Read *)
      qpat_x_assum ‘option_CASE _ _ _ = _’ mp_tac >>
      Cases_on ‘ALOOKUP ps.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
      rename1 ‘ALOOKUP ps.b.tbl c = SOME f’ >>
      IF_CASES_TAC >- (strip_tac >> gvs[chown_def, eown_def] >> metis_tac[]) >>
      reverse IF_CASES_TAC >- (strip_tac >> gvs[]) >>
      ‘f ≠ lfd ∧ ¬MEM f ps.acq ∧ ALL_DISTINCT (MAP SND ps.b.tbl)’
        by (imp_res_tac ALOOKUP_MEM >> fs[pown_def, ALL_DISTINCT_APPEND, MEM_MAP] >>
            metis_tac[SND]) >>
      ‘∀c. ALOOKUP w.open_fds f = SOME c ⇒ E c’ by (fs[eown_def] >> metis_tac[]) >>
      IF_CASES_TAC
      >- (simp[l1_close_def] >> Cases_on ‘sys_close f w’ >> simp[] >>
          rename1 ‘sys_close f w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
          strip_tac >> rveq >> rpt conj_tac
          >- metis_tac[kinv_sys_quiet]
          >- metis_tac[sys_winv]
          >- (simp[chown_def, forget_def, set_outbox_def] >> rpt strip_tac
              >- (drule_all adelkey_snd >> strip_tac >>
                  ‘∃c'. ALOOKUP w.open_fds f' = SOME c'’ by fs[chown_def] >>
                  metis_tac[sys_close_open])
              >> ‘f' ≠ f’ by (strip_tac >> gvs[]) >>
              ‘∃c'. ALOOKUP w.open_fds f' = SOME c'’ by fs[chown_def] >>
              metis_tac[sys_close_open])
          >> simp[eown_def, forget_def, set_outbox_def, MEM_FILTER] >> rpt strip_tac >>
          drule_all sys_close_open_back >> strip_tac >> fs[eown_def] >> metis_tac[])
      >> strip_tac >> gvs[chown_def, eown_def, MEM_FILTER] >> rpt strip_tac >>
      TRY (imp_res_tac MEM_SND_ADELKEY_sub) >> metis_tac[])
  >> (* Write *)
  PairCases_on ‘z’ >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >>
  simp[l1do_def] >> Cases_on ‘ALOOKUP ps.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
  rename1 ‘ALOOKUP ps.b.tbl c = SOME f’ >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >- (strip_tac >> gvs[chown_def, eown_def, set_outbox_def] >> metis_tac[]) >>
  Cases_on ‘sys_send f l w’ >> simp[] >>
  rename1 ‘sys_send f l w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  strip_tac >> rveq >> rpt conj_tac
  >- metis_tac[kinv_sys_quiet]
  >- metis_tac[sys_winv]
  >> drule (CONJUNCT2 sys_quiet_open) >> strip_tac >>
  fs[chown_def, eown_def, set_outbox_def] >> metis_tac[]
QED

Theorem pacts_kinv:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ pv_rel lfd cm0 ps s ∧ pown lfd ps ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
    chown ps w ∧ eown E ps w ⇒
    kinv p lfd sched w1 a cm D E w' ∧ winv w' ∧ chown ps' w' ∧ eown E ps' w'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all pdo_hdo >> strip_tac >>
  drule_all pdo_kinv >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_polls_kinv:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    sched_wf2 (sk_of p lfd sched w1) ⇒
    kinv p lfd sched w1 a cm D E w' ∧ winv w' ∧ w'.open_fds = w.open_fds
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  ‘kinv p lfd sched w1 a cm D E w1'’ by metis_tac[kinv_sys_quiet] >>
  ‘winv w1'’ by metis_tac[sys_winv] >>
  ‘w1'.open_fds = w.open_fds’ by metis_tac[sys_quiet_open] >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_kinv:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    sched_wf2 (sk_of p lfd sched w1) ⇒
    kinv p lfd sched w1 a cm D E w' ∧ winv w' ∧ w'.open_fds = w.open_fds
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_send _ _ w = SOME (out, wa, ev)’ >>
  ‘kinv p lfd sched w1 a cm D E wa’ by metis_tac[kinv_sys_quiet] >>
  ‘winv wa’ by metis_tac[sys_winv] >>
  ‘wa.open_fds = w.open_fds’ by metis_tac[sys_quiet_open] >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_reap_kinv:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    sched_wf2 (sk_of p lfd sched w1) ∧ ¬MEM lfd fs ∧
    (∀f c. MEM f fs ∧ ALOOKUP w.open_fds f = SOME c ⇒ E c) ⇒
    kinv p lfd sched w1 a cm D E w' ∧ winv w' ∧ st'.tbl = st.tbl ∧
    (∀f. MEM f st'.closing ⇒ MEM f st.closing) ∧
    (∀g c. ALOOKUP w'.open_fds g = SOME c ⇒ ALOOKUP w.open_fds g = SOME c)
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >>
  IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs(), l1_close_def] >>
      rename1 ‘sys_close h w = SOME (out, wa, ev)’ >>
      ‘kinv p lfd sched w1 a cm D E wa’ by (irule kinv_sys_close >> fs[] >> metis_tac[]) >>
      ‘winv wa’ by metis_tac[sys_winv] >>
      (first_x_assum drule >> impl_tac
       >- (simp[] >> rpt strip_tac >> drule_all sys_close_open_back >> strip_tac >>
           first_x_assum irule >> simp[] >> metis_tac[]) >>
       simp[forget_def, set_outbox_def, MEM_FILTER] >> strip_tac >>
       metis_tac[sys_close_open_back]))
  >> first_x_assum (qspecl_then [‘w’, ‘st’, ‘w'’, ‘st'’, ‘evs’] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> simp[]
QED

Theorem in_fds_poll_set:
  MEM f (in_fds (pf_poll_set lfd hw ps hs)) ⇒ f = lfd ∨ MEM f (MAP SND ps.b.tbl)
Proof
  simp[in_fds_def, pf_poll_set_def, MEM_MAP, MEM_FILTER, MEM_FLAT, PULL_EXISTS,
       EXISTS_PROD] >>
  rw[] >> gvs[] >> every_case_tac >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[SND]
QED

(* MAIN (E): one round keeps the invariant, with the round's fetch log read
   through psk's client numbering *)
Theorem pround_kinv:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  pv_rel lfd cm0 ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ chown ps w ∧ eown E ps w ⇒
  ∃as cm' a'.
    arrs lfd (cm, a) log = (as, (cm', a')) ∧
    kinv p lfd sched w1 a' cm' (λj. D j ++ data_of j as) (λj. E j ∨ MEM (Eof2 j) as) w' ∧
    winv w' ∧ chown ps' w' ∧ eown (λj. E j ∨ MEM (Eof2 j) as) ps' w'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_kinv) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all pacts_hacts >> strip_tac >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[winv_def] >>
  drule_all pacts_l0 >> strip_tac >>
  rename1 ‘l1_polls _ wa = SOME (rv, wb, pevs)’ >>
  drule_all l1_polls_kinv >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >>
  rename1 ‘l1_flush _ (wb, pa.b) = SOME ((wc, bc), fevs)’ >>
  drule_all l1_flush_kinv >> strip_tac >>
  ‘l0_rely wb’ by gvs[winv_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((wd, pd), log, gevs)’ >>
  qmatch_asmsub_abbrev_tac ‘pf_fetch _ _ fs _’ >>
  ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wc.open_fds g = SOME c’
    by (rw[Abbr ‘fs’, MEM_FILTER] >> drule in_fds_poll_set >> strip_tac >> gvs[] >>
        fs[chown_def] >> metis_tac[]) >>
  ‘eown E (pa with b := bc) wc’ by (fs[eown_def] >> metis_tac[]) >>
  ‘eused (pa with b := bc) wc’
    by (simp[eused_def] >> rpt strip_tac
        >- (‘MEM f (MAP SND pa.b.tbl)’ by (fs[pown_def] >> metis_tac[]) >>
            ‘∃c. ALOOKUP wa.open_fds f = SOME c’ by fs[chown_def] >>
            gvs[] >> metis_tac[used_open_fds])
        >> gvs[l0own_def]) >>
  drule_all kinv_fetch >> strip_tac >>
  drule_all pf_fetch_acq >> strip_tac >>
  drule pf_fetch_b >> strip_tac >>
  rename1 ‘l1_reap _ (wd, _) = SOME ((we, be), cevs)’ >>
  ‘¬MEM lfd pd.b.closing’ by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  ‘∀f c. MEM f (hup_step (hup_fds rv) (outbox_of pa.b) log pd).b.closing ∧
         ALOOKUP wd.open_fds f = SOME c ⇒ (λj. E j ∨ MEM (Eof2 j) as) c’
    by (simp_tac std_ss [hup_step_fields] >> fs[eown_def] >> metis_tac[]) >>
  mp_tac (Q.SPECL [‘pd.b.closing’, ‘wd’,
                   ‘(hup_step (hup_fds rv) (outbox_of pa.b) log pd).b’, ‘we’, ‘be’, ‘cevs’]
          (Q.INST [‘E’ |-> ‘λj. E j ∨ MEM (Eof2 j) as’, ‘a’ |-> ‘a'’, ‘cm’ |-> ‘cm'’,
                   ‘D’ |-> ‘λj. D j ++ data_of j as’] l1_reap_kinv)) >>
  impl_tac >- (simp[] >> gvs[] >> metis_tac[]) >> strip_tac >>
  drule l1_reap_wkeep >> strip_tac >>
  qexistsl_tac [‘as’, ‘cm'’, ‘a'’] >> simp[] >>
  conj_tac
  >- (simp[chown_def] >> rpt strip_tac
      >- ((* a handle's fd *)
          ‘MEM f (MAP SND pa.b.tbl)’ by gvs[] >>
          ‘¬MEM f pa.b.closing’
            by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
          ‘∃c. ALOOKUP wa.open_fds f = SOME c’ by fs[chown_def] >>
          fs[wkeep_def] >> gvs[] >> metis_tac[])
      >> (* a queued fd *)
      qpat_x_assum ‘∀f. MEM f pd.acq ⇒ _’ drule >> strip_tac
      >- (‘¬MEM f pa.b.closing’ by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
          ‘∃c. ALOOKUP wa.open_fds f = SOME c’ by fs[chown_def] >>
          fs[wkeep_def] >> gvs[] >> metis_tac[])
      >> ‘¬MEM f pa.b.closing’ by (gvs[l0own_def] >> metis_tac[]) >>
      fs[wkeep_def] >> gvs[] >> metis_tac[])
  >> fs[eown_def] >> rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED

(* ========================================================================
   F. The run, and R2′'s first half: psk is never ahead of the kernel
   ======================================================================== *)

Theorem plog_rlog:
  run_ok lfd hw ifds m w0 ⇒ plog lfd hw ifds m w0 k = rlog lfd hw ifds m w0 k
Proof
  rw[plog_def, rlog_def] >> drule prun_some >>
  disch_then (qspec_then ‘SUC k’ assume_tac) >> simp[] >>
  Cases_on ‘prun lfd hw ifds m w0 (SUC k)’ >> rename1 ‘_ = (h, r)’ >>
  PairCases_on ‘r’ >> simp[]
QED

Theorem pcm_SUC:
  run_ok lfd hw ifds m w0 ⇒
  arrs lfd (pcm lfd hw ifds m w0 k) (rlog lfd hw ifds m w0 k) =
  (parr lfd hw ifds m w0 k, pcm lfd hw ifds m w0 (SUC k))
Proof
  rw[pcm_def, parr_def] >> drule plog_rlog >> simp[]
QED

(* The run's invariant at round k *)
Definition rinv_def:
  rinv p lfd sched w1 hw ifds m k ⇔
    kinv p lfd sched w1 (SND (pcm lfd hw ifds m w1 k)) (FST (pcm lfd hw ifds m w1 k))
         (λj. data_of j (upto (parr lfd hw ifds m w1) k))
         (λj. MEM (Eof2 j) (upto (parr lfd hw ifds m w1) k))
         (rworld lfd hw ifds m w1 k) ∧
    chown (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k) ∧
    eown (λj. MEM (Eof2 j) (upto (parr lfd hw ifds m w1) k))
         (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k)
End

Theorem rinv_run:
  simple_v2 p lfd sched w1 ∧ (∀h. ¬w1.ch.emfile_drops h) ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧ w1.open_fds = [] ∧
  run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64)) ⇒
  ∀k. rinv p lfd sched w1 hw ifds m k
Proof
  strip_tac >>
  ‘MEM lfd (l0_used w1)’ by simp[l0_used_def] >>
  Induct
  >- (simp[rinv_def, rworld_def, rstate_def, prun_0, pcm_def, data_of_def] >>
      fs[kinv_def, kworld_def, ticks2_def, sinv_def, wk_def, lk_def, sk_of_def, qof_def,
         chown_def, eown_def, pinit_def, l1init_def]) >>
  drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  fs[rinv_def] >>
  drule_then drule pround_kinv >> simp[] >>
  disch_then (qspecl_then [‘s’, ‘cm’] mp_tac) >> simp[] >> strip_tac >>
  drule pcm_SUC >> disch_then (qspec_then ‘k’ mp_tac) >>
  strip_tac >> fs[] >> rveq >> simp[upto_SUC]
QED

Theorem arrs_conns_of:
  ∀l cm k as cm' k'. arrs lfd (cm, k) l = (as, (cm', k')) ⇒ conns_of as + k = k'
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> PairCases_on ‘ck’ >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[conns_of_def]
QED

Theorem conns_of_upto_parr:
  run_ok lfd hw ifds m w1 ⇒
  ∀k. conns_of (upto (parr lfd hw ifds m w1) k) = SND (pcm lfd hw ifds m w1 k)
Proof
  strip_tac >> Induct >- simp[pcm_def] >>
  drule pcm_SUC >> disch_then (qspec_then ‘k’ mp_tac) >>
  Cases_on ‘pcm lfd hw ifds m w1 k’ >> Cases_on ‘pcm lfd hw ifds m w1 (SUC k)’ >>
  strip_tac >> drule arrs_conns_of >> gvs[upto_SUC]
QED

(* MAIN (R2′, first half): at the end of each round, what psk has delivered
   is within what the kernel had delivered by the polls made so far: never
   ahead, per client (connections, data as a prefix, EOF) *)
Theorem l1pf_never_ahead:
  simple_v2 p lfd sched w1 ∧ (∀h. ¬w1.ch.emfile_drops h) ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧ w1.open_fds = [] ∧
  run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64)) ⇒
  ∀n. within (upto (parr lfd hw ifds m w1) (SUC n))
             (upto (kernel_steps p lfd sched w1) (round_instant lfd hw ifds m w1 n))
Proof
  rpt strip_tac >>
  drule_all rinv_run >> disch_then (qspec_then ‘SUC n’ mp_tac) >>
  simp[rinv_def, kinv_def, round_instant_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘kworld p lfd sched w1 P’ >>
  ‘vinv lfd (kworld p lfd sched w1 P) (upto (kernel_steps p lfd sched w1) P)’
    by metis_tac[kworld_vinv] >>
  qabbrev_tac ‘s = kworld p lfd sched w1 P’ >>
  qabbrev_tac ‘w = rworld lfd hw ifds m w1 (SUC n)’ >>
  qabbrev_tac ‘as = upto (parr lfd hw ifds m w1) (SUC n)’ >>
  ‘conns_of as = SND (pcm lfd hw ifds m w1 (SUC n))’
    by (simp[Abbr ‘as’] >> metis_tac[conns_of_upto_parr]) >>
  qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  qpat_x_assum ‘vinv _ _ _’ (strip_assume_tac o SIMP_RULE std_ss [vinv_def]) >>
  simp[within_def] >> rpt conj_tac >> TRY (fs[] >> NO_TAC) >>
  gen_tac >> reverse (Cases_on ‘j < LENGTH w.chans’)
  >- (‘SND (pcm lfd hw ifds m w1 (SUC n)) ≤ j’ by simp[] >>
      ‘data_of j as = [] ∧ ¬MEM (Eof2 j) as’ by metis_tac[] >> simp[]) >>
  ‘wch (EL j w.chans) (EL j s.clients) ∧
   dch (data_of j as) (MEM (Eof2 j) as) (EL j w.chans)’ by metis_tac[] >>
  ‘j < LENGTH s.clients’ by simp[] >>
  ‘(EL j s.clients).incoming = data_of j (upto (kernel_steps p lfd sched w1) P) ∧
   ((EL j s.clients).peer_closed ⇔ MEM (Eof2 j) (upto (kernel_steps p lfd sched w1) P))’
    by metis_tac[] >>
  fs[wch_def, dch_def] >> conj_tac
  >- (irule IS_PREFIX_TRANS >> qexists_tac ‘(EL j w.chans).peer_sent’ >> simp[] >>
      irule IS_PREFIX_TRANS >> qexists_tac ‘data_of j as ++ (EL j w.chans).inbox’ >>
      simp[IS_PREFIX_APPEND] >> metis_tac[])
  >> metis_tac[]
QED

(* ========================================================================
   G. R2′'s second half: psk misses nothing
   ======================================================================== *)

(* G1. Every round polls: the kernel's instant advances *)

Definition hgrow_def:
  hgrow (w : l0world) (w' : l0world) k ⇔ ∃h. w'.hist = w.hist ++ h ∧ k ≤ npolls h
End

Theorem npolls_append:
  npolls (h1 ++ h2) = npolls h1 + npolls h2
Proof
  simp[npolls_def, FILTER_APPEND]
QED

Theorem hgrow_refl[simp]:
  hgrow w w 0
Proof
  simp[hgrow_def] >> qexists_tac ‘[]’ >> simp[npolls_def]
QED

Theorem hgrow_trans:
  hgrow w w1 a ∧ hgrow w1 w2 b ⇒ hgrow w w2 (a + b)
Proof
  rw[hgrow_def] >> qexists_tac ‘h ++ h'’ >> simp[npolls_append]
QED

Theorem hgrow_mono:
  hgrow w w' a ∧ b ≤ a ⇒ hgrow w w' b
Proof
  rw[hgrow_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem l0_do_hgrow:
  l0_do n conf alen w = SOME (out, w', ev) ⇒
  hgrow w w' (if n = «sys_poll» then 1 else 0)
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> simp[hgrow_def] >> rw[npolls_def]
QED

Theorem sys_hgrow:
  (sys_poll fes w = SOME (out, w', ev) ⇒ hgrow w w' 1) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ hgrow w w' 0) ∧
  (sys_close f w = SOME (out, w', ev) ⇒ hgrow w w' 0) ∧
  (sys_accept f w = SOME (out, w', ev) ⇒ hgrow w w' 0) ∧
  (sys_recv f k w = SOME (out, w', ev) ⇒ hgrow w w' 0)
Proof
  rw[sys_poll_def, sys_send_def, sys_close_def, sys_accept_def, sys_recv_def] >>
  drule l0_do_hgrow >> simp[]
QED

Theorem l1_close_hgrow:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ hgrow w w' 0
Proof
  rw[l1_close_def, AllCaseEqs()] >> metis_tac[sys_hgrow]
QED

Theorem pdo_hgrow:
  pdo lfd (w, ps) act = SOME (r, (w', ps'), evs) ⇒ hgrow w w' 0
Proof
  Cases_on ‘act’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[l1do_def, AllCaseEqs()] >>
  metis_tac[l1_close_hgrow, sys_hgrow, hgrow_refl]
QED

Theorem pacts_hgrow:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ hgrow w w' 0
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule pdo_hgrow >> strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all hgrow_trans >> simp[]
QED

Theorem l1_polls_hgrow:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒
                    hgrow w w' (if chs = [] then 0 else 1)
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule (CONJUNCT1 sys_hgrow) >> strip_tac >> first_x_assum drule >> strip_tac >>
  ‘hgrow w w' (1 + if chs = [] then 0 else 1)’ by metis_tac[hgrow_trans] >>
  irule hgrow_mono >> first_assum (irule_at Any) >> rw[]
QED

Theorem l1_flush_hgrow:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ hgrow w w' 0
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule >> simp[]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule (el 2 (CONJUNCTS sys_hgrow)) >> strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all hgrow_trans >> simp[]
QED

Theorem pf_fetch_hgrow:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ hgrow w w' 0
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[sys_hgrow, hgrow_trans, ADD_CLAUSES]
QED

Theorem l1_reap_hgrow:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ hgrow w w' 0
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >>
  IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> PairCases_on ‘ws’ >>
      drule l1_close_hgrow >> strip_tac >> first_x_assum drule >> strip_tac >>
      drule_all hgrow_trans >> simp[])
  >> first_x_assum drule >> simp[]
QED

Theorem pround_hgrow:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ⇒ hgrow w w' 1
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  drule pacts_hgrow >> strip_tac >>
  drule l1_polls_hgrow >> simp[poll_chunks_ne] >> strip_tac >>
  drule l1_flush_hgrow >> strip_tac >>
  drule pf_fetch_hgrow >> strip_tac >>
  drule l1_reap_hgrow >> strip_tac >>
  metis_tac[hgrow_trans, ADD_CLAUSES]
QED

Theorem round_instant_ge:
  run_ok lfd hw ifds m w1 ⇒
  ∀k. k ≤ npolls (rworld lfd hw ifds m w1 k).hist − npolls w1.hist ∧
      npolls w1.hist ≤ npolls (rworld lfd hw ifds m w1 k).hist
Proof
  strip_tac >> Induct >- simp[rworld_def, prun_0] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule pround_hgrow >> rw[hgrow_def] >> gvs[npolls_append]
QED

(* ========================================================================
   G2. In simple worlds no call of the run is retried, and no accept fails
   (the latter with room for one more fd at each round's start)
   ======================================================================== *)

(* An fd L1 may fetch on without EAGAIN: the listener with a connection
   queued, or a connection with input or an EOF pending *)
Definition rdy_def:
  rdy lfd w f ⇔ if f = lfd then qof w lfd ≠ [] else pend w f
End

(* A call that is not retried, and, if it is an accept on the listener,
   does not fail *)
Definition ok_ev_def:
  ok_ev lfd ev ⇔ ¬retried ev ∧ (ev_on «sys_accept» lfd ev ⇒ ¬failed ev)
End

Theorem sinv_hist[simp]:
  sinv lfd p a cm D E s (w with hist := h) ⇔ sinv lfd p a cm D E s w
Proof
  simp[sinv_def, wk_def, lk_def, qof_def]
QED

Theorem sinv_clock[simp]:
  sinv lfd p a cm D E s (w with clock := c) ⇔ sinv lfd p a cm D E s w
Proof
  simp[sinv_def, wk_def, lk_def, qof_def]
QED

Theorem rdy_hist[simp]:
  rdy lfd (w with hist := h) f ⇔ rdy lfd w f
Proof
  simp[rdy_def, qof_def, pend_def, l0_chan_of_def]
QED

Theorem readable_zip_inv:
  ∀fes. MEM f (readable_fds (ZIP (MAP FST fes, MAP g fes))) ⇒
        ∃e. MEM (f, e) fes ∧ ((g (f, e)).rin ∨ (g (f, e)).rhup ∨ (g (f, e)).rerr)
Proof
  Induct >> simp[FORALL_PROD, readable_fds_def] >> rw[] >> gvs[readable_fds_def] >>
  metis_tac[]
QED

(* In the invariant's worlds, a readable fd is ready *)
Theorem sinv_readable_lfd:
  sinv lfd p a cm D E s w ∧
  ((byte_revents (fd_revents w (lfd, e))).rin ∨ (byte_revents (fd_revents w (lfd, e))).rhup ∨
   (byte_revents (fd_revents w (lfd, e))).rerr) ⇒
  rdy lfd w lfd
Proof
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> strip_tac >>
  (‘ALOOKUP w.open_fds lfd = NONE’
     by (Cases_on ‘ALOOKUP w.open_fds lfd’ >> simp[] >> res_tac >> fs[]) >>
   ‘l0_chan_of w lfd = NONE’ by simp[l0_chan_of_def] >>
   gvs[fd_revents_def, rdy_def, qof_def, byte_revents_revents_byte, no_revents_def])
QED

Theorem sinv_readable_ch:
  sinv lfd p a cm D E s w ∧ ALOOKUP w.open_fds f = SOME c ∧
  ((byte_revents (fd_revents w (f, e))).rin ∨ (byte_revents (fd_revents w (f, e))).rhup ∨
   (byte_revents (fd_revents w (f, e))).rerr) ⇒
  rdy lfd w f
Proof
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> strip_tac >>
  (res_tac >> ‘c < LENGTH w.chans’ by simp[] >>
   ‘l0_chan_of w f = SOME c’ by simp[l0_chan_of_def] >>
   ‘wch (EL c w.chans) (EL c s.clients)’ by fs[] >>
   gvs[fd_revents_def, chan_revents_def, wch_def, rdy_def, pend_def,
       byte_revents_revents_byte, no_revents_def] >>
   every_case_tac >> gvs[])
QED

Theorem poll_out_res:
  LENGTH fes ≤ 4096 ⇒ ∃k. l0_res_of (poll_out w fes) = Ok k
Proof
  strip_tac >> simp[poll_out_def] >> irule_at Any l0_res_of_enc_app >>
  simp[l0_res_ok_def] >>
  qspecl_then [‘λfe. fd_revents w fe ≠ 0w’, ‘fes’] assume_tac LENGTH_FILTER_LEQ >>
  simp[]
QED

(* A poll: not retried; what it reports readable (of the listener and the
   open fds) is ready after it *)
Theorem sys_poll_rdy:
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  EVERY (λ(f, e). e < 256) fes ∧ sys_poll fes w = SOME (out, w', ev) ⇒
  kinv p lfd sched w1 a cm D E w' ∧ ok_ev lfd ev ∧ w'.open_fds = w.open_fds ∧
  ∀f. MEM f (readable_fds (poll_revents fes out)) ∧
      (f = lfd ∨ ∃c. ALOOKUP w.open_fds f = SOME c) ⇒ rdy lfd w' f
Proof
  strip_tac >>
  ‘kinv p lfd sched w1 a cm D E w'’ by metis_tac[kinv_sys_quiet] >>
  ‘w'.open_fds = w.open_fds’ by metis_tac[sys_quiet_open] >>
  ‘l0_rely w’ by fs[winv_def] >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  drule_all ev_do >> strip_tac >>
  drule l0_do_cases >> strip_tac >>
  ‘poll_entries (DROP 1 (poll_conf fes)) = fes ∧ HD (poll_conf fes) = 0w ∧ poll_conf fes ≠ []’
    by simp[poll_conf_def, poll_entries_conf] >>
  drule_all call_poll_same >> strip_tac >> gvs[] >>
  ‘∀h. (l0_tick «sys_poll» w).ch.transient h = NONE’
    by fs[kinv_def, simple_v2_def, simple0_def] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[] >>
  simp[ok_ev_def] >> rpt conj_tac
  >- (strip_tac >> qspecl_then [‘l0_tick «sys_poll» w’, ‘fes’] mp_tac
                     (Q.GENL [‘w’, ‘fes’] poll_out_res) >> simp[] >> strip_tac >> gvs[])
  >- simp[ev_on_def]
  >> rpt strip_tac >>
  qpat_x_assum ‘MEM _ (readable_fds _)’ mp_tac >>
  simp[poll_revents_def] >>
  qspecl_then [‘l0_tick «sys_poll» w’, ‘fes’] mp_tac
    (Q.GENL [‘w’, ‘fes’] poll_out_res) >> simp[] >> strip_tac >> simp[DROP_poll_out] >>
  ‘TAKE (LENGTH fes) (MAP (fd_revents (l0_tick «sys_poll» w)) fes) =
   MAP (fd_revents (l0_tick «sys_poll» w)) fes’ by metis_tac[LENGTH_MAP, TAKE_LENGTH_ID] >>
  simp[MAP_MAP_o] >> strip_tac >>
  drule readable_zip_inv >> simp[] >> strip_tac >>
  qpat_x_assum ‘kinv _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [kinv_def]) >>
  fs[] >> metis_tac[sinv_readable_lfd, sinv_readable_ch, ticks_open_fds]
QED

(* A call whose failures are not transient (and, for an accept, do not
   happen) is ok *)
Theorem do_ok_ev:
  l0_rely w ∧ l0_do n conf alen w = SOME (out, w', ev) ∧ n ≠ «sys_poll» ∧
  (∀e x. l0_res_of out = Fail e x ⇒ ¬l1_transient e ∧ n ≠ «sys_accept») ⇒ ok_ev lfd ev
Proof
  strip_tac >> drule_all ev_do >> drule_all ev_failed >> rw[ok_ev_def] >> metis_tac[]
QED

Theorem res_of_ok_app:
  ∃k. l0_res_of (enc_res (Ok v) ++ rest) = Ok k
Proof
  simp[l0_res_of_def, dec_res_def, enc_res_def]
QED

Theorem res_of_fail0:
  LENGTH (w.ch.errno_of w.hist) = 4 ⇒
  l0_res_of (enc_res (fail w e)) = Fail e (w.ch.errno_of w.hist)
Proof
  metis_tac[res_of_fail, APPEND_NIL]
QED

(* The open fds' channels in the invariant's worlds *)
Theorem sinv_open_chan:
  sinv lfd p a cm D E s w ∧ ALOOKUP w.open_fds f = SOME j ⇒
  j < LENGTH w.chans ∧ f ≠ lfd ∧ l0_chan_of w f = SOME j ∧ ¬(EL j w.chans).connecting ∧
  ¬(EL j w.chans).broken ∧ (EL j w.chans).err = NONE ∧ ¬(EL j w.chans).shut ∧
  ¬(EL j w.chans).closed
Proof
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> strip_tac >> res_tac >>
  ‘j < LENGTH w.chans’ by simp[] >>
  ‘wch (EL j w.chans) (EL j s.clients)’ by fs[] >>
  fs[wch_def, l0_chan_of_def] >> metis_tac[]
QED

Theorem sinv_listener:
  sinv lfd p a cm D E s w ⇒ ∃q. w.listeners = [(lfd, p, q)]
Proof
  rw[sinv_def, wk_def]
QED

(* A send on an fd of L1's, never the listener nor a reserved fd: not
   retried (simple worlds take every byte) *)
Theorem l0_send_simple:
  sinv lfd p a cm D E s w ∧ (∀h. w.ch.transient h = NONE) ∧ (∀j h b n. w.ch.takes j h b n = n) ∧
  f ≠ lfd ∧ ¬MEM f w.reserved ∧ l0_send f bs w = (r, w') ⇒
  (∃k. r = Ok k) ∨ ∃e. r = fail w e ∧ ¬l1_transient e
Proof
  strip_tac >> drule sinv_listener >> strip_tac >>
  qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >> simp[l0_send_def] >>
  Cases_on ‘l0_chan_of w f’ >> simp[]
  >- (strip_tac >> gvs[not_chan_def, is_listener_fd_def] >> disj2_tac >>
      qexists_tac ‘E_BADF’ >> simp[l1_transient_def]) >>
  rename1 ‘l0_chan_of w f = SOME j’ >>
  ‘ALOOKUP w.open_fds f = SOME j’ by fs[l0_chan_of_def, AllCaseEqs()] >>
  drule_all sinv_open_chan >> strip_tac >> simp[] >>
  rw[] >> simp[l1_transient_def] >> Cases_on ‘bs’ >> fs[]
QED

Theorem l0_close_simple:
  (∀h. w.ch.close_intr h = NONE) ∧ l0_close f w = (r, w') ⇒
  (∃k. r = Ok k) ∨ ∃e. r = fail w e ∧ ¬l1_transient e
Proof
  rw[l0_close_def] >> gvs[] >> disj2_tac >> qexists_tac ‘E_BADF’ >> simp[l1_transient_def]
QED

(* A recv on a ready open fd returns data or an EOF *)
Theorem l0_recv_simple:
  sinv lfd p a cm D E s w ∧ (∀h. w.ch.transient h = NONE) ∧ (∀j h x. w.ch.short j h x = x) ∧
  pend w f ∧ 0 < n ∧ l0_recv f n w = (r, d, w') ⇒
  ∃k. r = Ok k
Proof
  strip_tac >> fs[pend_def] >>
  ‘ALOOKUP w.open_fds f = SOME j’ by fs[l0_chan_of_def, AllCaseEqs()] >>
  drule_all sinv_open_chan >> strip_tac >>
  qpat_x_assum ‘l0_recv _ _ _ = _’ mp_tac >> simp[l0_recv_def] >> rw[] >> gvs[]
QED

(* An accept with a connection queued and an fd free succeeds *)
Theorem l0_accept_simple:
  sinv lfd p a cm D E s w ∧ (∀h. w.ch.transient h = NONE) ∧ qof w lfd ≠ [] ∧
  w2n (lowest_fd w) < w.fd_limit ∧ l0_accept lfd w = (r, w') ⇒
  ∃k. r = Ok k
Proof
  strip_tac >> drule sinv_listener >> strip_tac >>
  qpat_x_assum ‘l0_accept _ _ = _’ mp_tac >> gvs[l0_accept_def, qof_def] >>
  Cases_on ‘q’ >> gvs[] >>
  ‘h < LENGTH w.chans’
    by (fs[sinv_def, lk_def, qof_def] >>
        ‘MEM h (GENLIST (λi. a + i) (LENGTH w.chans − a))’ by metis_tac[MEM] >>
        fs[MEM_GENLIST]) >>
  ‘¬(EL h w.chans).broken’
    by (fs[sinv_def, wk_def] >> ‘wch (EL h w.chans) (EL h s.clients)’ by fs[] >> fs[wch_def]) >>
  strip_tac >> gvs[l0_alloc_def]
QED

Theorem FOLDL_upd_used[simp]:
  ∀q w0. l0_used (FOLDL (λw j. upd_lchan j g w) w0 q) = l0_used w0
Proof
  Induct >> simp[]
QED

(* A close frees fds, never takes one *)
Theorem l0_close_used:
  l0_close f w = (r, w') ⇒ ∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)
Proof
  rw[l0_close_def, close_fd_def, AllCaseEqs()] >> gvs[] >>
  gvs[l0_used_def, MEM_FST_ADELKEY, MEM_FILTER, MEM_MAP, EXISTS_PROD] >>
  metis_tac[]
QED

(* With fewer fds in use than the limit, the lowest free fd is below it *)
Theorem lowest_fd_room:
  w.fd_limit ≤ 2 ** 31 ∧ CARD (set (l0_used w)) < w.fd_limit ⇒
  w2n (lowest_fd w) < w.fd_limit
Proof
  strip_tac >> ‘(2147483648:num) < dimword (:64)’ by EVAL_TAC >>
  ‘∃n. n < w.fd_limit ∧ ¬MEM (n2w n : word64) (l0_used w)’
    by (CCONTR_TAC >> fs[] >>
        ‘count w.fd_limit ⊆ IMAGE w2n (set (l0_used w))’
          by (rw[SUBSET_DEF] >> res_tac >> qexists_tac ‘n2w x’ >> simp[] >>
              ‘x < dimword (:64)’
                by (‘(2147483648:num) < dimword (:64)’ by EVAL_TAC >> decide_tac) >>
              simp[] >> metis_tac[]) >>
        ‘CARD (count w.fd_limit) ≤ CARD (IMAGE w2n (set (l0_used w)))’
          by (irule CARD_SUBSET >> simp[IMAGE_FINITE]) >>
        ‘CARD (IMAGE w2n (set (l0_used w))) ≤ CARD (set (l0_used w))’
          by simp[CARD_IMAGE] >>
        fs[]) >>
  simp[lowest_fd_def] >> numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rw[] >> ‘n' ≤ n’ by (CCONTR_TAC >> fs[NOT_LESS_EQUAL] >> res_tac) >>
  ‘w.fd_limit ≤ 2147483648’ by fs[] >>
  ‘n' < dimword (:64)’ by decide_tac >>
  simp[]
QED

Theorem sys_send_ok:
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ f ≠ lfd ∧ ¬MEM f w.reserved ∧
  sys_send f bs w = SOME (out, w', ev) ⇒ ok_ev lfd ev ∧ l0_used w' = l0_used w
Proof
  rw[sys_send_def] >> ‘l0_rely w’ by fs[winv_def] >>
  TRY (drule l0_do_used >> simp[] >> NO_TAC) >>
  ‘«sys_send» ≠ «sys_poll»’ by simp[] >>
  ‘∀e x. l0_res_of out = Fail e x ⇒ ¬l1_transient e ∧ «sys_send» ≠ «sys_accept»’
    suffices_by (strip_tac >> drule_all do_ok_ev >> simp[]) >>
  drule l0_do_cases >> strip_tac >>
  drule_then (qspec_then ‘«sys_send»’ mp_tac) kinv_tick_clock >> simp[] >> strip_tac >>
  ‘∀j h b n. w.ch.takes j h b n = n’ by fs[kinv_def, simple_v2_def, simple0_def] >>
  ‘LENGTH (w.ch.errno_of w.hist) = 4’ by fs[l0_rely_def] >>
  gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
  rename1 ‘l0_send _ _ _ = (r, _)’ >>
  ‘(∃k. r = Ok k) ∨ ∃e. r = fail (w with clock := w.clock + 1) e ∧ ¬l1_transient e’
    by (irule l0_send_simple >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[res_of_fail0] >>
  qspecl_then [‘k’, ‘[]’] strip_assume_tac (Q.GENL [‘v’, ‘rest’] res_of_ok_app) >> gvs[]
QED

Theorem sys_close_ok:
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sys_close f w = SOME (out, w', ev) ⇒
  ok_ev lfd ev ∧ ∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)
Proof
  simp[sys_close_def] >> strip_tac >> ‘l0_rely w’ by fs[winv_def] >>
  drule l0_do_cases >> strip_tac >>
  drule_then (qspec_then ‘«sys_close»’ mp_tac) kinv_tick_clock >> simp[] >> strip_tac >>
  ‘∀h. w.ch.close_intr h = NONE’ by fs[kinv_def, simple_v2_def, simple0_def] >>
  ‘LENGTH (w.ch.errno_of w.hist) = 4’ by fs[l0_rely_def] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 ‘l0_close _ _ = (r, _)’ >> reverse conj_tac
  >- (drule l0_close_used >> gvs[l0_used_def]) >>
  ‘«sys_close» ≠ «sys_poll»’ by simp[] >>
  ‘∀e x. l0_res_of (enc_res r) = Fail e x ⇒ ¬l1_transient e ∧ «sys_close» ≠ «sys_accept»’
    suffices_by (strip_tac >> qpat_x_assum ‘l0_do _ _ _ _ = _’ assume_tac >>
                 drule_all do_ok_ev >> simp[]) >>
  (   ‘(∃k. r = Ok k) ∨ ∃e. r = fail (w with clock := w.clock + 1) e ∧ ¬l1_transient e’
        by (irule l0_close_simple >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> gvs[res_of_fail0] >>
      qspecl_then [‘k’, ‘[]’] strip_assume_tac (Q.GENL [‘v’, ‘rest’] res_of_ok_app) >> gvs[])
QED

Theorem sys_recv_ok:
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ pend w f ∧ sys_recv f pf_chunk w = SOME (out, w', ev) ⇒
  ok_ev lfd ev ∧ l0_used w' = l0_used w ∧ ∃k. l0_res_of out = Ok k
Proof
  simp[sys_recv_def] >> strip_tac >> ‘l0_rely w’ by fs[winv_def] >>
  ‘l0_used w' = l0_used w’ by (drule l0_do_used >> simp[]) >> simp[] >>
  ‘∃k. l0_res_of out = Ok k’
    suffices_by (strip_tac >> simp[] >>
                 ‘«sys_recv» ≠ «sys_poll»’ by simp[] >>
                 ‘∀e x. l0_res_of out = Fail e x ⇒ ¬l1_transient e ∧ «sys_recv» ≠ «sys_accept»’
                   by simp[] >>
                 drule_all do_ok_ev >> simp[]) >>
  drule l0_do_cases >> strip_tac >>
  drule_then (qspec_then ‘«sys_recv»’ mp_tac) kinv_tick_clock >> simp[] >> strip_tac >>
  gvs[l0_call_def, l0_hdr_def, fd_ok_def] >> pairarg_tac >> gvs[] >>
  rename1 ‘l0_recv _ _ _ = (r, d, _)’ >>
  ‘0 < pf_chunk’ by simp[pf_chunk_def] >>
  ‘pend (w with clock := w.clock + 1) f’ by fs[pend_def, l0_chan_of_def] >>
  ‘∃k. r = Ok k’
    by (mp_tac (Q.INST [‘w’ |-> ‘w with clock := w.clock + 1’, ‘n’ |-> ‘pf_chunk’,
                        ‘s’ |-> ‘kworld p lfd sched w1 (npolls w.hist − npolls w1.hist)’,
                        ‘w'’ |-> ‘w''’] l0_recv_simple) >>
        impl_tac >- fs[] >> simp[]) >>
  gvs[] >>
  qspecl_then [‘k’, ‘d ++ REPLICATE (pf_chunk − LENGTH d) 0w’] strip_assume_tac
    (Q.GENL [‘v’, ‘rest’] res_of_ok_app) >> gvs[]
QED

Theorem sys_accept_ok:
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ qof w lfd ≠ [] ∧
  CARD (set (l0_used w)) < w.fd_limit ∧ sys_accept lfd w = SOME (out, w', ev) ⇒
  ok_ev lfd ev ∧ ∃k. l0_res_of out = Ok k
Proof
  simp[sys_accept_def] >> strip_tac >> ‘l0_rely w’ by fs[winv_def] >>
  ‘∃k. l0_res_of out = Ok k’
    suffices_by (strip_tac >> simp[] >>
                 ‘«sys_accept» ≠ «sys_poll»’ by simp[] >>
                 ‘∀e x. l0_res_of out = Fail e x ⇒ ¬l1_transient e ∧ «sys_accept» ≠ «sys_accept»’
                   by simp[] >>
                 drule_all do_ok_ev >> simp[]) >>
  drule l0_do_cases >> strip_tac >>
  drule_then (qspec_then ‘«sys_accept»’ mp_tac) kinv_tick_clock >> simp[] >> strip_tac >>
  ‘lowest_fd (w with clock := w.clock + 1) = lowest_fd w’ by simp[lowest_fd_def, l0_used_def] >>
  ‘w2n (lowest_fd w) < w.fd_limit’ by (irule lowest_fd_room >> fs[l0_rely_def]) >>
  drule qof_call_accept >> simp[] >> strip_tac >> gvs[] >>
  ‘qof (w with clock := w.clock + 1) lfd ≠ []’ by fs[qof_def] >>
  ‘∃k. r = Ok k’
    by (mp_tac (Q.INST [‘w’ |-> ‘w with clock := w.clock + 1’,
                        ‘s’ |-> ‘kworld p lfd sched w1 (npolls w.hist − npolls w1.hist)’,
                        ‘w'’ |-> ‘w1'’] l0_accept_simple) >>
        impl_tac >- fs[] >> simp[]) >>
  gvs[] >>
  qspecl_then [‘k’, ‘[]’] strip_assume_tac (Q.GENL [‘v’, ‘rest’] res_of_ok_app) >> gvs[]
QED

(* Readiness of other fds survives an accept and a recv *)
Theorem rdy_sys_accept:
  winv w ∧ rdy lfd w g ∧ g ≠ lfd ∧ sys_accept lfd w = SOME (out, w', ev) ⇒ rdy lfd w' g
Proof
  rw[rdy_def, sys_accept_def] >> drule_at (Pos last) pend_do >> simp[] >>
  disch_then irule >> simp[]
QED

Theorem rdy_sys_recv:
  winv w ∧ rdy lfd w g ∧ g ≠ f ∧ sys_recv f n w = SOME (out, w', ev) ⇒ rdy lfd w' g
Proof
  rw[rdy_def, sys_recv_def]
  >- (drule_at (Pos last) qof_do >> simp[] >> disch_then (qspec_then ‘g’ strip_assume_tac) >>
      simp[])
  >> drule_at (Pos last) pend_do >> simp[] >> disch_then irule >> simp[]
QED

(* The fetch: every accept and recv is on a ready fd, so none is retried
   and the accept does not fail *)
Theorem pf_fetch_ok:
  ∀fs w ps w' ps' log evs a cm D E.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    (∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP w.open_fds g = SOME c) ∧
    (∀g. MEM g fs ∧ wants_input lfd hw ps g ⇒ rdy lfd w g) ∧
    (wants_input lfd hw ps lfd ⇒ CARD (set (l0_used w)) < w.fd_limit) ⇒
    EVERY (ok_ev lfd) evs
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> simp[Once pf_fetch_def] >>
  reverse (Cases_on ‘wants_input lfd hw ps g’) >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      disch_then (qspecl_then [‘a’, ‘cm’, ‘D’, ‘E’] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  IF_CASES_TAC
  >- ((* an accept *)
      pop_assum SUBST_ALL_TAC >> strip_tac >>
      qpat_x_assum ‘option_CASE (sys_accept _ _) _ _ = _’ mp_tac >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, wa, ev)’ >>
      pairarg_tac >> simp[] >>
      Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
      rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
      strip_tac >> rveq >>
      ‘rdy lfd w lfd’ by metis_tac[] >>
      ‘qof w lfd ≠ []’ by fs[rdy_def] >>
      ‘CARD (set (l0_used w)) < w.fd_limit’ by metis_tac[] >>
      drule_all sys_accept_ok >> strip_tac >> simp[] >>
      drule_all (el 4 (CONJUNCTS sys_winv)) >> strip_tac >>
      drule_all kinv_sys_accept >> strip_tac >- gvs[] >>
      gvs[] >> last_x_assum drule >> disch_then drule >>
      impl_tac >- (
        simp[] >> rpt conj_tac
        >- (rpt strip_tac >> ‘∃c. ALOOKUP w.open_fds g = SOME c’ by metis_tac[] >>
            rw[] >> metis_tac[])
        >- (rpt strip_tac >> ‘g ≠ lfd’ by (strip_tac >> gvs[wants_input_def]) >>
            ‘wants_input lfd hw ps g’ by fs[wants_input_def] >>
            irule rdy_sys_accept >> metis_tac[])
        >> simp[wants_input_def]) >>
      simp[])
  >> (* a recv *)
  strip_tac >>
  qpat_x_assum ‘option_CASE (sys_recv _ _ _) _ _ = _’ mp_tac >>
  Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME (out, wa, ev)’ >>
  pairarg_tac >> simp[] >>
  Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
  rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
  strip_tac >> rveq >>
  ‘rdy lfd w g’ by metis_tac[] >>
  ‘pend w g’ by (‘rdy lfd w g’ by metis_tac[] >> pop_assum mp_tac >> PURE_REWRITE_TAC [rdy_def] >> rw[]) >>
  drule_all sys_recv_ok >> strip_tac >> simp[] >>
  ‘wa.fd_limit = w.fd_limit’
    by (qpat_x_assum ‘sys_recv _ _ _ = _’ mp_tac >> simp[sys_recv_def] >> strip_tac >>
        imp_res_tac l0_do_env) >>
  drule_all (el 3 (CONJUNCTS sys_winv)) >> strip_tac >>
  ‘∃c. ALOOKUP w.open_fds g = SOME c’ by metis_tac[] >>
  drule_all kinv_sys_recv >> strip_tac
  >- ((* EOF *)
      gvs[] >> last_x_assum drule >> disch_then drule >>
      impl_tac >- (
        simp[] >> rpt conj_tac >>
        TRY (rpt strip_tac >> ‘g' ≠ g’ by (strip_tac >> gvs[wants_input_def]) >>
             ‘wants_input lfd hw ps g'’ by metis_tac[wants_input_other] >>
             irule rdy_sys_recv >> metis_tac[] >> NO_TAC) >>
        TRY (metis_tac[wants_input_other] >> NO_TAC) >>
        metis_tac[]) >>
      simp[])
  >- gvs[]
  >> (* data *)
  gvs[] >> last_x_assum drule >> disch_then drule >>
  impl_tac >- (
    simp[] >> rpt conj_tac >>
    TRY (rpt strip_tac >> ‘g' ≠ g’ by (strip_tac >> gvs[wants_input_def]) >>
         ‘wants_input lfd hw ps g'’ by metis_tac[wants_input_other] >>
         irule rdy_sys_recv >> metis_tac[] >> NO_TAC) >>
    TRY (metis_tac[wants_input_other] >> NO_TAC) >>
    metis_tac[]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   L1's fds are never reserved: they all came from accepts, of fds not in
   use, and the reserved fds only shrink
   ------------------------------------------------------------------------ *)

Theorem deliver_reserved[simp]:
  (l0_deliver w a).reserved = w.reserved
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_reserved[simp]:
  ∀as w. (FOLDL l0_deliver w as).reserved = w.reserved
Proof
  Induct >> simp[]
QED

Theorem ticks_reserved[simp]:
  ∀k w. (l0_tick nm w).reserved = w.reserved ∧ (l0_ticks nm k w).reserved = w.reserved
Proof
  Induct >> simp[l0_ticks_def, l0_tick_def]
QED

Theorem FOLDL_upd_reserved[simp]:
  ∀q w0. (FOLDL (λw j. upd_lchan j g w) w0 q).reserved = w0.reserved
Proof
  Induct >> simp[] >> simp[upd_lchan_def]
QED

Theorem ops_reserved:
  (l0_accept l w = (r, w') ⇒ w'.reserved = w.reserved) ∧
  (l0_recv f n w = (r, d, w') ⇒ w'.reserved = w.reserved) ∧
  (l0_send f bs w = (r, w') ⇒ w'.reserved = w.reserved) ∧
  (l0_close f w = (r, w') ⇒ ∀g. MEM g w'.reserved ⇒ MEM g w.reserved)
Proof
  rpt conj_tac
  >- (simp[l0_accept_def] >> rpt (CASE_TAC >> gvs[]) >> rw[] >> gvs[upd_lchan_def])
  >- (rw[l0_recv_def, AllCaseEqs()] >> gvs[upd_lchan_def])
  >- (rw[l0_send_def, AllCaseEqs()] >> gvs[upd_lchan_def])
  >> rw[l0_close_def, close_fd_def, AllCaseEqs()] >> gvs[upd_lchan_def, MEM_FILTER]
QED

Theorem l0_do_reserved:
  l0_do n conf alen w = SOME (out, w', ev) ∧
  (n = «sys_poll» ∨ n = «sys_send» ∨ n = «sys_recv» ∨ n = «sys_accept» ∨ n = «sys_close») ⇒
  ∀g. MEM g w'.reserved ⇒ MEM g w.reserved
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  gvs[l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac ops_reserved >> gvs[]
QED

Theorem sys_reserved:
  (sys_poll fes w = SOME (out, w', ev) ⇒ ∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ ∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
  (sys_recv f n w = SOME (out, w', ev) ⇒ ∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
  (sys_accept f w = SOME (out, w', ev) ⇒ ∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
  (sys_close f w = SOME (out, w', ev) ⇒ ∀g. MEM g w'.reserved ⇒ MEM g w.reserved)
Proof
  rw[sys_poll_def, sys_send_def, sys_recv_def, sys_accept_def, sys_close_def] >>
  drule l0_do_reserved >> simp[]
QED

Theorem sys_close_env:
  sys_close f w = SOME (out, w', ev) ⇒ w'.fd_limit = w.fd_limit
Proof
  rw[sys_close_def] >> imp_res_tac l0_do_env
QED

(* The fds L1's state holds *)
Definition ufds_def:
  ufds (ps : l1p) f ⇔
    MEM f (MAP FST ps.b.outbox) ∨ MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq
End

Definition nores_def:
  nores (ps : l1p) (w : l0world) ⇔ ∀f. ufds ps f ⇒ ¬MEM f w.reserved
End

Theorem nores_mono2:
  nores ps w ∧ (∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
  (∀f. ufds ps' f ⇒ ufds ps f ∨ ¬MEM f w'.reserved) ⇒
  nores ps' w'
Proof
  rw[nores_def] >> metis_tac[]
QED

Theorem nores_mono:
  nores ps w ∧ (∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧ (∀f. ufds ps' f ⇒ ufds ps f) ⇒
  nores ps' w'
Proof
  rw[nores_def] >> metis_tac[]
QED

Theorem set_outbox_keys:
  MEM g (MAP FST (set_outbox f bs st).outbox) ⇒ MEM g (MAP FST st.outbox) ∨ g = f
Proof
  rw[set_outbox_def, MEM_FST_ADELKEY] >> gvs[MEM_FST_ADELKEY]
QED

Theorem forget_keys:
  (MEM g (MAP FST (forget f st).outbox) ⇒ MEM g (MAP FST st.outbox)) ∧
  (forget f st).tbl = st.tbl ∧ (MEM g (forget f st).closing ⇒ MEM g st.closing)
Proof
  rw[forget_def, set_outbox_def, MEM_FST_ADELKEY, MEM_FILTER] >> gvs[MEM_FST_ADELKEY]
QED

Theorem after_send_keys:
  MEM g (MAP FST (after_send f r st).outbox) ⇒ MEM g (MAP FST st.outbox) ∨ g = f
Proof
  rw[after_send_def] >> every_case_tac >> gvs[] >> drule set_outbox_keys >> simp[]
QED

Theorem outbox_key:
  outbox_of st f ≠ [] ⇒ MEM f (MAP FST st.outbox)
Proof
  rw[outbox_of_def] >> every_case_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
  simp[MEM_MAP] >> metis_tac[FST]
QED

(* Readiness survives polls and sends *)
Theorem rdy_sys_poll:
  winv w ∧ rdy lfd w g ∧ sys_poll fes w = SOME (out, w', ev) ⇒ rdy lfd w' g
Proof
  rw[rdy_def, sys_poll_def]
  >- (drule_at (Pos last) qof_do >> simp[] >> disch_then (qspec_then ‘g’ strip_assume_tac) >>
      simp[])
  >> drule_at (Pos last) pend_do >> simp[] >> disch_then irule >> simp[]
QED

Theorem rdy_sys_send:
  winv w ∧ rdy lfd w g ∧ sys_send f bs w = SOME (out, w', ev) ⇒ rdy lfd w' g
Proof
  rw[rdy_def, sys_send_def]
  >- (drule_at (Pos last) qof_do >> simp[] >> disch_then (qspec_then ‘g’ strip_assume_tac) >>
      simp[])
  >> drule_at (Pos last) pend_do >> simp[] >> disch_then irule >> simp[]
QED

Theorem sys_poll_env:
  sys_poll fes w = SOME (out, w', ev) ⇒ w'.fd_limit = w.fd_limit ∧ l0_used w' = l0_used w
Proof
  rw[sys_poll_def] >> imp_res_tac l0_do_env >> drule l0_do_used >> simp[]
QED

Theorem sys_send_env:
  sys_send f bs w = SOME (out, w', ev) ⇒ w'.fd_limit = w.fd_limit ∧ l0_used w' = l0_used w
Proof
  rw[sys_send_def] >> imp_res_tac l0_do_env >> drule l0_do_used >> simp[]
QED

(* One action of the server *)
Theorem pdo_ok:
  pdo lfd (w, ps) act = SOME (r, (w', ps'), evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ pown lfd ps ∧ nores ps w ⇒
  EVERY (ok_ev lfd) evs ∧ nores ps' w' ∧ w'.fd_limit = w.fd_limit ∧
  ∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)
Proof
  Cases_on ‘act’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept *)
      gvs[AllCaseEqs()] >> irule nores_mono >> qexistsl_tac [‘ps’, ‘w’] >>
      simp[ufds_def] >> metis_tac[MEM])
  >- ((* Read *)
      qpat_x_assum ‘option_CASE _ _ _ = _’ mp_tac >>
      Cases_on ‘ALOOKUP ps.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
      rename1 ‘ALOOKUP ps.b.tbl c = SOME f’ >>
      ‘MEM f (MAP SND ps.b.tbl)’ by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[] >> irule nores_mono >> qexistsl_tac [‘ps’, ‘w’] >>
          simp[ufds_def]) >>
      reverse IF_CASES_TAC >- (strip_tac >> gvs[]) >>
      IF_CASES_TAC
      >- (simp[l1_close_def] >> Cases_on ‘sys_close f w’ >> simp[] >>
          rename1 ‘sys_close f w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
          strip_tac >> rveq >>
          drule_all sys_close_ok >> strip_tac >> simp[] >>
          imp_res_tac sys_close_env >> simp[] >>
          irule nores_mono >> qexistsl_tac [‘ps’, ‘w’] >>
          conj_tac >- metis_tac[sys_reserved] >>
          rw[ufds_def] >> gvs[forget_def, set_outbox_def, MEM_FST_ADELKEY, MEM_FILTER] >>
          imp_res_tac MEM_SND_ADELKEY_sub >> simp[])
      >> strip_tac >> gvs[] >> irule nores_mono >> qexistsl_tac [‘ps’, ‘w’] >>
      rw[ufds_def] >> gvs[MEM_FILTER] >> imp_res_tac MEM_SND_ADELKEY_sub >> simp[])
  >> (* Write *)
  PairCases_on ‘z’ >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >>
  simp[l1do_def] >> Cases_on ‘ALOOKUP ps.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
  rename1 ‘ALOOKUP ps.b.tbl c = SOME f’ >>
  ‘MEM f (MAP SND ps.b.tbl)’ by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> irule nores_mono >> qexistsl_tac [‘ps’, ‘w’] >>
      rw[ufds_def] >> imp_res_tac set_outbox_keys >> gvs[set_outbox_def] >> metis_tac[]) >>
  Cases_on ‘sys_send f l w’ >> simp[] >>
  rename1 ‘sys_send f l w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  strip_tac >> rveq >>
  ‘f ≠ lfd’ by (fs[pown_def] >> strip_tac >> gvs[]) >>
  ‘¬MEM f w.reserved’ by fs[nores_def, ufds_def] >>
  drule_all sys_send_ok >> strip_tac >> simp[] >>
  imp_res_tac sys_send_env >> simp[] >>
  irule nores_mono >> qexistsl_tac [‘ps’, ‘w’] >>
  conj_tac >- metis_tac[sys_reserved] >>
  rw[ufds_def] >> imp_res_tac after_send_keys >> gvs[] >> imp_res_tac set_outbox_keys >>
  gvs[after_send_def, set_outbox_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem pacts_ok:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ pv_rel lfd cm0 ps s ∧ pown lfd ps ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
    chown ps w ∧ eown E ps w ∧ nores ps w ⇒
    EVERY (ok_ev lfd) evs ∧ nores ps' w' ∧ w'.fd_limit = w.fd_limit ∧
    ∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all pdo_hdo >> strip_tac >>
  drule_all pdo_kinv >> strip_tac >>
  drule_all pdo_ok >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_polls_ok:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    sched_wf2 (sk_of p lfd sched w1) ∧ (∀c. MEM c chs ⇒ EVERY (λ(f, e). e < 256) c) ⇒
    EVERY (ok_ev lfd) evs ∧ l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧
    (∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
    (∀g. rdy lfd w g ⇒ rdy lfd w' g) ∧
    ∀f. MEM f (readable_fds rv) ∧ (f = lfd ∨ ∃c. ALOOKUP w.open_fds f = SOME c) ⇒
        rdy lfd w' f
Proof
  Induct >> simp[l1_polls_def, readable_fds_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >>
  rename1 ‘sys_poll fes w = SOME (out, wa, ev)’ >>
  drule_all sys_poll_rdy >> strip_tac >>
  ‘winv wa’ by metis_tac[sys_winv] >>
  drule sys_poll_env >> strip_tac >>
  ‘∀g. MEM g wa.reserved ⇒ MEM g w.reserved’ by metis_tac[sys_reserved] >>
  first_x_assum drule_all >> strip_tac >> gvs[readable_fds_def] >>
  rpt conj_tac
  >- metis_tac[rdy_sys_poll]
  >> gvs[FILTER_APPEND] >> rpt strip_tac >> gvs[readable_fds_def] >> metis_tac[]
QED

Theorem l1_flush_ok:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    sched_wf2 (sk_of p lfd sched w1) ∧ noob lfd st ∧
    (∀f. MEM f (MAP FST st.outbox) ⇒ ¬MEM f w.reserved) ⇒
    EVERY (ok_ev lfd) evs ∧ l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧
    (∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
    (∀f. MEM f (MAP FST st'.outbox) ⇒ MEM f (MAP FST st.outbox)) ∧
    (∀g. rdy lfd w g ⇒ rdy lfd w' g)
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_send _ _ w = SOME (out, wa, ev)’ >>
  ‘MEM h (MAP FST st.outbox)’ by metis_tac[outbox_key] >>
  ‘h ≠ lfd’ by (strip_tac >> gvs[noob_outbox]) >>
  ‘¬MEM h w.reserved’ by metis_tac[] >>
  drule_all sys_send_ok >> strip_tac >>
  ‘kinv p lfd sched w1 a cm D E wa’ by metis_tac[kinv_sys_quiet] >>
  ‘winv wa’ by metis_tac[sys_winv] >>
  drule sys_send_env >> strip_tac >>
  ‘∀g. MEM g wa.reserved ⇒ MEM g w.reserved’ by metis_tac[sys_reserved] >>
  first_x_assum (qspecl_then [‘wa’, ‘after_send h (l0_res_of out) st’, ‘w'’, ‘st'’, ‘evs'’]
                  mp_tac) >>
  impl_tac
  >- (simp[noob_after_send] >> rpt strip_tac >> imp_res_tac after_send_keys >> gvs[] >>
      metis_tac[]) >>
  strip_tac >> simp[] >>
  ‘∀f. MEM f (MAP FST st'.outbox) ⇒ MEM f (MAP FST st.outbox)’
    by (rpt strip_tac >> res_tac >> imp_res_tac after_send_keys >> gvs[]) >>
  ‘∀g. rdy lfd w g ⇒ rdy lfd w' g’ by metis_tac[rdy_sys_send] >>
  simp[] >> metis_tac[]
QED

Theorem pf_fetch_reserved:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    ∀g. MEM g w'.reserved ⇒ MEM g w.reserved
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[]
  >- (first_x_assum drule >> simp[])
  >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> metis_tac[sys_reserved]
QED

Theorem l1_reap_keys:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒
    (∀f. MEM f (MAP FST st'.outbox) ⇒ MEM f (MAP FST st.outbox)) ∧
    (∀g. MEM g w'.reserved ⇒ MEM g w.reserved) ∧
    st'.tbl = st.tbl ∧ (∀f. MEM f st'.closing ⇒ MEM f st.closing)
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs(), l1_close_def] >> first_x_assum drule >> strip_tac >>
      imp_res_tac sys_reserved >> metis_tac[forget_keys])
  >> first_x_assum drule >> simp[]
QED

Theorem l1_reap_ok:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    sched_wf2 (sk_of p lfd sched w1) ∧ ¬MEM lfd fs ∧
    (∀f c. MEM f fs ∧ ALOOKUP w.open_fds f = SOME c ⇒ E c) ⇒
    EVERY (ok_ev lfd) evs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs(), l1_close_def] >>
      rename1 ‘sys_close h w = SOME (out, wa, ev)’ >>
      drule_all sys_close_ok >> strip_tac >> simp[] >>
      ‘kinv p lfd sched w1 a cm D E wa’ by (irule kinv_sys_close >> fs[] >> metis_tac[]) >>
      ‘winv wa’ by metis_tac[sys_winv] >>
      first_x_assum drule >> disch_then irule >> simp[] >> rpt strip_tac >>
      drule_all sys_close_open_back >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> first_x_assum drule >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem l1_flush_b:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ st'.tbl = st.tbl ∧ st'.closing = st.closing
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> first_x_assum drule >>
  simp[after_send_def, set_outbox_def] >> every_case_tac >> simp[]
QED

Theorem CARD_set_sub:
  (∀g. MEM g l ⇒ MEM g l') ⇒ CARD (set l) ≤ CARD (set l')
Proof
  strip_tac >> irule CARD_SUBSET >> simp[SUBSET_DEF]
QED

(* MAIN (G2): a round makes no retried call, and its accept (if any) does
   not fail, given room for one more fd at its start *)
Theorem pround_ok:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  pv_rel lfd cm0 ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ chown ps w ∧ eown E ps w ∧
  noob lfd ps.b ∧ nores ps w ∧ CARD (set (l0_used w)) < w.fd_limit ⇒
  EVERY (ok_ev lfd) evs ∧ nores ps' w'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_kinv) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_ok) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all pacts_noob >> strip_tac >>
  drule_all pacts_hacts >> strip_tac >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[winv_def] >>
  drule_all pacts_l0 >> strip_tac >>
  rename1 ‘l1_polls _ wa = SOME (rv, wb, pevs)’ >>
  qmatch_asmsub_abbrev_tac ‘l1_polls (poll_chunks fes) wa’ >>
  ‘∀c. MEM c (poll_chunks fes) ⇒ EVERY (λ(f, e). e < 256) c’
    by (qspec_then ‘fes’ mp_tac
          (ISPEC “λ(f:word64, e:num). e < 256” (Q.GEN ‘P’ poll_chunks_ok)) >>
        impl_tac >- simp[Abbr ‘fes’, pf_poll_set_lt] >>
        simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all l1_polls_kinv >> strip_tac >>
  drule_all l1_polls_ok >> strip_tac >>
  rename1 ‘l1_flush _ (wb, pa.b) = SOME ((wc, bc), fevs)’ >>
  drule_all l1_flush_kinv >> strip_tac >>
  ‘∀f. MEM f (MAP FST pa.b.outbox) ⇒ ¬MEM f wb.reserved’
    by (fs[nores_def, ufds_def] >> metis_tac[]) >>
  drule_all l1_flush_ok >> strip_tac >>
  drule l1_flush_b >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((wd, pd), log, gevs)’ >>
  qmatch_asmsub_abbrev_tac ‘pf_fetch _ _ fs _’ >>
  ‘∀g. MEM g fs ⇒ g = lfd ∨ ∃c. ALOOKUP wa.open_fds g = SOME c’
    by (rw[Abbr ‘fs’, MEM_FILTER] >> fs[Abbr ‘fes’] >> drule in_fds_poll_set >>
        strip_tac >> gvs[] >> fs[chown_def] >> metis_tac[]) >>
  ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wc.open_fds g = SOME c’ by metis_tac[] >>
  ‘∀g. MEM g fs ⇒ rdy lfd wc g’
    by (rw[] >> ‘MEM g (readable_fds rv)’ by fs[Abbr ‘fs’, MEM_FILTER] >> metis_tac[]) >>
  ‘CARD (set (l0_used wc)) < wc.fd_limit’
    by (‘CARD (set (l0_used wa)) ≤ CARD (set (l0_used w))’ by (irule CARD_set_sub >> simp[]) >>
        gvs[]) >>
  ‘EVERY (ok_ev lfd) gevs’
    by (irule pf_fetch_ok >> simp[] >> metis_tac[]) >>
  (* the reap *)
  ‘eown E (pa with b := bc) wc’ by (fs[eown_def] >> metis_tac[]) >>
  ‘eused (pa with b := bc) wc’
    by (simp[eused_def] >> rpt strip_tac
        >- (‘MEM f (MAP SND pa.b.tbl)’ by (fs[pown_def] >> metis_tac[]) >>
            ‘∃c. ALOOKUP wa.open_fds f = SOME c’ by fs[chown_def] >>
            gvs[] >> metis_tac[used_open_fds])
        >> gvs[l0own_def]) >>
  ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wc.open_fds g = SOME c’ by metis_tac[] >>
  drule_all kinv_fetch >> strip_tac >>
  drule_all pf_fetch_acq >> strip_tac >>
  drule pf_fetch_b >> strip_tac >>
  drule pf_fetch_reserved >> strip_tac >>
  rename1 ‘l1_reap _ (wd, _) = SOME ((we, be), cevs)’ >>
  ‘¬MEM lfd pd.b.closing’ by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  ‘∀f c. MEM f (hup_step (hup_fds rv) (outbox_of pa.b) log pd).b.closing ∧
         ALOOKUP wd.open_fds f = SOME c ⇒ (λj. E j ∨ MEM (Eof2 j) as) c’
    by (simp_tac std_ss [hup_step_fields] >> fs[eown_def] >> metis_tac[]) >>
  mp_tac (Q.SPECL [‘pd.b.closing’, ‘wd’,
                   ‘(hup_step (hup_fds rv) (outbox_of pa.b) log pd).b’, ‘we’, ‘be’, ‘cevs’]
          (Q.INST [‘E’ |-> ‘λj. E j ∨ MEM (Eof2 j) as’, ‘a’ |-> ‘a'’, ‘cm’ |-> ‘cm'’,
                   ‘D’ |-> ‘λj. D j ++ data_of j as’] l1_reap_ok)) >>
  impl_tac >- (simp[] >> gvs[] >> metis_tac[]) >> strip_tac >>
  drule l1_reap_keys >> strip_tac >>
  simp[] >>
  (* L1's fds after the round *)
  irule nores_mono2 >> qexistsl_tac [‘pa’, ‘wa’] >> simp[] >>
  ‘∀g. MEM g we.reserved ⇒ MEM g wa.reserved’ by metis_tac[] >> simp[] >>
  rw[ufds_def]
  >- (disj1_tac >> disj1_tac >>
      ‘MEM f (MAP FST (hup_step (hup_fds rv) (outbox_of pa.b) log pd).b.outbox)’ by metis_tac[] >>
      drule (cj 3 hup_step_outbox) >> gvs[])
  >- gvs[]
  >- (‘MEM f pd.b.closing’ by metis_tac[hup_step_fields] >> gvs[])
  >> qpat_x_assum ‘∀f. MEM f pd.acq ⇒ _’ (qspec_then ‘f’ mp_tac) >> gvs[] >>
  strip_tac >> simp[] >> disj2_tac >> strip_tac >>
  ‘MEM f wc.reserved’ by metis_tac[] >> gvs[l0_used_def]
QED

(* ------------------------------------------------------------------------
   The run: with room for one more fd at each round's start (a bound on
   the connections open at once, not on all connections), no call of the
   run is retried and no accept fails
   ------------------------------------------------------------------------ *)

Definition fds_room_def:
  fds_room lfd hw ifds m w1 ⇔
    ∀n. CARD (set (l0_used (rworld lfd hw ifds m w1 n))) < w1.fd_limit
End

Theorem run_ok_ev:
  simple_v2 p lfd sched w1 ∧ (∀h. ¬w1.ch.emfile_drops h) ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧ w1.open_fds = [] ∧
  run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64)) ∧
  fds_room lfd hw ifds m w1 ⇒
  ∀k. nores (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k) ∧
      EVERY (ok_ev lfd) (rrev lfd hw ifds m w1 k)
Proof
  strip_tac >>
  ‘MEM lfd (l0_used w1)’ by simp[l0_used_def] >>
  ‘∀k. rinv p lfd sched w1 hw ifds m k’ by metis_tac[rinv_run] >>
  ‘∀k. noob lfd (rstate lfd hw ifds m w1 k).b’ by metis_tac[noob_run] >>
  ‘∀k. (rworld lfd hw ifds m w1 k).fd_limit = w1.fd_limit’
    by (gen_tac >>
        qpat_assum ‘∀k. rinv _ _ _ _ _ _ _ k’
          (qspec_then ‘k’ (strip_assume_tac o
                            SIMP_RULE std_ss [rinv_def, kinv_def, simple_v2_def, simple0_def])) >>
        fs[simple_v2_def, simple0_def]) >>
  ‘∀k. nores (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k) ⇒
       EVERY (ok_ev lfd) (rrev lfd hw ifds m w1 k) ∧
       nores (rstate lfd hw ifds m w1 (SUC k)) (rworld lfd hw ifds m w1 (SUC k))’
    by (rpt strip_tac >>
        drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
        drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
        qpat_assum ‘∀k. rinv _ _ _ _ _ _ _ k’ (qspec_then ‘k’ mp_tac) >>
        simp_tac std_ss [rinv_def] >> strip_tac >>
        drule_then drule pround_ok >> simp[] >>
        disch_then (qspecl_then [‘s’, ‘cm’] mp_tac) >> simp[] >>
        fs[fds_room_def]) >>
  ‘∀k. nores (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k)’
    by (Induct >- simp[nores_def, ufds_def, rstate_def, prun_0, pinit_def, l1init_def] >>
        metis_tac[]) >>
  metis_tac[]
QED

Theorem revs_ok:
  run_ok lfd hw ifds m w1 ∧ (∀k. EVERY (ok_ev lfd) (rrev lfd hw ifds m w1 k)) ⇒
  ∀n. EVERY (ok_ev lfd) (revs lfd hw ifds m w1 n)
Proof
  strip_tac >> Induct >- simp[revs_def, prun_0] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >> simp[]
QED

(* So [F1] holds in simple worlds, and accepts do not fail *)
Theorem simple_F1:
  run_ok lfd hw ifds m w1 ∧ (∀k. EVERY (ok_ev lfd) (rrev lfd hw ifds m w1 k)) ⇒
  F1 lfd hw ifds m w1 ∧ ¬accepts_fail lfd hw ifds m w1
Proof
  strip_tac >> drule_all revs_ok >> strip_tac >> conj_tac
  >- (rw[F1_def, call_ok_at_def] >> first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
      qexists_tac ‘i'’ >> fs[call_at_def] >> conj_tac >- metis_tac[] >>
      qexists_tac ‘n’ >> simp[] >>
      first_x_assum (qspec_then ‘n’ mp_tac) >> simp[EVERY_EL, ok_ev_def])
  >> rw[accepts_fail_def] >> qexists_tac ‘0’ >> rpt strip_tac >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[EVERY_EL, ok_ev_def] >> metis_tac[]
QED

(* ========================================================================
   G3. Every connection the kernel queued is eventually accepted
   ======================================================================== *)

Theorem rinv_sinv:
  rinv p lfd sched w1 hw ifds m k ⇒
  ∃s. sinv lfd p (SND (pcm lfd hw ifds m w1 k)) (FST (pcm lfd hw ifds m w1 k))
           (λj. data_of j (upto (parr lfd hw ifds m w1) k))
           (λj. MEM (Eof2 j) (upto (parr lfd hw ifds m w1) k)) s (rworld lfd hw ifds m w1 k)
Proof
  rw[rinv_def, kinv_def] >> metis_tac[]
QED

Theorem conns_caught_up:
  simple_v2 p lfd sched w1 ∧ (∀h. ¬w1.ch.emfile_drops h) ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧ w1.open_fds = [] ∧
  run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64)) ∧
  fds_room lfd hw ifds m w1 ∧ S1 lfd hw ifds m w1 ∧ S2 lfd hw ifds m w1 ⇒
  ∀N. ∃k. LENGTH (rworld lfd hw ifds m w1 N).chans ≤ SND (pcm lfd hw ifds m w1 k)
Proof
  rpt strip_tac >>
  drule_all rinv_run >> strip_tac >>
  drule_all run_ok_ev >> strip_tac >>
  ‘F1 lfd hw ifds m w1 ∧ ¬accepts_fail lfd hw ifds m w1’ by metis_tac[simple_F1] >>
  qpat_assum ‘∀k. rinv _ _ _ _ _ _ _ k’ (qspec_then ‘N’ assume_tac) >>
  drule rinv_sinv >> strip_tac >>
  qabbrev_tac ‘L = LENGTH (rworld lfd hw ifds m w1 N).chans’ >>
  Cases_on ‘L ≤ SND (pcm lfd hw ifds m w1 N)’ >- metis_tac[] >>
  ‘MEM (L − 1) (qof (rworld lfd hw ifds m w1 N) lfd)’
    by (fs[sinv_def, lk_def, MEM_GENLIST, Abbr ‘L’] >>
        qexists_tac ‘LENGTH (rworld lfd hw ifds m w1 N).chans − 1 −
                     SND (pcm lfd hw ifds m w1 N)’ >> simp[]) >>
  ‘MEM lfd (l0_used w1) ∧ linv lfd w1’ by simp[l0_used_def, linv_def] >>
  drule_all live_conn >> strip_tac >> gvs[] >>
  qpat_assum ‘∀k. rinv _ _ _ _ _ _ _ k’ (qspec_then ‘SUC k’ assume_tac) >>
  drule rinv_sinv >> strip_tac >>
  fs[resolved_def]
  >- (qexists_tac ‘SUC k’ >> fs[sinv_def, lk_def] >> res_tac >> simp[])
  >> fs[sinv_def, wk_def] >>
  ‘wch (EL (L − 1) (rworld lfd hw ifds m w1 (SUC k)).chans)
       (EL (L − 1) s'.clients)’ by fs[] >>
  fs[wch_def]
QED

(* ========================================================================
   G4. L1 holds every open fd: in its handle table, its accepted queue, or
   its closing list
   ======================================================================== *)

Definition own_def:
  own (ps : l1p) (w : l0world) ⇔
    ∀f c. ALOOKUP w.open_fds f = SOME c ⇒
          MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.acq ∨ MEM f ps.b.closing
End

(* In simple worlds a close of an open fd closes it *)
Theorem sys_close_gone:
  kinv p lfd sched w1 a cm D E w ∧ ALOOKUP w.open_fds f = SOME c ∧
  sys_close f w = SOME (out, w', ev) ⇒ ALOOKUP w'.open_fds f = NONE
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >>
  drule_then (qspec_then ‘«sys_close»’ mp_tac) kinv_tick_clock >> simp[] >> strip_tac >>
  ‘∀h. w.ch.close_intr h = NONE’ by fs[kinv_def, simple_v2_def, simple0_def] >>
  drule_all sinv_open_chan >> strip_tac >>
  ‘MEM f (l0_used w)’ by metis_tac[used_open_fds] >>
  gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
  gvs[l0_close_def, close_fd_def, l0_chan_of_def, l0_used_def, AllCaseEqs(), ALOOKUP_ADELKEY,
      upd_lchan_def]
QED

Theorem MEM_SND_ADELKEY_other:
  ∀l. ALL_DISTINCT (MAP FST l) ∧ ALOOKUP l h = SOME f ∧ MEM g (MAP SND l) ∧ g ≠ f ⇒
      MEM g (MAP SND (ADELKEY h l))
Proof
  Induct >> simp[FORALL_PROD, ADELKEY_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), MEM_MAP, MEM_FILTER, EXISTS_PROD] >> rw[] >> gvs[] >>
  TRY (metis_tac[]) >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem pdo_own:
  pdo lfd (w, ps) act = SOME (r, (w', ps'), evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ pown lfd ps ∧ own ps w ⇒ own ps' w'
Proof
  Cases_on ‘act’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept *)
      gvs[AllCaseEqs()] >> fs[own_def] >> metis_tac[MEM])
  >- ((* Read *)
      qpat_x_assum ‘option_CASE _ _ _ = _’ mp_tac >>
      Cases_on ‘ALOOKUP ps.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
      rename1 ‘ALOOKUP ps.b.tbl c = SOME f’ >>
      IF_CASES_TAC >- (strip_tac >> gvs[own_def]) >>
      reverse IF_CASES_TAC >- (strip_tac >> gvs[]) >>
      ‘ALL_DISTINCT (MAP FST ps.b.tbl)’ by fs[pown_def] >>
      IF_CASES_TAC
      >- (simp[l1_close_def] >> Cases_on ‘sys_close f w’ >> simp[] >>
          rename1 ‘sys_close f w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
          strip_tac >> rveq >>
          simp[own_def] >> rpt strip_tac >>
          drule_all sys_close_open_back >> strip_tac >>
          ‘f' ≠ f’ by (strip_tac >> gvs[] >> drule_all sys_close_gone >> simp[]) >>
          ‘MEM f' (MAP SND ps.b.tbl) ∨ MEM f' ps.acq ∨ MEM f' ps.b.closing’ by metis_tac[own_def] >>
          gvs[forget_def, set_outbox_def, MEM_FILTER] >> metis_tac[MEM_SND_ADELKEY_other])
      >> strip_tac >> gvs[own_def, MEM_FILTER] >> rpt strip_tac >> res_tac >> gvs[] >>
      Cases_on ‘f' = f’ >> gvs[] >> metis_tac[MEM_SND_ADELKEY_other])
  >> (* Write *)
  PairCases_on ‘z’ >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >>
  simp[l1do_def] >> Cases_on ‘ALOOKUP ps.b.tbl c’ >> simp[] >- (strip_tac >> gvs[]) >>
  rename1 ‘ALOOKUP ps.b.tbl c = SOME f’ >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >- (strip_tac >> gvs[own_def, set_outbox_def]) >>
  Cases_on ‘sys_send f l w’ >> simp[] >>
  rename1 ‘sys_send f l w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  strip_tac >> rveq >>
  drule (CONJUNCT2 sys_quiet_open) >> strip_tac >>
  gvs[own_def, after_send_def, set_outbox_def] >> every_case_tac >> gvs[]
QED

Theorem pacts_own:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ pv_rel lfd cm0 ps s ∧ pown lfd ps ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
    chown ps w ∧ eown E ps w ∧ own ps w ⇒
    own ps' w'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all pdo_hdo >> strip_tac >>
  drule_all pdo_kinv >> strip_tac >>
  drule_all pdo_own >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem own_same:
  own ps w ∧ ps'.b = ps.b ∧ ps'.acq = ps.acq ∧ w'.open_fds = w.open_fds ⇒ own ps' w'
Proof
  rw[own_def]
QED

Theorem pf_fetch_own:
  ∀fs w ps w' ps' log evs a cm D E.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    (∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP w.open_fds g = SOME c) ∧ own ps w ⇒
    own ps' w'
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> simp[Once pf_fetch_def] >>
  reverse (Cases_on ‘wants_input lfd hw ps g’) >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      disch_then (qspecl_then [‘a’, ‘cm’, ‘D’, ‘E’] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  IF_CASES_TAC
  >- ((* an accept *)
      pop_assum SUBST_ALL_TAC >> strip_tac >>
      qpat_x_assum ‘option_CASE (sys_accept _ _) _ _ = _’ mp_tac >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, wa, ev)’ >>
      pairarg_tac >> simp[] >>
      Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
      rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
      strip_tac >> rveq >>
      drule_all (el 4 (CONJUNCTS sys_winv)) >> strip_tac >>
      drule_all kinv_sys_accept >> strip_tac
      >- (‘ps1.b = ps.b ∧ ps1.acq = ps.acq’
            by (Cases_on ‘l0_res_of out’ >> fs[] >> rw[] >> fs[]) >>
          ‘own ps1 wa’
            by (irule own_same >> qexistsl_tac [‘ps’, ‘w’] >> rpt conj_tac >>
                first_assum ACCEPT_TAC) >>
          ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wa.open_fds g = SOME c’
            by (qpat_x_assum ‘wa.open_fds = _’ (fn th => rewrite_tac[th]) >> metis_tac[]) >>
          last_x_assum drule >> disch_then drule >> impl_tac >- fs[] >>
          simp[])
      >> ‘ps1.b = ps.b ∧ ps1.acq = ps.acq ++ [n2w k]’ by (fs[] >> rw[]) >>
      ‘own ps1 wa’ by (fs[own_def] >> rw[] >> res_tac >> simp[]) >>
      ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wa.open_fds g = SOME c’
        by (rpt strip_tac >> res_tac >> simp[] >> rw[]) >>
      last_x_assum drule >> disch_then drule >> impl_tac >- fs[] >>
      simp[])
  >> (* a recv *)
  strip_tac >>
  qpat_x_assum ‘option_CASE (sys_recv _ _ _) _ _ = _’ mp_tac >>
  Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME (out, wa, ev)’ >>
  pairarg_tac >> simp[] >>
  Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
  rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
  strip_tac >> rveq >>
  drule_all (el 3 (CONJUNCTS sys_winv)) >> strip_tac >>
  ‘∃c. ALOOKUP w.open_fds g = SOME c’ by metis_tac[] >>
  drule_all kinv_sys_recv >> strip_tac >>
  ‘ps1.b = ps.b ∧ ps1.acq = ps.acq’ by gvs[] >>
  ‘own ps1 wa’
    by (irule own_same >> qexistsl_tac [‘ps’, ‘w’] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wa.open_fds g = SOME c’
    by (qpat_x_assum ‘wa.open_fds = _’ (fn th => rewrite_tac[th]) >> metis_tac[]) >>
  last_x_assum drule >> disch_then drule >> impl_tac >- fs[] >>
  simp[]
QED

Definition ownb_def:
  ownb acq (st : l1st) (w : l0world) ⇔
    ∀f c. ALOOKUP w.open_fds f = SOME c ⇒
          MEM f (MAP SND st.tbl) ∨ MEM f acq ∨ MEM f st.closing
End

Theorem own_ownb:
  own ps w ⇔ ownb ps.acq ps.b w
Proof
  simp[own_def, ownb_def]
QED

Theorem l1_reap_own:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    sched_wf2 (sk_of p lfd sched w1) ∧ ¬MEM lfd fs ∧
    (∀f c. MEM f fs ∧ ALOOKUP w.open_fds f = SOME c ⇒ E c) ∧ ownb acq st w ⇒
    ownb acq st' w'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >>
  IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs(), l1_close_def] >>
      rename1 ‘sys_close h w = SOME (out, wa, ev)’ >>
      ‘kinv p lfd sched w1 a cm D E wa’ by (irule kinv_sys_close >> fs[] >> metis_tac[]) >>
      ‘winv wa’ by metis_tac[sys_winv] >>
      first_x_assum drule >> disch_then irule >> simp[] >> rpt conj_tac
      >- (rpt strip_tac >> drule_all sys_close_open_back >> strip_tac >>
          first_x_assum irule >> simp[] >> metis_tac[])
      >> simp[ownb_def] >> rpt strip_tac >> drule_all sys_close_open_back >> strip_tac >>
      ‘f ≠ h’ by (strip_tac >> gvs[] >> drule_all sys_close_gone >> simp[]) >>
      fs[ownb_def] >> res_tac >> gvs[forget_def, set_outbox_def, MEM_FILTER])
  >> first_x_assum drule >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem own_same2:
  own ps w ∧ ps'.b.tbl = ps.b.tbl ∧ ps'.b.closing = ps.b.closing ∧ ps'.acq = ps.acq ∧
  w'.open_fds = w.open_fds ⇒ own ps' w'
Proof
  rw[own_def]
QED

Theorem pround_own:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  pv_rel lfd cm0 ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ chown ps w ∧ eown E ps w ∧
  own ps w ⇒
  own ps' w'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_kinv) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_own) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all pacts_hacts >> strip_tac >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[winv_def] >>
  drule_all pacts_l0 >> strip_tac >>
  rename1 ‘l1_polls _ wa = SOME (rv, wb, pevs)’ >>
  drule_all l1_polls_kinv >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >>
  rename1 ‘l1_flush _ (wb, pa.b) = SOME ((wc, bc), fevs)’ >>
  drule_all l1_flush_kinv >> strip_tac >>
  ‘l0_rely wb’ by gvs[winv_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  drule l1_flush_b >> strip_tac >>
  ‘own (pa with b := bc) wc’ by (irule own_same2 >> qexistsl_tac [‘pa’, ‘wa’] >> simp[]) >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((wd, pd), log, gevs)’ >>
  qmatch_asmsub_abbrev_tac ‘pf_fetch _ _ fs _’ >>
  ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wc.open_fds g = SOME c’
    by (rw[Abbr ‘fs’, MEM_FILTER] >> drule in_fds_poll_set >> strip_tac >> gvs[] >>
        fs[chown_def] >> metis_tac[]) >>
  drule_all pf_fetch_own >> strip_tac >>
  ‘eown E (pa with b := bc) wc’ by (fs[eown_def] >> metis_tac[]) >>
  ‘eused (pa with b := bc) wc’
    by (simp[eused_def] >> rpt strip_tac
        >- (‘MEM f (MAP SND pa.b.tbl)’ by (fs[pown_def] >> metis_tac[]) >>
            ‘∃c. ALOOKUP wa.open_fds f = SOME c’ by fs[chown_def] >>
            gvs[] >> metis_tac[used_open_fds])
        >> gvs[l0own_def]) >>
  drule_all kinv_fetch >> strip_tac >>
  drule pf_fetch_b >> strip_tac >>
  rename1 ‘l1_reap _ (wd, _) = SOME ((we, be), cevs)’ >>
  ‘¬MEM lfd pd.b.closing’ by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  ‘∀f c. MEM f (hup_step (hup_fds rv) (outbox_of pa.b) log pd).b.closing ∧
         ALOOKUP wd.open_fds f = SOME c ⇒ (λj. E j ∨ MEM (Eof2 j) as) c’
    by (simp_tac std_ss [hup_step_fields] >> fs[eown_def] >> metis_tac[]) >>
  mp_tac (Q.SPECL [‘pd.b.closing’, ‘wd’,
                   ‘(hup_step (hup_fds rv) (outbox_of pa.b) log pd).b’, ‘we’, ‘be’, ‘cevs’]
          (Q.INST [‘E’ |-> ‘λj. E j ∨ MEM (Eof2 j) as’, ‘a’ |-> ‘a'’, ‘cm’ |-> ‘cm'’,
                   ‘D’ |-> ‘λj. D j ++ data_of j as’, ‘acq’ |-> ‘pd.acq’] l1_reap_own)) >>
  impl_tac
  >- (simp[] >> gvs[] >> conj_tac >- metis_tac[] >>
      qpat_x_assum ‘own pd wd’ mp_tac >> simp[own_def, ownb_def]) >>
  simp[own_def, ownb_def]
QED

Theorem own_run:
  simple_v2 p lfd sched w1 ∧ (∀h. ¬w1.ch.emfile_drops h) ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧ w1.open_fds = [] ∧
  run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64)) ⇒
  ∀k. own (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k)
Proof
  strip_tac >> ‘MEM lfd (l0_used w1)’ by simp[l0_used_def] >>
  ‘∀k. rinv p lfd sched w1 hw ifds m k’ by metis_tac[rinv_run] >>
  Induct >- simp[own_def, rstate_def, rworld_def, prun_0, pinit_def, l1init_def] >>
  drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  qpat_assum ‘∀k. rinv _ _ _ _ _ _ _ k’ (qspec_then ‘k’ mp_tac) >>
  simp_tac std_ss [rinv_def] >> strip_tac >>
  drule_then drule pround_own >> simp[] >>
  disch_then (qspecl_then [‘s’, ‘cm’] mp_tac) >> simp[]
QED

(* ========================================================================
   G5. The link: within a round, an open fd's fetched data and EOF are its
   client's data and EOF in psk's step
   ======================================================================== *)

Theorem data_of_cons:
  data_of j (Data2 c bs :: l) = (if c = j then bs else []) ++ data_of j l ∧
  data_of j (Eof2 c :: l) = data_of j l ∧ data_of j (Connect2 x :: l) = data_of j l
Proof
  simp[data_of_def]
QED

Theorem pf_fetch_link:
  ∀fs w ps w' ps' log evs a cm D E as cm' a'.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧
    (∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP w.open_fds g = SOME c) ∧
    ALOOKUP w.open_fds f = SOME c ∧ arrs lfd (cm, a) log = (as, (cm', a')) ⇒
    data_of c as = fdata f log ∧ (MEM (Eof2 c) as ⇔ fend f log) ∧
    (∀bs. MEM (FData f bs) log ⇒ bs ≠ []) ∧ ALOOKUP w'.open_fds f = SOME c
Proof
  Induct
  >- (simp[pf_fetch_def] >> rpt strip_tac >> gvs[arrs_def]) >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> simp[Once pf_fetch_def] >>
  reverse (Cases_on ‘wants_input lfd hw ps g’) >> simp[]
  >- (strip_tac >> last_x_assum drule >> disch_then drule >> simp[] >>
      disch_then irule >> metis_tac[]) >>
  IF_CASES_TAC
  >- ((* an accept *)
      pop_assum SUBST_ALL_TAC >> strip_tac >>
      qpat_x_assum ‘option_CASE (sys_accept _ _) _ _ = _’ mp_tac >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, wa, ev)’ >>
      pairarg_tac >> simp[] >>
      Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
      rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
      strip_tac >> rveq >>
      drule_all (el 4 (CONJUNCTS sys_winv)) >> strip_tac >>
      ‘MEM f (l0_used w)’ by metis_tac[used_open_fds] >>
      drule_all kinv_sys_accept >> strip_tac
      >- (‘fl' = []’ by (Cases_on ‘l0_res_of out’ >> fs[] >> rw[] >> fs[]) >>
          gvs[] >> last_x_assum drule >> disch_then drule >> simp[] >>
          TRY (impl_tac >- metis_tac[] >> simp[]))
      >> ‘fl' = [FConn (n2w k)]’ by (fs[] >> rw[]) >>
      gvs[arrs_def] >> pairarg_tac >> gvs[data_of_cons] >>
      ‘n2w k ≠ f’ by (strip_tac >> gvs[]) >>
      last_x_assum drule >> disch_then drule >> simp[] >>
      impl_tac >- (rw[] >> metis_tac[]) >> simp[])
  >> (* a recv *)
  strip_tac >>
  qpat_x_assum ‘option_CASE (sys_recv _ _ _) _ _ = _’ mp_tac >>
  Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
  rename1 ‘sys_recv g pf_chunk w = SOME (out, wa, ev)’ >>
  pairarg_tac >> simp[] >>
  Cases_on ‘pf_fetch lfd hw fs (wa, ps1)’ >> simp[] >>
  rename1 ‘pf_fetch lfd hw fs (wa, ps1) = SOME y’ >> PairCases_on ‘y’ >> simp[] >>
  strip_tac >> rveq >>
  drule_all (el 3 (CONJUNCTS sys_winv)) >> strip_tac >>
  ‘∃cg. ALOOKUP w.open_fds g = SOME cg’ by metis_tac[] >>
  drule_all kinv_cl >> strip_tac >>
  ‘(cg = c ⇔ g = f)’
    by (eq_tac >> rw[] >> gvs[] >>
        qpat_x_assum ‘kinv _ _ _ _ _ _ _ _ _’ mp_tac >>
        simp[kinv_def, sinv_def, lk_def] >> metis_tac[]) >>
  drule_all kinv_sys_recv >> strip_tac
  >- ((* EOF *)
      ‘fl' = [FEof g]’ by fs[] >>
      ‘kinv p lfd sched w1 a cm D ((cl cm g =+ T) E) wa’ by (irule kinv_E >> fs[]) >>
      gvs[arrs_def] >> pairarg_tac >> gvs[data_of_cons] >>
      last_x_assum drule >> disch_then drule >> simp[] >>
      TRY (impl_tac >- metis_tac[]) >> strip_tac >> simp[] >> metis_tac[])
  >- ((* a retried failure *)
      ‘fl' = []’ by (Cases_on ‘l0_res_of out’ >> fs[]) >>
      gvs[] >> last_x_assum drule >> disch_then drule >> simp[] >>
      TRY (impl_tac >- metis_tac[] >> simp[]))
  >> (* data *)
  ‘fl' = [FData g (TAKE k (DROP 13 out))]’ by (fs[] >> rw[]) >>
  gvs[arrs_def] >> pairarg_tac >> gvs[data_of_cons] >>
  last_x_assum drule >> disch_then drule >> simp[] >>
  TRY (impl_tac >- metis_tac[]) >> strip_tac >> simp[] >> rw[] >> gvs[]
QED

(* The server's actions close only fds whose EOF was fetched *)
Theorem pdo_keep:
  pdo lfd (w, ps) act = SOME (r, (w', ps'), evs) ∧ eown E ps w ∧
  ALOOKUP w.open_fds f = SOME c ∧ ¬E c ⇒ ALOOKUP w'.open_fds f = SOME c
Proof
  Cases_on ‘act’ >> simp[pdo_def] >> strip_tac
  >- gvs[AllCaseEqs()]
  >- (qpat_x_assum ‘option_CASE _ _ _ = _’ mp_tac >>
      Cases_on ‘ALOOKUP ps.b.tbl c'’ >> simp[] >- (strip_tac >> gvs[]) >>
      rename1 ‘ALOOKUP ps.b.tbl h = SOME g’ >>
      IF_CASES_TAC >- (strip_tac >> gvs[]) >>
      reverse IF_CASES_TAC >- (strip_tac >> gvs[]) >>
      IF_CASES_TAC
      >- (simp[l1_close_def] >> Cases_on ‘sys_close g w’ >> simp[] >>
          rename1 ‘sys_close g w = SOME z’ >> PairCases_on ‘z’ >> simp[] >>
          strip_tac >> rveq >>
          ‘g ≠ f’ by (strip_tac >> gvs[eown_def] >> metis_tac[]) >>
          metis_tac[sys_close_open])
      >> strip_tac >> gvs[])
  >> PairCases_on ‘z’ >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >>
  simp[l1do_def] >> rw[AllCaseEqs()] >> gvs[] >>
  drule (CONJUNCT2 sys_quiet_open) >> simp[]
QED

Theorem pacts_keep:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ pv_rel lfd cm0 ps s ∧ pown lfd ps ∧
    kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
    chown ps w ∧ eown E ps w ∧ ALOOKUP w.open_fds f = SOME c ∧ ¬E c ⇒
    ALOOKUP w'.open_fds f = SOME c
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all pdo_hdo >> strip_tac >>
  drule_all pdo_kinv >> strip_tac >>
  drule_all pdo_keep >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* MAIN (G5): a round, seen from an open fd whose EOF was not fetched *)
Theorem pround_link:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  pv_rel lfd cm0 ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ chown ps w ∧ eown E ps w ∧
  ALOOKUP w.open_fds f = SOME c ∧ ¬E c ∧ arrs lfd (cm, a) log = (as, (cm', a')) ⇒
  data_of c as = fdata f log ∧ (MEM (Eof2 c) as ⇔ fend f log) ∧
  (∀bs. MEM (FData f bs) log ⇒ bs ≠ []) ∧
  (ALOOKUP w'.open_fds f = SOME c ∨ MEM (Eof2 c) as)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_kinv) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_keep) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all pacts_hacts >> strip_tac >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[winv_def] >>
  drule_all pacts_l0 >> strip_tac >>
  rename1 ‘l1_polls _ wa = SOME (rv, wb, pevs)’ >>
  drule_all l1_polls_kinv >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >>
  rename1 ‘l1_flush _ (wb, pa.b) = SOME ((wc, bc), fevs)’ >>
  drule_all l1_flush_kinv >> strip_tac >>
  ‘l0_rely wb’ by gvs[winv_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((wd, pd), log, gevs)’ >>
  qmatch_asmsub_abbrev_tac ‘pf_fetch _ _ fs _’ >>
  ‘∀g. MEM g fs ∧ g ≠ lfd ⇒ ∃c. ALOOKUP wc.open_fds g = SOME c’
    by (rw[Abbr ‘fs’, MEM_FILTER] >> drule in_fds_poll_set >> strip_tac >> gvs[] >>
        fs[chown_def] >> metis_tac[]) >>
  ‘ALOOKUP wc.open_fds f = SOME c’ by gvs[] >>
  drule_all pf_fetch_link >> strip_tac >> simp[] >>
  ‘eown E (pa with b := bc) wc’ by (fs[eown_def] >> metis_tac[]) >>
  ‘eused (pa with b := bc) wc’
    by (simp[eused_def] >> rpt strip_tac
        >- (‘MEM f' (MAP SND pa.b.tbl)’ by (fs[pown_def] >> metis_tac[]) >>
            ‘∃c. ALOOKUP wa.open_fds f' = SOME c’ by fs[chown_def] >>
            gvs[] >> metis_tac[used_open_fds])
        >> gvs[l0own_def]) >>
  drule_all kinv_fetch >> strip_tac >> gvs[] >>
  drule pf_fetch_b >> strip_tac >>
  rename1 ‘l1_reap _ (wd, _) = SOME ((we, be), cevs)’ >>
  drule l1_reap_wkeep >> strip_tac >>
  Cases_on ‘MEM f pd.b.closing’
  >- (disj2_tac >> fs[eown_def] >> metis_tac[])
  >> disj1_tac >> fs[wkeep_def] >> first_x_assum irule >>
  simp[hup_step_fields] >> metis_tac[]
QED

(* The run's hypotheses for R2′ (simple worlds) *)
Definition simple_run_def:
  simple_run p lfd sched hw ifds m w1 ⇔
    simple_v2 p lfd sched w1 ∧ (∀h. ¬w1.ch.emfile_drops h) ∧ sched_wf2 (sk_of p lfd sched w1) ∧
    winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧ w1.open_fds = [] ∧
    run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64))
End

Theorem run_link:
  simple_run p lfd sched hw ifds m w1 ⇒
  ∀k f c.
    ALOOKUP (rworld lfd hw ifds m w1 k).open_fds f = SOME c ∧
    ¬MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k) ⇒
    data_of c (parr lfd hw ifds m w1 k) = fdata f (rlog lfd hw ifds m w1 k) ∧
    (MEM (Eof2 c) (parr lfd hw ifds m w1 k) ⇔ fend f (rlog lfd hw ifds m w1 k)) ∧
    (∀bs. MEM (FData f bs) (rlog lfd hw ifds m w1 k) ⇒ bs ≠ []) ∧
    (ALOOKUP (rworld lfd hw ifds m w1 (SUC k)).open_fds f = SOME c ∨
     MEM (Eof2 c) (parr lfd hw ifds m w1 k))
Proof
  strip_tac >> qpat_x_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  rpt gen_tac >> strip_tac >>
  ‘MEM lfd (l0_used w1)’ by simp[l0_used_def] >>
  drule_all rinv_run >> disch_then (qspec_then ‘k’ mp_tac) >>
  simp_tac std_ss [rinv_def] >> strip_tac >>
  drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule pcm_SUC >> disch_then (qspec_then ‘k’ assume_tac) >>
  Cases_on ‘pcm lfd hw ifds m w1 k’ >> Cases_on ‘pcm lfd hw ifds m w1 (SUC k)’ >> fs[] >>
  drule_then drule pround_link >> simp[] >>
  disch_then (qspecl_then [‘s’, ‘f’, ‘cm’, ‘c’] mp_tac) >> simp[]
QED

(* ========================================================================
   G6. An accepted fd gets a handle (the server accepts, S2, and L1's
   queue of accepted fds is first in, first out)
   ======================================================================== *)

(* The fds a fetch accepts were not in use when it started *)
Theorem pf_fetch_conns:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ⇒
    EVERY (λg. ¬MEM g (l0_used w)) (log_conns log)
Proof
  Induct >- simp[pf_fetch_def, log_conns_def] >>
  rpt gen_tac >> rename1 ‘h :: fs’ >> simp[Once pf_fetch_def] >>
  reverse (Cases_on ‘wants_input lfd hw ps h’) >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
      rename1 ‘sys_accept _ w = SOME (out, wa, ev)’ >>
      ‘winv wa’ by metis_tac[sys_winv] >>
      first_x_assum drule_all >> strip_tac >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used wa)’
        by (qpat_x_assum ‘sys_accept _ _ = _’ mp_tac >> simp[sys_accept_def] >>
            strip_tac >> drule l0_do_used >> simp[]) >>
      ‘l0_rely w ∧ fds_lt w’ by fs[winv_def] >>
      Cases_on ‘l0_res_of out’ >> gvs[log_conns_def, EVERY_MEM] >> rw[] >> gvs[] >>
      TRY (drule_all sys_accept_fresh >> simp[] >> NO_TAC) >>
      metis_tac[])
  >> strip_tac >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_recv _ _ w = SOME (out, wa, ev)’ >>
  ‘winv wa’ by metis_tac[sys_winv] >>
  first_x_assum drule_all >> strip_tac >>
  ‘l0_used wa = l0_used w’
    by (qpat_x_assum ‘sys_recv _ _ _ = _’ mp_tac >> simp[sys_recv_def] >>
        strip_tac >> drule l0_do_used >> simp[]) >>
  every_case_tac >> gvs[log_conns_def]
QED

(* A round accepts no fd that was open, with its EOF not fetched, when the
   round started *)
Theorem pround_fresh:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  kinv p lfd sched w1 a cm D E w ∧ winv w ∧ sched_wf2 (sk_of p lfd sched w1) ∧
  pv_rel lfd cm0 ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ chown ps w ∧ eown E ps w ∧
  ALOOKUP w.open_fds f = SOME c ∧ ¬E c ⇒
  ¬MEM f (log_conns log)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_kinv) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [‘acts’, ‘w’, ‘ps’, ‘s’, ‘rs’, ‘aevs’, ‘wa’, ‘pa’] pacts_keep) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 ‘l1_polls _ wa = SOME (rv, wb, pevs)’ >>
  drule_all l1_polls_kinv >> strip_tac >>
  rename1 ‘l1_flush _ (wb, pa.b) = SOME ((wc, bc), fevs)’ >>
  drule_all l1_flush_kinv >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((wd, pd), log, gevs)’ >>
  drule_all pf_fetch_conns >> strip_tac >>
  ‘MEM f (l0_used wc)’ by (irule used_open_fds >> gvs[] >> metis_tac[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem run_fresh:
  simple_run p lfd sched hw ifds m w1 ⇒
  ∀k f c.
    ALOOKUP (rworld lfd hw ifds m w1 k).open_fds f = SOME c ∧
    ¬MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k) ⇒
    ¬MEM f (log_conns (rlog lfd hw ifds m w1 k))
Proof
  strip_tac >>
  qpat_x_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  rpt gen_tac >> strip_tac >>
  ‘MEM lfd (l0_used w1)’ by simp[l0_used_def] >>
  drule_all rinv_run >> disch_then (qspec_then ‘k’ mp_tac) >>
  simp_tac std_ss [rinv_def] >> strip_tac >>
  drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule_then drule pround_fresh >> simp[] >>
  disch_then (qspecl_then [‘s’, ‘f’, ‘cm’, ‘c’] mp_tac) >> simp[]
QED

Theorem upto_mono:
  ∀d n. ∃l. upto g (n + d) = upto g n ++ l
Proof
  Induct >- (rw[] >> qexists_tac ‘[]’ >> simp[]) >>
  rpt gen_tac >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  qexists_tac ‘l ++ g (n + d)’ >> fs[ADD_CLAUSES, upto_SUC]
QED

Theorem upto_mem_mono:
  MEM x (upto g n) ∧ n ≤ n' ⇒ MEM x (upto g n')
Proof
  strip_tac >> qspecl_then [‘n' − n’, ‘n’] strip_assume_tac (Q.GEN ‘g’ upto_mono |> Q.SPEC ‘g’) >>
  ‘n + (n' − n) = n'’ by decide_tac >> gvs[]
QED

(* One round, seen from an accepted fd waiting for a handle *)
Theorem fifo_step:
  simple_run p lfd sched hw ifds m w1 ⇒
  ∀k f c pre post.
    (rstate lfd hw ifds m w1 k).acq = pre ++ f :: post ∧
    ALOOKUP (rworld lfd hw ifds m w1 k).open_fds f = SOME c ∧
    ¬MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k) ⇒
    MEM (Eof2 c) (upto (parr lfd hw ifds m w1) (SUC k)) ∨
    (ALOOKUP (rworld lfd hw ifds m w1 (SUC k)).open_fds f = SOME c ∧
     (MEM f (MAP SND (rstate lfd hw ifds m w1 (SUC k)).b.tbl) ∨
      ∃pre' post'. (rstate lfd hw ifds m w1 (SUC k)).acq = pre' ++ f :: post' ∧
                   LENGTH pre' ≤ LENGTH pre ∧
                   (MEM (Accept lfd) (new_actions (log_of m) (rhist lfd hw ifds m w1 k)) ⇒
                    LENGTH pre' < LENGTH pre)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule run_link >> disch_then drule_all >> strip_tac >>
  drule run_fresh >> disch_then drule_all >> strip_tac >>
  qpat_x_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  ‘MEM lfd (l0_used w1) ∧ linv lfd w1’ by simp[l0_used_def, linv_def] >>
  ‘∀k. own (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k)’
    by (drule_all own_run >> simp[]) >>
  ‘∀k. rinv p lfd sched w1 hw ifds m k’ by (drule_all rinv_run >> simp[]) >>
  drule_all run_lfd >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  simp[upto_SUC] >>
  reverse (Cases_on ‘MEM (Eof2 c) (parr lfd hw ifds m w1 k)’) >> simp[] >> gvs[] >>
  qpat_x_assum ‘∀k. rinv _ _ _ _ _ _ _ k’ (qspec_then ‘SUC k’ mp_tac) >>
  simp_tac std_ss [rinv_def, eown_def] >> strip_tac >>
  ‘¬MEM f (rstate lfd hw ifds m w1 (SUC k)).b.closing’
    by (strip_tac >> res_tac >> gvs[upto_SUC]) >>
  ‘MEM f (MAP SND (rstate lfd hw ifds m w1 (SUC k)).b.tbl) ∨
   MEM f (rstate lfd hw ifds m w1 (SUC k)).acq’
    by (qpat_x_assum ‘∀k. own _ _’ (qspec_then ‘SUC k’ mp_tac) >> simp[own_def] >>
        metis_tac[]) >>
  simp[] >>
  ‘ALL_DISTINCT (rstate lfd hw ifds m w1 k).acq’ by fs[pown_def, ALL_DISTINCT_APPEND] >>
  gvs[MEM_APPEND] >>
  Cases_on ‘d ≤ LENGTH pre’
  >- (disj2_tac >> qexistsl_tac [‘DROP d pre’, ‘post ++ log_conns (rlog lfd hw ifds m w1 k)’] >>
      simp[DROP_APPEND] >> ‘d − LENGTH pre = 0’ by simp[] >>
      ‘d − (LENGTH pre + 1) = 0’ by simp[] >> simp[] >>
      rw[] >> res_tac >> decide_tac)
  >> gvs[DROP_APPEND, NOT_LESS_EQUAL] >>
  ‘d − LENGTH pre = SUC (d − LENGTH pre − 1)’ by simp[] >>
  gvs[DROP_def, ALL_DISTINCT_APPEND] >> imp_res_tac MEM_DROP_IMP >> gvs[]
QED

(* MAIN (G6): an accepted fd gets a handle (unless its EOF is fetched
   first, at which point nothing of it is left to fetch) *)
Theorem fifo:
  simple_run p lfd sched hw ifds m w1 ∧ S2 lfd hw ifds m w1 ⇒
  ∀q k f c pre post.
    (rstate lfd hw ifds m w1 k).acq = pre ++ f :: post ∧ LENGTH pre = q ∧
    ALOOKUP (rworld lfd hw ifds m w1 k).open_fds f = SOME c ⇒
    ∃k'. k ≤ k' ∧
         (MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k') ∨
          MEM f (MAP SND (rstate lfd hw ifds m w1 k').b.tbl) ∧
          ALOOKUP (rworld lfd hw ifds m w1 k').open_fds f = SOME c)
Proof
  strip_tac >> completeInduct_on ‘q’ >> rpt strip_tac >>
  Cases_on ‘MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k)’ >- (qexists_tac ‘k’ >> simp[]) >>
  ‘∃n'. k ≤ n' ∧ MEM (Accept lfd) (new_actions (log_of m) (rhist lfd hw ifds m w1 n'))’
    by (qpat_x_assum ‘S2 _ _ _ _ _’ mp_tac >> simp[S2_def] >>
        disch_then (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘∀t. k + t ≤ n' ⇒
       (∃k'. k ≤ k' ∧
             (MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k') ∨
              MEM f (MAP SND (rstate lfd hw ifds m w1 k').b.tbl) ∧
              ALOOKUP (rworld lfd hw ifds m w1 k').open_fds f = SOME c)) ∨
       (¬MEM (Eof2 c) (upto (parr lfd hw ifds m w1) (k + t)) ∧
        ALOOKUP (rworld lfd hw ifds m w1 (k + t)).open_fds f = SOME c ∧
        ∃pre' post'. (rstate lfd hw ifds m w1 (k + t)).acq = pre' ++ f :: post' ∧
                     LENGTH pre' ≤ q)’
    by (Induct
        >- (strip_tac >> disj2_tac >> simp[] >> qexistsl_tac [‘pre’, ‘post’] >> simp[]) >>
        strip_tac >> fs[] >>
        TRY (disj1_tac >> metis_tac[] >> NO_TAC) >>
        rename1 ‘(rstate lfd hw ifds m w1 (k + t)).acq = pr ++ [f] ++ po’ >>
        drule_then (qspecl_then [‘k + t’, ‘f’, ‘c’, ‘pr’, ‘po’] mp_tac) fifo_step >>
        simp[] >> strip_tac
        >- (disj1_tac >> qexists_tac ‘SUC (k + t)’ >> simp[])
        >- (disj1_tac >> qexists_tac ‘SUC (k + t)’ >> simp[])
        >> rename1 ‘_ = pr' ++ [f] ++ po'’ >>
        Cases_on ‘MEM (Eof2 c) (upto (parr lfd hw ifds m w1) (SUC (k + t)))’
        >- (disj1_tac >> qexists_tac ‘SUC (k + t)’ >> simp[])
        >> disj2_tac >> fs[ADD_CLAUSES] >> qexistsl_tac [‘pr'’, ‘po'’] >> simp[]) >>
  first_x_assum (qspec_then ‘n' − k’ mp_tac) >> simp[] >> strip_tac >>
  TRY (qexists_tac ‘k'’ >> simp[] >> NO_TAC) >>
  ‘k + (n' − k) = n'’ by simp[] >> fs[] >>
  rename1 ‘(rstate lfd hw ifds m w1 n').acq = pr ++ [f] ++ po’ >>
  drule_then (qspecl_then [‘n'’, ‘f’, ‘c’, ‘pr’, ‘po’] mp_tac) fifo_step >>
  simp[] >> strip_tac
  >- (qexists_tac ‘SUC n'’ >> simp[])
  >- (qexists_tac ‘SUC n'’ >> simp[])
  >> rename1 ‘_ = pr' ++ [f] ++ po'’ >>
  first_x_assum (qspec_then ‘LENGTH pr'’ mp_tac) >> simp[] >>
  disch_then (qspecl_then [‘SUC n'’, ‘f’, ‘c’, ‘pr'’, ‘po'’] mp_tac) >> simp[] >>
  strip_tac >> qexists_tac ‘k'’ >> simp[]
QED

(* ========================================================================
   G7. Every client's data and EOF the kernel delivered are eventually
   fetched
   ======================================================================== *)

(* After a client's EOF the kernel's schedule has no more data for it *)
Theorem step_ok2_closed:
  ∀as s. step_ok2 s as ∧ c < LENGTH s.clients ∧ (EL c s.clients).peer_closed ⇒
         data_of c as = []
Proof
  Induct >> simp[step_ok2_def] >> rpt gen_tac >> strip_tac >>
  ‘c < LENGTH (deliver2 s h).clients ∧ (EL c (deliver2 s h).clients).peer_closed’
    by (Cases_on ‘h’ >>
        rw[deliver2_def, update_client_def, EL_LUPDATE, EL_APPEND1] >> rw[] >> gvs[]) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on ‘h’ >> gvs[data_of_cons, arrival_ok2_def] >> rw[] >> gvs[]
QED

Theorem kernel_eof_stable:
  w1.listeners = [(lfd, p, [])] ∧ w1.chans = [] ∧ sched_wf2 (sk_of p lfd sched w1) ⇒
  ∀d i. MEM (Eof2 c) (upto (kernel_steps p lfd sched w1) i) ⇒
        data_of c (upto (kernel_steps p lfd sched w1) (i + d)) =
        data_of c (upto (kernel_steps p lfd sched w1) i)
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[ADD_CLAUSES, upto_SUC] >>
  qabbrev_tac ‘kst = kernel_steps p lfd sched w1’ >>
  ‘vinv lfd (kworld p lfd sched w1 (i + d)) (upto kst (i + d))’
    by (simp[Abbr ‘kst’] >> metis_tac[kworld_vinv]) >>
  ‘MEM (Eof2 c) (upto kst (i + d))’ by (irule upto_mem_mono >> qexists_tac ‘i’ >> simp[]) >>
  ‘step_ok2 (kworld p lfd sched w1 (i + d)) (kst (i + d))’
    by (simp[Abbr ‘kst’] >> metis_tac[kworld_step_ok]) >>
  fs[vinv_def] >>
  ‘c < LENGTH (kworld p lfd sched w1 (d + i)).clients’
    by (CCONTR_TAC >> fs[NOT_LESS] >> res_tac) >>
  ‘(EL c (kworld p lfd sched w1 (d + i)).clients).peer_closed’ by metis_tac[] >>
  drule_all step_ok2_closed >> simp[]
QED

Theorem rworld_hgrow:
  run_ok lfd hw ifds m w1 ⇒
  ∀d k. ∃h. (rworld lfd hw ifds m w1 (k + d)).hist = (rworld lfd hw ifds m w1 k).hist ++ h
Proof
  strip_tac >> Induct >- simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k + d’] strip_assume_tac) >>
  drule pround_hgrow >> rw[hgrow_def] >> simp[ADD_CLAUSES] >> metis_tac[APPEND_ASSOC]
QED

Theorem npolls_mono:
  run_ok lfd hw ifds m w1 ∧ k ≤ k' ⇒
  npolls (rworld lfd hw ifds m w1 k).hist ≤ npolls (rworld lfd hw ifds m w1 k').hist
Proof
  strip_tac >> drule rworld_hgrow >> disch_then (qspecl_then [‘k' − k’, ‘k’] strip_assume_tac) >>
  ‘k + (k' − k) = k'’ by simp[] >> gvs[npolls_append]
QED

Theorem upto_prefix:
  n ≤ n' ⇒ upto g n ≼ upto g n'
Proof
  strip_tac >> qspecl_then [‘n' − n’, ‘n’] strip_assume_tac (Q.GEN ‘g’ upto_mono |> Q.SPEC ‘g’) >>
  ‘n + (n' − n) = n'’ by decide_tac >> gvs[]
QED

Theorem data_of_prefix:
  as ≼ as' ⇒ data_of j as ≼ data_of j as'
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem conns_of_prefix:
  as ≼ as' ⇒ conns_of as ≤ conns_of as'
Proof
  rw[IS_PREFIX_APPEND] >> simp[conns_of_def, FILTER_APPEND]
QED

(* A channel at the start of round k, against the kernel's schedule and
   psk's arrivals *)
Theorem rinv_chan:
  simple_run p lfd sched hw ifds m w1 ⇒
  ∀k c. c < LENGTH (rworld lfd hw ifds m w1 k).chans ⇒
    (EL c (rworld lfd hw ifds m w1 k).chans).peer_sent =
      data_of c (upto (kernel_steps p lfd sched w1)
                      (npolls (rworld lfd hw ifds m w1 k).hist − npolls w1.hist)) ∧
    ((EL c (rworld lfd hw ifds m w1 k).chans).peer_eof ⇔
      MEM (Eof2 c) (upto (kernel_steps p lfd sched w1)
                         (npolls (rworld lfd hw ifds m w1 k).hist − npolls w1.hist))) ∧
    data_of c (upto (parr lfd hw ifds m w1) k) ++ (EL c (rworld lfd hw ifds m w1 k).chans).inbox =
      (EL c (rworld lfd hw ifds m w1 k).chans).peer_sent ∧
    (MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k) ⇒
      (EL c (rworld lfd hw ifds m w1 k).chans).peer_eof ∧
      (EL c (rworld lfd hw ifds m w1 k).chans).inbox = []) ∧
    ((EL c (rworld lfd hw ifds m w1 k).chans).closed ⇒ MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k))
Proof
  strip_tac >>
  qpat_x_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  rpt gen_tac >> strip_tac >>
  drule_all rinv_run >> disch_then (qspec_then ‘k’ mp_tac) >>
  simp_tac std_ss [rinv_def, kinv_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘kworld p lfd sched w1 P’ >>
  ‘vinv lfd (kworld p lfd sched w1 P) (upto (kernel_steps p lfd sched w1) P)’
    by metis_tac[kworld_vinv] >>
  qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’ (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  fs[vinv_def] >>
  ‘c < LENGTH (kworld p lfd sched w1 P).clients’ by fs[] >>
  ‘wch (EL c (rworld lfd hw ifds m w1 k).chans) (EL c (kworld p lfd sched w1 P).clients) ∧
   dch (data_of c (upto (parr lfd hw ifds m w1) k)) (MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k))
       (EL c (rworld lfd hw ifds m w1 k).chans)’ by fs[] >>
  fs[wch_def, dch_def]
QED

Theorem rinv_len:
  simple_run p lfd sched hw ifds m w1 ⇒
  ∀k. LENGTH (rworld lfd hw ifds m w1 k).chans =
      conns_of (upto (kernel_steps p lfd sched w1)
                     (npolls (rworld lfd hw ifds m w1 k).hist − npolls w1.hist)) ∧
      SND (pcm lfd hw ifds m w1 k) ≤ LENGTH (rworld lfd hw ifds m w1 k).chans
Proof
  strip_tac >>
  qpat_x_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  gen_tac >>
  drule_all rinv_run >> disch_then (qspec_then ‘k’ mp_tac) >>
  simp_tac std_ss [rinv_def, kinv_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘kworld p lfd sched w1 P’ >>
  ‘vinv lfd (kworld p lfd sched w1 P) (upto (kernel_steps p lfd sched w1) P)’
    by metis_tac[kworld_vinv] >>
  fs[sinv_def, wk_def, lk_def, vinv_def]
QED

(* Between rounds R ≤ k, what the kernel delivered to a client only grows *)
Theorem ps_mono:
  simple_run p lfd sched hw ifds m w1 ∧ R ≤ k ∧ c < LENGTH (rworld lfd hw ifds m w1 R).chans ⇒
  c < LENGTH (rworld lfd hw ifds m w1 k).chans ∧
  (EL c (rworld lfd hw ifds m w1 R).chans).peer_sent ≼
    (EL c (rworld lfd hw ifds m w1 k).chans).peer_sent ∧
  ((EL c (rworld lfd hw ifds m w1 R).chans).peer_eof ⇒
   (EL c (rworld lfd hw ifds m w1 k).chans).peer_eof ∧
   (EL c (rworld lfd hw ifds m w1 k).chans).peer_sent =
     (EL c (rworld lfd hw ifds m w1 R).chans).peer_sent)
Proof
  strip_tac >>
  ‘run_ok lfd hw ifds m w1’ by fs[simple_run_def] >>
  ‘npolls (rworld lfd hw ifds m w1 R).hist ≤ npolls (rworld lfd hw ifds m w1 k).hist’
    by metis_tac[npolls_mono] >>
  qabbrev_tac ‘IR = npolls (rworld lfd hw ifds m w1 R).hist − npolls w1.hist’ >>
  qabbrev_tac ‘Ik = npolls (rworld lfd hw ifds m w1 k).hist − npolls w1.hist’ >>
  ‘IR ≤ Ik’ by simp[Abbr ‘IR’, Abbr ‘Ik’] >>
  qabbrev_tac ‘kst = kernel_steps p lfd sched w1’ >>
  ‘upto kst IR ≼ upto kst Ik’ by metis_tac[upto_prefix] >>
  drule rinv_len >> strip_tac >>
  ‘c < LENGTH (rworld lfd hw ifds m w1 k).chans’
    by (first_assum (qspec_then ‘R’ mp_tac) >> first_x_assum (qspec_then ‘k’ mp_tac) >>
        simp[] >> rpt strip_tac >> drule conns_of_prefix >> gvs[]) >>
  simp[] >>
  drule rinv_chan >> strip_tac >>
  first_assum (qspecl_then [‘R’, ‘c’] mp_tac) >> first_x_assum (qspecl_then [‘k’, ‘c’] mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[]
  >- metis_tac[data_of_prefix]
  >- (fs[IS_PREFIX_APPEND] >> gvs[])
  >> qpat_x_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  mp_tac kernel_eof_stable >> impl_tac >- simp[] >>
  disch_then (qspecl_then [‘Ik − IR’, ‘IR’] mp_tac) >> simp[Abbr ‘kst’]
QED

(* Once a client's EOF is fetched, all the kernel delivered to it is *)
Theorem fin_eof:
  simple_run p lfd sched hw ifds m w1 ∧ R ≤ k ∧ c < LENGTH (rworld lfd hw ifds m w1 R).chans ∧
  MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k) ⇒
  (EL c (rworld lfd hw ifds m w1 R).chans).peer_sent ≼ data_of c (upto (parr lfd hw ifds m w1) k)
Proof
  strip_tac >> drule_all ps_mono >> strip_tac >>
  drule rinv_chan >> disch_then (qspecl_then [‘k’, ‘c’] mp_tac) >> simp[] >> strip_tac >>
  gvs[]
QED

(* An fd with a handle keeps it while its EOF is not fetched *)
Theorem tbl_step:
  simple_run p lfd sched hw ifds m w1 ⇒
  ∀k f c. MEM f (MAP SND (rstate lfd hw ifds m w1 k).b.tbl) ∧
          ALOOKUP (rworld lfd hw ifds m w1 k).open_fds f = SOME c ∧
          ¬MEM (Eof2 c) (upto (parr lfd hw ifds m w1) (SUC k)) ⇒
          MEM f (MAP SND (rstate lfd hw ifds m w1 (SUC k)).b.tbl) ∧
          ALOOKUP (rworld lfd hw ifds m w1 (SUC k)).open_fds f = SOME c
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  ‘¬MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k) ∧ ¬MEM (Eof2 c) (parr lfd hw ifds m w1 k)’
    by fs[upto_SUC] >>
  drule run_fresh >> disch_then (qspecl_then [‘k’, ‘f’, ‘c’] mp_tac) >> simp[] >> strip_tac >>
  drule run_link >> disch_then drule_all >> strip_tac >> gvs[] >>
  qpat_x_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  ‘MEM lfd (l0_used w1) ∧ linv lfd w1’ by simp[l0_used_def, linv_def] >>
  ‘∀k. own (rstate lfd hw ifds m w1 k) (rworld lfd hw ifds m w1 k)’
    by (drule_all own_run >> simp[]) >>
  ‘∀k. rinv p lfd sched w1 hw ifds m k’ by (drule_all rinv_run >> simp[]) >>
  drule_all run_lfd >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  qpat_x_assum ‘∀k. rinv _ _ _ _ _ _ _ k’ (qspec_then ‘SUC k’ mp_tac) >>
  simp_tac std_ss [rinv_def, eown_def] >> strip_tac >>
  ‘¬MEM f (rstate lfd hw ifds m w1 (SUC k)).b.closing’ by (strip_tac >> res_tac) >>
  ‘¬MEM f (rstate lfd hw ifds m w1 (SUC k)).acq’
    by (strip_tac >> gvs[MEM_APPEND] >> imp_res_tac MEM_DROP_IMP >>
        fs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qpat_x_assum ‘∀k. own _ _’ (qspec_then ‘SUC k’ mp_tac) >> rewrite_tac[own_def] >>
  disch_then drule >> metis_tac[]
QED

Theorem rlogs_snoc:
  rlogs lfd hw ifds m w0 n0 (SUC d) =
  rlogs lfd hw ifds m w0 n0 d ++ rlog lfd hw ifds m w0 (n0 + d)
Proof
  ‘SUC d = d + 1’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[rlogs_add] >> simp[rlogs_def]
QED

(* Round by round from k: unless its EOF is fetched, an fd with a handle
   keeps it, and its client's fetched data grows by the fd's log *)
Theorem dl_iter:
  simple_run p lfd sched hw ifds m w1 ⇒
  ∀d k f c.
    MEM f (MAP SND (rstate lfd hw ifds m w1 k).b.tbl) ∧
    ALOOKUP (rworld lfd hw ifds m w1 k).open_fds f = SOME c ⇒
    MEM (Eof2 c) (upto (parr lfd hw ifds m w1) (k + d)) ∨
    (MEM f (MAP SND (rstate lfd hw ifds m w1 (k + d)).b.tbl) ∧
     ALOOKUP (rworld lfd hw ifds m w1 (k + d)).open_fds f = SOME c ∧
     data_of c (upto (parr lfd hw ifds m w1) (k + d)) =
       data_of c (upto (parr lfd hw ifds m w1) k) ++ fdata f (rlogs lfd hw ifds m w1 k d) ∧
     ¬fend f (rlogs lfd hw ifds m w1 k d) ∧
     ∀bs. MEM (FData f bs) (rlogs lfd hw ifds m w1 k d) ⇒ bs ≠ [])
Proof
  strip_tac >> Induct >- simp[rlogs_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- (disj1_tac >> irule upto_mem_mono >> qexists_tac ‘k + d’ >> simp[]) >>
  Cases_on ‘MEM (Eof2 c) (upto (parr lfd hw ifds m w1) (k + SUC d))’ >> simp[] >>
  ‘¬MEM (Eof2 c) (upto (parr lfd hw ifds m w1) (k + d))’
    by (strip_tac >> qpat_x_assum ‘¬MEM _ (upto _ (k + SUC d))’ mp_tac >> simp[] >>
        irule upto_mem_mono >> qexists_tac ‘k + d’ >> simp[]) >>
  drule run_link >> disch_then (qspecl_then [‘k + d’, ‘f’, ‘c’] mp_tac) >> simp[] >>
  strip_tac >>
  drule tbl_step >> disch_then (qspecl_then [‘k + d’, ‘f’, ‘c’] mp_tac) >>
  fs[ADD_CLAUSES] >> strip_tac >>
  fs[upto_SUC, rlogs_snoc] >> metis_tac[]
QED

Theorem pcm_mono:
  run_ok lfd hw ifds m w1 ∧ k ≤ k' ⇒ SND (pcm lfd hw ifds m w1 k) ≤ SND (pcm lfd hw ifds m w1 k')
Proof
  strip_tac >> drule conns_of_upto_parr >> strip_tac >>
  first_assum (qspec_then ‘k’ (SUBST1_TAC o SYM)) >>
  first_x_assum (qspec_then ‘k'’ (SUBST1_TAC o SYM)) >>
  irule conns_of_prefix >> irule upto_prefix >> simp[]
QED

(* Each client the kernel connected eventually has an fd with a handle, or
   its EOF fetched *)
Theorem handle_reached:
  simple_run p lfd sched hw ifds m w1 ∧ fds_room lfd hw ifds m w1 ∧
  S1 lfd hw ifds m w1 ∧ S2 lfd hw ifds m w1 ⇒
  ∀R c. c < LENGTH (rworld lfd hw ifds m w1 R).chans ⇒
    ∃k. R ≤ k ∧
        (MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k) ∨
         ∃f. MEM f (MAP SND (rstate lfd hw ifds m w1 k).b.tbl) ∧
             ALOOKUP (rworld lfd hw ifds m w1 k).open_fds f = SOME c)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  ‘∃k0. LENGTH (rworld lfd hw ifds m w1 R).chans ≤ SND (pcm lfd hw ifds m w1 k0)’
    by (irule conns_caught_up >> fs[simple_run_def] >> metis_tac[]) >>
  ‘run_ok lfd hw ifds m w1’ by fs[simple_run_def] >>
  ‘c < SND (pcm lfd hw ifds m w1 (R + k0))’
    by (‘SND (pcm lfd hw ifds m w1 k0) ≤ SND (pcm lfd hw ifds m w1 (R + k0))’
          by (irule pcm_mono >> simp[]) >> simp[]) >>
  qabbrev_tac ‘k1 = R + k0’ >>
  ‘c < LENGTH (rworld lfd hw ifds m w1 k1).chans’
    by (drule rinv_len >> disch_then (qspec_then ‘k1’ strip_assume_tac) >> simp[]) >>
  Cases_on ‘MEM (Eof2 c) (upto (parr lfd hw ifds m w1) k1)’
  >- (qexists_tac ‘k1’ >> simp[Abbr ‘k1’]) >>
  qpat_assum ‘simple_run _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [simple_run_def]) >>
  drule_all rinv_run >> disch_then (qspec_then ‘k1’ mp_tac) >>
  simp_tac std_ss [rinv_def, kinv_def, eown_def] >> strip_tac >>
  ‘(EL c (rworld lfd hw ifds m w1 k1).chans).closed ∨
   ∃f. ALOOKUP (rworld lfd hw ifds m w1 k1).open_fds f = SOME c’
    by fs[sinv_def, lk_def] >>
  drule rinv_chan >> disch_then (qspecl_then [‘k1’, ‘c’] mp_tac) >> simp[] >> strip_tac >>
  ‘own (rstate lfd hw ifds m w1 k1) (rworld lfd hw ifds m w1 k1)’
    by (drule_all own_run >> simp[]) >>
  qpat_x_assum ‘own _ _’ mp_tac >> simp[own_def] >> disch_then drule >> strip_tac
  >- (qexists_tac ‘k1’ >> simp[Abbr ‘k1’] >> metis_tac[])
  >- (qpat_x_assum ‘MEM f (_ .acq)’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
      drule_then (qspecl_then [‘LENGTH l1’, ‘k1’, ‘f’, ‘c’, ‘l1’, ‘l2’] mp_tac)
        (fifo |> REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      simp[] >> strip_tac >> qexists_tac ‘k'’ >> simp[Abbr ‘k1’] >> metis_tac[])
  >> res_tac
QED
