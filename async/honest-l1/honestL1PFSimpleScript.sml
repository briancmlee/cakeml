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
    a.peer_sent = v.incoming
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
    (∀f c. ALOOKUP w.open_fds f = SOME c ⇒ ALOOKUP cm f = SOME c ∧ c < a) ∧
    (∀c. c < LENGTH w.chans ⇒ dch (D c) (E c) (EL c w.chans)) ∧
    (∀c. a ≤ c ⇒ D c = [] ∧ ¬E c)
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
      >- metis_tac[]
      >> rpt strip_tac >> Cases_on ‘c < LENGTH w.chans’
      >- gvs[EL_APPEND1]
      >> ‘c = LENGTH w.chans’ by simp[] >> simp[EL_APPEND2] >>
      ‘D c = [] ∧ ¬E c’ by gvs[] >> simp[ch_fresh])
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
      >- metis_tac[]
      >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[])
      >> metis_tac[])
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
      >- metis_tac[]
      >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[])
      >> metis_tac[])
  >- ((* LBreak: excluded *) fs[])
  >- ((* LDrain *)
      rename1 ‘LDrain j k’ >>
      simp[l0_deliver_def] >> IF_CASES_TAC
      >- (simp[upd_lchan_def] >> simp_tac std_ss [sinv_def, wk_def, lk_def] >>
          simp[qof_def] >> rpt conj_tac
          >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[] >>
              metis_tac[ch_drain])
          >- metis_tac[]
          >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[] >>
              metis_tac[ch_drain])
          >> metis_tac[])
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
       wch (g (EL j w.chans)) v ∧ dch (D j) (E j) (g (EL j w.chans))) ⇒
  sinv lfd p a cm D E s (upd_lchan j g w)
Proof
  rpt strip_tac >> qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[upd_lchan_def, qof_def] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (res_tac >> NO_TAC) >>
  TRY (gvs[qof_def] >> NO_TAC) >>
  simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[] >>
  ‘wch (EL c w.chans) (EL c s.clients) ∧ dch (D c) (E c) (EL c w.chans)’ by fs[] >>
  qpat_x_assum ‘∀v. _’ (qspecl_then [‘EL c s.clients’] mp_tac) >> simp[]
QED

(* Fewer open fds keep it *)
Theorem sinv_open_fds:
  sinv lfd p a cm D E s w ∧
  (∀f c. ALOOKUP ofs f = SOME c ⇒ ALOOKUP w.open_fds f = SOME c) ⇒
  sinv lfd p a cm D E s (w with open_fds := ofs)
Proof
  rw[sinv_def, wk_def, lk_def, qof_def] >> metis_tac[]
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
  ‘E x’ by (fs[l0_chan_of_def, AllCaseEqs()] >> res_tac) >>
  irule sinv_upd >> conj_tac
  >- (simp[] >> rpt strip_tac >> drule_all ch_close >> simp[])
  >> irule sinv_open_fds >> simp[] >> metis_tac[ALOOKUP_ADELKEY_SOME]
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
  (∀v. wch (EL c w.chans) v ⇒ wch (g (EL c w.chans)) v) ∧ dch x (E c) (g (EL c w.chans)) ⇒
  sinv lfd p a cm ((c =+ x) D) E s (upd_lchan c g w)
Proof
  rpt strip_tac >> qpat_x_assum ‘sinv _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [sinv_def, wk_def, lk_def]) >>
  simp_tac std_ss [sinv_def, wk_def, lk_def] >> simp[upd_lchan_def, qof_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC
      >- (gvs[] >> qpat_x_assum ‘∀v. wch _ v ⇒ _’ irule >> fs[])
      >> fs[])
  >- (rpt strip_tac >> res_tac)
  >- (rpt strip_tac >> simp[EL_LUPDATE, APPLY_UPDATE_THM] >> IF_CASES_TAC >> gvs[])
  >> rpt strip_tac >> simp[APPLY_UPDATE_THM] >> IF_CASES_TAC >> gvs[]
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
      simp[AFUPDKEY_def, qof_def] >> rpt conj_tac >> rpt strip_tac >>
      TRY (Cases_on ‘f = lowest_fd w’ >> gvs[] >> res_tac >> simp[] >> NO_TAC) >>
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
      >> conj_tac >- simp[upd_lchan_def]
      >> irule sinv_upd_D >> simp[] >> conj_tac
      >- simp[wch_def]
      >> irule ch_recv >> fs[])
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
   (∃k. l0_res_of out = Ok k ∧ 0 < k ∧
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
  fs[APPEND_ASSOC] >> disj2_tac >> irule kinv_after >> simp[] >> metis_tac[]
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

Theorem used_open_fds:
  ALOOKUP w.open_fds g = SOME c ⇒ MEM g (l0_used w)
Proof
  rw[l0_used_def] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[FST]
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
