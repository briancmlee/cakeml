(*
  The quiescence measure of the protocol server's run (option C, design/33
  §2.5 (c)), and why its actions stop: every action shrinks the measure.

  For the polling run of a program (ifds, m) in a socket world that
  receives nothing more after round N (static), the measure of round n
  over the connections ks is
     the connections pending on the listener
   + for each connection c in ks:
       its unread bytes, plus 1 if its peer has closed, while the server
       has not read its EOF                                     (rterm)
     + the bytes read from c and still unread, less the writes to c
                                                                (wterm).
  The second part bounds the writes still to come: the protocol server
  writes at most one response per complete request, and a request has at
  least one byte.  Unlike asyncEchoMeasure's measure, no progress argument
  is needed: in a static round

  - nothing grows (wmeas_le), and
  - every action of the protocol server shrinks it (meas_act): an accept
    takes a pending connection (the listener was readable), a read takes
    bytes or the EOF (the connection was readable, and its EOF unread:
    asyncProtoActs), and a write is owed (proto_server_safety).

  So the run reaches a round after which it performs no actions
  (proto_acts_stop).

  MAIN: wmeas_le, meas_act, proto_acts_stop.
*)
Theory asyncProtoMeasure
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  ffiSpikeSocketFFI ffiSpikeSocketFair asyncM3World asyncM4GRounds
  asyncM4GTrans asyncM4SockInv asyncM4Relabel asyncM4RelabelDist
  asyncM4SockModel asyncM4EchoRunOk asyncM4Loop asyncM4Sched asyncM4Queue
  asyncM4LiveWorld asyncM4LiveServer asyncRunOkGen asyncStaticRounds
  asyncEchoMeasure asyncEchoStable asyncServerWith asyncProto
  asyncProtoServer asyncProtoSafe asyncSWActs asyncProtoActs QuietSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   The measure, for any program
   ------------------------------------------------------------------------ *)

(* The server has read c's EOF in the first n rounds *)
Definition weofr_def:
  weofr ifds m s0 c n ⇔ ∃k. MEM (Read c k, Got (SOME [])) (gperf ifds m s0 n)
End

(* c's unread bytes *)
Definition inlen_def:
  inlen s c = case ALOOKUP s.conns c of NONE => 0 | SOME cn => LENGTH cn.incoming
End

(* The writes to c *)
Definition nwr_def:
  nwr c (ps : (sact # sresp) list) = LENGTH (FILTER (λp. ∃d. FST p = Write c d) ps)
End

(* What is left to read on c *)
Definition rterm_def:
  rterm ifds m s0 n c =
    if weofr ifds m s0 c n then 0 else cm (gstate ifds m s0 n) c
End

(* The bytes c has sent, less the writes to c *)
Definition wterm_def:
  wterm ifds m s0 n c =
    rdbytes c (gperf ifds m s0 n) + inlen (gstate ifds m s0 n) c −
    nwr c (gperf ifds m s0 n)
End

Definition wmeas_def:
  wmeas l ifds m s0 ks n =
    LENGTH (lq l (gstate ifds m s0 n)) +
    SUM (MAP (λc. rterm ifds m s0 n c + wterm ifds m s0 n c) ks)
End

Theorem rdbytes_APPEND[local]:
  rdbytes c (xs ++ ys) = rdbytes c xs + rdbytes c ys
Proof
  simp[rdbytes_def, SUM_APPEND]
QED

Theorem nwr_APPEND[local]:
  nwr c (xs ++ ys) = nwr c xs + nwr c ys
Proof
  simp[nwr_def, FILTER_APPEND]
QED

Theorem SUM_MAP_LE[local]:
  ∀l. (∀x. MEM x l ⇒ f x ≤ g x) ⇒ SUM (MAP f l) ≤ SUM (MAP g l)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  ‘f h ≤ g h ∧ SUM (MAP f l) ≤ SUM (MAP g l)’ by simp[] >> simp[]
QED

Theorem SUM_MAP_LT[local]:
  ∀l. (∀x. MEM x l ⇒ f x ≤ g x) ∧ MEM y l ∧ f y < g y ⇒
      SUM (MAP f l) < SUM (MAP g l)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[]
  >- (‘SUM (MAP f l) ≤ SUM (MAP g l)’ by (irule SUM_MAP_LE >> simp[]) >> simp[])
  >> ‘f h ≤ g h ∧ SUM (MAP f l) < SUM (MAP g l)’ by (simp[] >> metis_tac[]) >> simp[]
QED

Theorem weofr_SUC:
  weofr ifds m s0 c (SUC n) ⇔
  weofr ifds m s0 c n ∨
  ∃k. MEM (Read c k, Got (SOME [])) (ZIP (gacts ifds m s0 n, gres ifds m s0 n))
Proof
  simp[weofr_def, gperf_SUC] >> metis_tac[]
QED

(* One static round: c's read term does not grow, and shrinks if c is read *)
Theorem rterm_step:
  grun_ok ifds m s0 ∧ next_step (gstate ifds m s0 n) = [] ⇒
  rterm ifds m s0 (SUC n) c ≤ rterm ifds m s0 n c ∧
  (¬weofr ifds m s0 c n ∧
   (0 < rdbytes c (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) ∨
    ∃k. MEM (Read c k, Got (SOME [])) (ZIP (gacts ifds m s0 n, gres ifds m s0 n))) ⇒
   rterm ifds m s0 (SUC n) c < rterm ifds m s0 n c)
Proof
  strip_tac >>
  drule_all static_round >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  ‘∀k. MEM (Read c k, Got (SOME [])) (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) ⇒
       ∃cn. ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ∧ cn.peer_closed’
    by (rpt strip_tac >> drule grun_ok_sock_acts >>
        disch_then (qspec_then ‘n’ strip_assume_tac) >>
        ‘∃cn. ALOOKUP (gstate ifds m s0 n).conns c = SOME cn’
          by (Cases_on ‘ALOOKUP (gstate ifds m s0 n).conns c’ >> simp[] >>
              drule_all sock_acts_eof >> strip_tac >>
              drule sock_acts_counts >> strip_tac >> res_tac >> gvs[]) >>
        drule_all sock_acts_conn >> metis_tac[]) >>
  simp[rterm_def, weofr_SUC] >>
  Cases_on ‘weofr ifds m s0 c n’ >> simp[] >>
  Cases_on ‘ALOOKUP (gstate ifds m s0 n).conns c’ >> simp[cm_def]
  >- (rw[] >> res_tac >> gvs[]) >>
  rename1 ‘_ = SOME cn’ >> first_x_assum drule >> strip_tac >> simp[] >>
  rw[] >> res_tac >> gvs[]
QED

(* One static round: c's write term does not grow, and shrinks with a write
   to c that is owed *)
Theorem wterm_step:
  grun_ok ifds m s0 ∧ next_step (gstate ifds m s0 n) = [] ⇒
  wterm ifds m s0 (SUC n) c ≤ wterm ifds m s0 n c ∧
  (0 < nwr c (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) ∧
   nwr c (gperf ifds m s0 n) < rdbytes c (gperf ifds m s0 n) + inlen (gstate ifds m s0 n) c ⇒
   wterm ifds m s0 (SUC n) c < wterm ifds m s0 n c)
Proof
  strip_tac >>
  drule_all static_round >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  ‘rdbytes c (gperf ifds m s0 (SUC n)) + inlen (gstate ifds m s0 (SUC n)) c =
   rdbytes c (gperf ifds m s0 n) + inlen (gstate ifds m s0 n) c’
    by (simp[gperf_SUC, rdbytes_APPEND, inlen_def] >>
        Cases_on ‘ALOOKUP (gstate ifds m s0 n).conns c’ >> res_tac >> simp[]) >>
  ‘nwr c (gperf ifds m s0 (SUC n)) =
   nwr c (gperf ifds m s0 n) + nwr c (ZIP (gacts ifds m s0 n, gres ifds m s0 n))’
    by simp[gperf_SUC, nwr_APPEND] >>
  simp[wterm_def]
QED

(* The world receives nothing from round N on *)
Overload static_g = “λifds m s0 N. ∀n. N ≤ n ⇒ next_step (gstate ifds m s0 n) = []”

(* One static round: the measure does not grow, and shrinks if the queue
   or one connection's term does *)
Theorem wmeas_step:
  grun_ok ifds m s0 ∧ next_step (gstate ifds m s0 n) = [] ⇒
  wmeas l ifds m s0 ks (SUC n) ≤ wmeas l ifds m s0 ks n ∧
  ((0 < nacc_ok l (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) ∨
    ∃c. MEM c ks ∧ (rterm ifds m s0 (SUC n) c < rterm ifds m s0 n c ∨
                    wterm ifds m s0 (SUC n) c < wterm ifds m s0 n c)) ⇒
   wmeas l ifds m s0 ks (SUC n) < wmeas l ifds m s0 ks n)
Proof
  strip_tac >>
  drule_all static_round >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  ‘∀c. rterm ifds m s0 (SUC n) c ≤ rterm ifds m s0 n c ∧
       wterm ifds m s0 (SUC n) c ≤ wterm ifds m s0 n c’
    by (gen_tac >> drule_all rterm_step >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
        drule_all wterm_step >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
        simp[]) >>
  ‘SUM (MAP (λc. rterm ifds m s0 (SUC n) c + wterm ifds m s0 (SUC n) c) ks) ≤
   SUM (MAP (λc. rterm ifds m s0 n c + wterm ifds m s0 n c) ks)’
    by (irule SUM_MAP_LE >> rw[] >>
        first_x_assum (qspec_then ‘x’ strip_assume_tac) >> simp[]) >>
  simp[wmeas_def] >> rpt strip_tac >- simp[] >>
  ‘SUM (MAP (λc. rterm ifds m s0 (SUC n) c + wterm ifds m s0 (SUC n) c) ks) <
   SUM (MAP (λc. rterm ifds m s0 n c + wterm ifds m s0 n c) ks)’
    by (irule SUM_MAP_LT >> rw[]
        >- (first_x_assum (qspec_then ‘x’ strip_assume_tac) >> simp[])
        >> qexists_tac ‘c’ >> simp[] >>
        first_x_assum (qspec_then ‘c’ strip_assume_tac) >> simp[]) >>
  simp[]
QED

(* MAIN: from N on, the measure only shrinks *)
Theorem wmeas_le:
  grun_ok ifds m s0 ∧ static_g ifds m s0 N ⇒
  ∀d n. N ≤ n ⇒ wmeas l ifds m s0 ks (n + d) ≤ wmeas l ifds m s0 ks n
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘next_step (gstate ifds m s0 (n + d)) = []’ by simp[] >>
  ‘wmeas l ifds m s0 ks (SUC (n + d)) ≤ wmeas l ifds m s0 ks (n + d)’
    by metis_tac[wmeas_step] >>
  decide_tac
QED

(* ------------------------------------------------------------------------
   The world, for any program that uses the socket API correctly
   ------------------------------------------------------------------------ *)

Theorem deliver1_no_listener[local]:
  is_listener s l ∧ ALOOKUP s.conns l = NONE ⇒
  is_listener (deliver1 s a) l ∧ ALOOKUP (deliver1 s a).conns l = NONE
Proof
  Cases_on ‘a’ >>
  rw[deliver1_def, is_listener_def, is_conn_def, AFUPDKEY_ALOOKUP] >>
  gvs[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on ‘ALOOKUP s.listeners l’ >> gvs[] >> rw[]
QED

Theorem FOLDL_deliver1_no_listener[local]:
  ∀as s. is_listener s l ∧ ALOOKUP s.conns l = NONE ⇒
         is_listener (FOLDL deliver1 s as) l ∧
         ALOOKUP (FOLDL deliver1 s as).conns l = NONE
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> metis_tac[deliver1_no_listener]
QED

Theorem tick_no_listener[local]:
  is_listener s l ∧ ALOOKUP s.conns l = NONE ⇒
  ALOOKUP (tick s).conns l = NONE
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def] >>
  qmatch_goalsub_abbrev_tac ‘FOLDL deliver1 s1 as’ >>
  qspecl_then [‘as’, ‘s1’] mp_tac FOLDL_deliver1_no_listener >>
  simp[Abbr ‘s1’] >> gvs[is_listener_def]
QED

(* No connection ever has the listener's fd *)
Theorem conns_no_listener_g:
  grun_ok ifds m s0 ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n. ALOOKUP (gstate ifds m s0 n).conns (n2w lfdn) = NONE
Proof
  strip_tac >>
  Induct >- simp[gstate_def, grounds_def] >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def] >>
  simp[gstate_SUC] >> irule tick_no_listener >>
  drule sock_acts_counts >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  simp[] >>
  qspecl_then [‘s0’, ‘n2w lfdn’, ‘ifds’, ‘m’] mp_tac
    (Q.GENL [‘s0’, ‘lfd’, ‘ifds’, ‘m’] grounds_known) >>
  simp[] >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule sock_acts_keys >> strip_tac >>
  gvs[is_listener_def, ALOOKUP_NONE]
QED

(* A static round's end has no connection its start did not have *)
Theorem conns_back_g:
  grun_ok ifds m s0 ∧ static_g ifds m s0 N ⇒
  ∀d. ALOOKUP (gstate ifds m s0 N).conns c = NONE ⇒
      ALOOKUP (gstate ifds m s0 (N + d)).conns c = NONE
Proof
  strip_tac >> Induct >> simp[] >> strip_tac >> gvs[] >>
  ‘N + SUC d = SUC (N + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘next_step (gstate ifds m s0 (N + d)) = []’ by simp[] >>
  drule_all static_round >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  res_tac
QED

(* The connections of round N *)
Overload ksg = “λifds m s0 N. MAP FST (gstate ifds m s0 N).conns”

Theorem conn_ks:
  grun_ok ifds m s0 ∧ static_g ifds m s0 N ∧ N ≤ n ∧
  ALOOKUP (gstate ifds m s0 n).conns c ≠ NONE ⇒
  MEM c (ksg ifds m s0 N)
Proof
  rpt strip_tac >> CCONTR_TAC >>
  ‘ALOOKUP (gstate ifds m s0 N).conns c = NONE’ by simp[ALOOKUP_NONE] >>
  drule_all conns_back_g >> disch_then (qspec_then ‘n − N’ mp_tac) >> simp[]
QED

(* An accepted connection is a connection of the world *)
Theorem accepted_conn:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (gperf ifds (srelabel m) s0 n)) ⇒
  ∃cn. ALOOKUP (gstate ifds (srelabel m) s0 n).conns c = SOME cn
Proof
  strip_tac >> drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  gvs[sinv_def, is_conn_def] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> simp[] >>
  Cases_on ‘ALOOKUP (gstate ifds (srelabel m) s0 n).conns c’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The transcript, and the world's counts
   ------------------------------------------------------------------------ *)

Theorem TREL_CONS_SOME[local]:
  TREL ((a0, r0) :: tt) (MAP (λ(a, r). (a, SOME r)) ((a, r) :: ps)) ⇔
    sfa a0 = a ∧ r0 = SOME (sfr r) ∧ TREL tt (MAP (λ(a, r). (a, SOME r)) ps)
Proof
  simp[] >> metis_tac[]
QED

(* The writes to c in the model transcript are those of the world *)
Theorem TREL_written:
  ∀tt ps. TREL tt (MAP (λ(a, r). (a, SOME r)) ps) ∧
          (∀fd. EXISTS (on_fd fd) tt ⇒ fd < dimword (:64)) ⇒
          LENGTH (written (w2n c) tt) = nwr c ps
Proof
  Induct >- (Cases >> simp[written_def, nwr_def]) >>
  rpt gen_tac >> Cases_on ‘ps’ >> simp[] >>
  PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >> strip_tac >>
  first_x_assum drule >>
  impl_tac >- (rpt strip_tac >> simp[] >> first_x_assum irule >> simp[]) >> strip_tac >>
  gvs[written_def, nwr_def] >>
  Cases_on ‘h0’ >> gvs[sfa_def] >> rw[] >> gvs[] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[w2n_n2w, LESS_MOD, n2w_w2n]
QED

(* The bytes read from c in the model transcript are those of the world *)
Theorem TREL_read:
  ∀tt ps. TREL tt (MAP (λ(a, r). (a, SOME r)) ps) ∧
          (∀fd. EXISTS (on_fd fd) tt ⇒ fd < dimword (:64)) ⇒
          LENGTH (CONCAT (read (w2n c) tt)) = rdbytes c ps
Proof
  Induct >- (Cases >> simp[read_def, rdbytes_def]) >>
  rpt gen_tac >> Cases_on ‘ps’ >> simp[] >>
  PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >> strip_tac >>
  first_x_assum drule >>
  impl_tac >- (rpt strip_tac >> simp[] >> first_x_assum irule >> simp[]) >> strip_tac >>
  ONCE_REWRITE_TAC[counts_CONS] >>
  gvs[read_def, rdbytes_def] >>
  Cases_on ‘h0’ >> gvs[sfa_def] >>
  Cases_on ‘h'1’ >> gvs[sfr_def] >>
  TRY (rename1 ‘Accepted oc’ >> Cases_on ‘oc’ >> gvs[sfr_def]) >>
  TRY (rename1 ‘Got oc’ >> Cases_on ‘oc’ >> gvs[sfr_def] >> rw[] >> gvs[]) >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> rw[] >> gvs[] >> metis_tac[w2n_n2w, LESS_MOD, n2w_w2n]
QED

Theorem proto_all_LENGTH:
  ∀s. LENGTH (proto_all P s) ≤ LENGTH s
Proof
  gen_tac >> completeInduct_on ‘LENGTH s’ >> rw[] >>
  simp[Once proto_all_def] >> every_case_tac >> gvs[] >>
  rename1 ‘PComplete r rest’ >>
  first_x_assum (qspec_then ‘LENGTH rest’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘rest’ mp_tac) >> simp[]
QED

Theorem accs_accepted:
  ∀tt. accs fd tt = LENGTH (FILTER ($= fd) (accepted tt))
Proof
  Induct >- simp[accs_def] >> rpt gen_tac >> PairCases_on ‘h’ >>
  Cases_on ‘h1’ >> TRY (rename1 ‘SOME x’ >> Cases_on ‘x’) >>
  Cases_on ‘h0’ >> simp[is_acc_def, FILTER_APPEND] >> IF_CASES_TAC >> gvs[]
QED

(* The model transcript hands out each fd at most once *)
Theorem accs_le_one_g:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  accs fd (TSg m ifds s0 n) ≤ 1
Proof
  strip_tac >> drule_all gen_fresh >>
  disch_then (qspecl_then [‘n’, ‘ifds’] mp_tac) >> rw[fresh_def] >>
  simp[accs_accepted] >>
  Cases_on ‘MEM fd (accepted (TSg m ifds s0 n))’
  >- (gvs[ALL_DISTINCT_FILTER] >> res_tac >> simp[])
  >> ‘FILTER ($= fd) (accepted (TSg m ifds s0 n)) = []’
       by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

(* An EOF the world returned is one in the model transcript *)
Theorem weofr_eofs:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  weofr ifds (srelabel m) s0 c n ⇒
  1 ≤ eofs (w2n c) (TSg m ifds s0 n)
Proof
  rw[weofr_def] >> drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  ‘MEM (Read c k, SOME Eof) (MAP (λ(a, r). (sfa a, r)) tt1)’
    by (ASM_REWRITE_TAC[] >> simp[MEM_MAP, EXISTS_PROD] >>
        qexists_tac ‘SOME (Got (SOME []))’ >> simp[sfr_def]) >>
  qpat_x_assum ‘MEM _ (MAP _ tt1)’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_MAP, EXISTS_PROD]) >>
  rename1 ‘MEM (a, SOME Eof) tt1’ >> Cases_on ‘a’ >> fs[sfa_def] >>
  rename1 ‘MEM (Read fd, SOME Eof) tt1’ >>
  ‘fd < dimword (:64)’
    by (qspecl_then [‘s0’, ‘lfdn’, ‘m’, ‘ifds’, ‘n’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘m’, ‘ifds’, ‘n’] gen_fds_bounded) >>
        simp[] >> disch_then irule >> simp[EXISTS_MEM] >> disj1_tac >>
        qexists_tac ‘(Read fd, SOME Eof)’ >> simp[]) >>
  ‘w2n c = fd’ by gvs[] >>
  ‘MEM (Read fd, SOME Eof) (FILTER (is_eof fd) tt1)’ by simp[MEM_FILTER, is_eof_def] >>
  simp[eofs_def, FILTER_APPEND] >>
  Cases_on ‘FILTER (is_eof fd) tt1’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   The protocol server
   ------------------------------------------------------------------------ *)

Overload PM = “λP resp lfdn. srelabel (proto_server P resp lfdn)”

Theorem proto_uses_ok:
  proto_ok P ⇒ uses_ok lfdn (proto_server P resp lfdn)
Proof
  simp[uses_ok_def] >> metis_tac[proto_server_uses_accepted]
QED

Theorem proto_grun_ok:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grun_ok ifds (PM P resp lfdn) s0
Proof
  strip_tac >> irule gen_grun_ok >> simp[] >> metis_tac[proto_uses_ok]
QED

(* Round 0 has no actions; round n + 1's are the server's with the
   snapshot of round n + 1's ready fds and round n's responses *)
Theorem proto_gacts_0:
  gacts ifds (PM P resp lfdn) s0 0 = []
Proof
  simp[gacts_def, ghist_def, grounds_def, new_actions_relabel, new_actions_NIL,
       log_of_def, proto_server_def, sw_NIL_actions]
QED

Theorem proto_gacts_SUC:
  gacts ifds (PM P resp lfdn) s0 (SUC n) =
  MAP sfa (NA (proto_server P resp lfdn)
               (MAP sfs (ghist ifds (PM P resp lfdn) s0 n) ++
                [sfs (ssnap (FILTER (is_ready (gstate ifds (PM P resp lfdn) s0 (SUC n)))
                                    (ifds (ghist ifds (PM P resp lfdn) s0 n)))
                            (gres ifds (PM P resp lfdn) s0 n))]))
Proof
  simp[gacts_def, new_actions_relabel, ghist_SUC_snap]
QED

Theorem ready_sfs[local]:
  Readable g ∈ (sfs (ssnap ys rs)).ready ⇔ ∃w. g = w2n w ∧ MEM w ys
Proof
  simp[snap_map_def, ssnap_def, sfe_def] >> metis_tac[]
QED

Theorem n2w_w2n_eq[local]:
  lfdn < dimword (:64) ∧ lfdn = w2n (w : word64) ⇒ w = n2w lfdn
Proof
  rw[] >> simp[]
QED

Theorem MEM_ZIP_FST[local]:
  ∀xs ys. LENGTH xs = LENGTH ys ∧ MEM x xs ⇒ ∃y. MEM (x, y) (ZIP (xs, ys))
Proof
  Induct >> simp[] >> Cases_on ‘ys’ >> simp[] >> rw[] >> metis_tac[]
QED

(* What round n's actions need, in the world: an accept, the listener
   ready; a read of c, c ready and its EOF not read in the transcript *)
Theorem gacts_cause:
  MEM a (gacts ifds (PM P resp lfdn) s0 n) ⇒
  ∃m a0. n = SUC m ∧ a = sfa a0 ∧
    MEM a0 (NA (proto_server P resp lfdn) (MAP sfs (ghist ifds (PM P resp lfdn) s0 n))) ∧
    (∀l0. a0 = Accept l0 ⇒
          l0 = lfdn ∧ ∃w. lfdn = w2n w ∧ is_ready (gstate ifds (PM P resp lfdn) s0 n) w) ∧
    (∀g. a0 = Read g ⇒
         (∃w. g = w2n w ∧ is_ready (gstate ifds (PM P resp lfdn) s0 n) w) ∧
         eofs g (TSg (proto_server P resp lfdn) ifds s0 n) <
         accs g (TSg (proto_server P resp lfdn) ifds s0 n))
Proof
  Cases_on ‘n’ >- simp[proto_gacts_0] >>
  rename1 ‘SUC m’ >> simp[] >>
  REWRITE_TAC[proto_gacts_SUC, MEM_MAP] >> strip_tac >>
  qexists_tac ‘y’ >> simp[ghist_SUC_snap] >>
  drule proto_server_new_actions >> strip_tac >>
  rpt strip_tac >> gvs[ready_sfs, MEM_FILTER] >> metis_tac[]
QED

Theorem read_NONE[local]:
  ∀tt. EVERY (λp. SND p = NONE) tt ⇒ read fd tt = []
Proof
  Induct >> simp[read_def] >> Cases >> rw[] >> gvs[read_def] >>
  Cases_on ‘q’ >> simp[]
QED

(* An accept of the protocol server takes a pending connection *)
Theorem act_accept:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  MEM (Accept l) (gacts (EI lfdn) (PM P resp lfdn) s0 n) ⇒
  0 < nacc_ok l (ZIP (gacts (EI lfdn) (PM P resp lfdn) s0 n,
                      gres (EI lfdn) (PM P resp lfdn) s0 n))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (PM P resp lfdn) s0’ by metis_tac[proto_grun_ok] >>
  drule gacts_cause >> strip_tac >>
  qpat_x_assum ‘MEM a0 _’ kall_tac >> qpat_x_assum ‘∀g. a0 = Read g ⇒ _’ kall_tac >>
  Cases_on ‘a0’ >> fs[sfa_def] >> gvs[] >>
  qspecl_then [‘interest [l]’, ‘PM P resp (w2n l)’, ‘s0’, ‘w2n l’] mp_tac
    (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfdn’] conns_no_listener_g) >>
  simp[] >> disch_then (qspec_then ‘SUC m’ assume_tac) >>
  ‘lq l (gstate (interest [l]) (PM P resp (w2n l)) s0 (SUC m)) ≠ []’
    by (qpat_x_assum ‘is_ready _ _’ mp_tac >> simp[is_ready_def, lq_def] >>
        every_case_tac >> simp[]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘SUC m’ strip_assume_tac) >>
  drule sock_acts_accepts >> disch_then irule >> fs[]
QED

(* A read of the protocol server takes bytes or the EOF, of a connection
   whose EOF it has not read *)
Theorem act_read:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  MEM (Read c k) (gacts (EI lfdn) (PM P resp lfdn) s0 n) ⇒
  ¬weofr (EI lfdn) (PM P resp lfdn) s0 c n ∧
  (∃cn. ALOOKUP (gstate (EI lfdn) (PM P resp lfdn) s0 n).conns c = SOME cn) ∧
  (0 < rdbytes c (ZIP (gacts (EI lfdn) (PM P resp lfdn) s0 n,
                       gres (EI lfdn) (PM P resp lfdn) s0 n)) ∨
   ∃k'. MEM (Read c k', Got (SOME []))
            (ZIP (gacts (EI lfdn) (PM P resp lfdn) s0 n, gres (EI lfdn) (PM P resp lfdn) s0 n)))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (PM P resp lfdn) s0’ by metis_tac[proto_grun_ok] >>
  ‘uses_ok lfdn (proto_server P resp lfdn)’ by metis_tac[proto_uses_ok] >>
  drule gacts_cause >> strip_tac >>
  qpat_x_assum ‘MEM a0 _’ kall_tac >> qpat_x_assum ‘∀l0. a0 = Accept l0 ⇒ _’ kall_tac >>
  Cases_on ‘a0’ >> fs[sfa_def] >> gvs[] >>
  ‘accs (w2n c) (TSg (proto_server P resp lfdn) (EI lfdn) s0 (SUC m)) ≤ 1’ by (irule accs_le_one_g >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  ‘eofs (w2n c) (TSg (proto_server P resp lfdn) (EI lfdn) s0 (SUC m)) = 0’ by decide_tac >>
  conj_tac
  >- (strip_tac >>
      ‘1 ≤ eofs (w2n c) (TSg (proto_server P resp lfdn) (EI lfdn) s0 (SUC m))’ by (irule weofr_eofs >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
      decide_tac) >>
  (* c is an accepted connection: not the listener *)
  ‘MEM (w2n c) (accepted (TSg (proto_server P resp lfdn) (EI lfdn) s0 (SUC m)))’
    by (CCONTR_TAC >>
        ‘FILTER ($= (w2n c)) (accepted (TSg (proto_server P resp lfdn) (EI lfdn) s0 (SUC m))) = []’
          by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
        gvs[accs_accepted]) >>
  ‘MEM c (wacc (gperf (EI lfdn) (PM P resp lfdn) s0 (SUC m)))’
    by (drule_all gen_sinv >>
        disch_then (qspecl_then [‘EI lfdn’, ‘SUC m’] strip_assume_tac) >>
        drule gen_trans_split >> strip_tac >>
        drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
        gvs[accepted_NONE, MEM_MAP]) >>
  ‘∃cn. ALOOKUP (gstate (EI lfdn) (PM P resp lfdn) s0 (SUC m)).conns c = SOME cn’
    by (irule accepted_conn >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  ‘ALOOKUP (gstate (EI lfdn) (PM P resp lfdn) s0 (SUC m)).conns (n2w lfdn) = NONE’
    by (qspecl_then [‘EI lfdn’, ‘PM P resp lfdn’, ‘s0’, ‘lfdn’] mp_tac
          (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfdn’] conns_no_listener_g) >>
        impl_tac >- fs[] >> simp[]) >>
  ‘ALOOKUP (gstate (EI lfdn) (PM P resp lfdn) s0 (SUC m)).listeners c = NONE’
    by (‘c ≠ n2w lfdn’ by (strip_tac >> gvs[]) >>
        qspecl_then [‘s0’, ‘n2w lfdn’, ‘EI lfdn’, ‘PM P resp lfdn’] mp_tac
          (Q.GENL [‘s0’, ‘lfd’, ‘ifds’, ‘m’] grounds_known) >>
        simp[] >> disch_then (qspec_then ‘SUC m’ strip_assume_tac) >>
        PairCases_on ‘x0’ >> gvs[]) >>
  conj_tac >- (qexists_tac ‘cn’ >> simp[]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘SUC m’ strip_assume_tac) >>
  drule sock_acts_reads >> disch_then irule >> simp[] >>
  conj_tac >- (qpat_x_assum ‘is_ready _ _’ mp_tac >> simp[is_ready_def]) >>
  qexists_tac ‘bufsz’ >> simp[]
QED

(* A write of the protocol server is owed: the server has written to c
   fewer times than it has read bytes from c *)
Theorem act_write:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM (Write c bs) (gacts (EI lfdn) (PM P resp lfdn) s0 n) ⇒
  (∃cn. ALOOKUP (gstate (EI lfdn) (PM P resp lfdn) s0 n).conns c = SOME cn) ∧
  0 < nwr c (ZIP (gacts (EI lfdn) (PM P resp lfdn) s0 n, gres (EI lfdn) (PM P resp lfdn) s0 n)) ∧
  nwr c (gperf (EI lfdn) (PM P resp lfdn) s0 n) <
  rdbytes c (gperf (EI lfdn) (PM P resp lfdn) s0 n)
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (PM P resp lfdn) s0’ by metis_tac[proto_grun_ok] >>
  ‘uses_ok lfdn (proto_server P resp lfdn)’ by metis_tac[proto_uses_ok] >>
  drule_all gen_sinv >> disch_then (qspecl_then [‘EI lfdn’, ‘n’] strip_assume_tac) >>
  (* c is accepted *)
  ‘MEM c (wacc (gperf (EI lfdn) (PM P resp lfdn) s0 n))’
    by (drule_all gen_round_actions_ok >> simp[EVERY_MEM] >>
        disch_then drule >> simp[action_ok_def]) >>
  conj_tac >- (irule accepted_conn >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  conj_tac
  >- (‘∃r. MEM (Write c bs, r)
               (ZIP (gacts (EI lfdn) (PM P resp lfdn) s0 n, gres (EI lfdn) (PM P resp lfdn) s0 n))’
        by (irule MEM_ZIP_FST >> simp[LENGTH_gres]) >>
      simp[nwr_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >>
      qexists_tac ‘(Write c bs, r)’ >> simp[]) >>
  (* safety: what is written is a prefix of the responses to what is read *)
  ‘fresh (TSg (proto_server P resp lfdn) (EI lfdn) s0 n)’
    by (irule gen_fresh >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  ‘∀fd. EXISTS (on_fd fd) (TSg (proto_server P resp lfdn) (EI lfdn) s0 n) ⇒ fd < dimword (:64)’
    by (qspecl_then [‘s0’, ‘lfdn’, ‘proto_server P resp lfdn’, ‘EI lfdn’, ‘n’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘m’, ‘ifds’, ‘n’] gen_fds_bounded) >>
        impl_tac >- fs[] >> simp[]) >>
  ‘LENGTH (written (w2n c) (TSg (proto_server P resp lfdn) (EI lfdn) s0 n)) ≤
   LENGTH (CONCAT (read (w2n c) (TSg (proto_server P resp lfdn) (EI lfdn) s0 n)))’
    by (drule_all proto_server_safety >> disch_then (qspec_then ‘w2n c’ assume_tac) >>
        drule IS_PREFIX_LENGTH >> simp[] >> strip_tac >>
        qmatch_goalsub_abbrev_tac ‘STRLEN DD’ >>
        ‘LENGTH (proto_all P DD) ≤ LENGTH DD’ by simp[proto_all_LENGTH] >>
        decide_tac) >>
  drule gen_trans_split >> strip_tac >> gvs[EXISTS_APPEND] >>
  ‘∀fd. EXISTS (on_fd fd) tt1 ⇒ fd < dimword (:64)’
    by (rpt strip_tac >> simp[] >> qpat_x_assum ‘∀fd. _ ∨ _ ⇒ _’ irule >> simp[]) >>
  ‘LENGTH (written (w2n c) tt1) = nwr c (gperf (EI lfdn) (PM P resp lfdn) s0 n)’
    by (irule TREL_written >> simp[]) >>
  ‘LENGTH (CONCAT (read (w2n c) tt1)) = rdbytes c (gperf (EI lfdn) (PM P resp lfdn) s0 n)’
    by (irule TREL_read >> simp[]) >>
  (* tt2 holds the write, unanswered *)
  drule TREL_NONE >> strip_tac >>
  ‘read (w2n c) tt2 = []’ by (irule read_NONE >> simp[]) >>
  ‘1 ≤ LENGTH (written (w2n c) tt2)’
    by (‘MEM (Write c bs) (MAP (sfa o FST) tt2)’ by simp[] >>
        pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_MAP]) >>
        rename1 ‘MEM p tt2’ >> PairCases_on ‘p’ >>
        Cases_on ‘p0’ >> gvs[sfa_def] >> rename1 ‘MEM (Write fd s, _) tt2’ >>
        ‘fd < dimword (:64)’
          by (simp[] >> qpat_x_assum ‘∀fd. _ ∨ _ ⇒ _’ irule >> disj2_tac >> simp[EXISTS_MEM] >>
              qexists_tac ‘(Write fd s, p1)’ >> simp[]) >>
        gvs[MEM_SPLIT, written_def]) >>
  fs[] >> decide_tac
QED

(* MAIN: after the last arrival, every action of the protocol server
   shrinks the measure *)
Theorem meas_act:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  static_g (EI lfdn) (PM P resp lfdn) s0 N ∧ N ≤ n ∧
  gacts (EI lfdn) (PM P resp lfdn) s0 n ≠ [] ⇒
  wmeas (n2w lfdn) (EI lfdn) (PM P resp lfdn) s0 (ksg (EI lfdn) (PM P resp lfdn) s0 N) (SUC n) <
  wmeas (n2w lfdn) (EI lfdn) (PM P resp lfdn) s0 (ksg (EI lfdn) (PM P resp lfdn) s0 N) n
Proof
  strip_tac >> drule_all proto_grun_ok >>
  disch_then (qspecl_then [‘resp’, ‘EI lfdn’] assume_tac) >>
  ‘next_step (gstate (EI lfdn) (PM P resp lfdn) s0 n) = []’ by simp[] >>
  drule_all wmeas_step >>
  disch_then (qspecl_then [‘n2w lfdn’, ‘ksg (EI lfdn) (PM P resp lfdn) s0 N’]
                (irule o CONJUNCT2)) >>
  ‘∃h. MEM h (gacts (EI lfdn) (PM P resp lfdn) s0 n)’
    by (Cases_on ‘gacts (EI lfdn) (PM P resp lfdn) s0 n’ >> fs[] >> metis_tac[MEM]) >>
  Cases_on ‘h’
  (* an accept *)
  >- (disj1_tac >> rename1 ‘Accept a’ >>
      ‘a = n2w lfdn’
        by (qpat_x_assum ‘MEM (Accept _) _’ mp_tac >> strip_tac >>
            drule gacts_cause >> strip_tac >>
            qpat_x_assum ‘MEM a0 _’ kall_tac >> qpat_x_assum ‘∀g. a0 = Read g ⇒ _’ kall_tac >>
            Cases_on ‘a0’ >> fs[sfa_def]) >>
      gvs[] >> irule act_accept >> fs[])
  (* a read *)
  >- (disj2_tac >> rename1 ‘Read c k’ >> qexists_tac ‘c’ >>
      drule_at Any act_read >> simp[] >> strip_tac >>
      ‘MEM c (ksg (EI lfdn) (PM P resp lfdn) s0 N)’
        by (irule conn_ks >> rpt conj_tac >> TRY (qexists_tac ‘n’) >> fs[]) >>
      simp[] >> disj1_tac >> drule_all rterm_step >>
      disch_then (qspec_then ‘c’ strip_assume_tac) >> first_x_assum irule >> fs[] >>
      metis_tac[])
  (* a write *)
  >> disj2_tac >> rename1 ‘Write c bs’ >> qexists_tac ‘c’ >>
  drule_at Any act_write >> simp[] >> strip_tac >>
  conj_tac >- (irule conn_ks >> rpt conj_tac >> TRY (qexists_tac ‘n’) >> fs[]) >>
  disj2_tac >> drule_all wterm_step >>
  disch_then (qspec_then ‘c’ strip_assume_tac) >> first_x_assum irule >> simp[]
QED

(* MAIN: in a world where only finitely many things arrive, the polling run
   of the protocol server reaches a round after which it performs no
   actions *)
Theorem proto_acts_stop:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃N n1. N ≤ n1 ∧ static_g (EI lfdn) (PM P resp lfdn) s0 N ∧
         ∀n. n1 ≤ n ⇒ gacts (EI lfdn) (PM P resp lfdn) s0 n = []
Proof
  strip_tac >>
  qspecl_then [‘s0’, ‘EI lfdn’, ‘PM P resp lfdn’] mp_tac
    (Q.GENL [‘s0’, ‘ifds’, ‘m’] static_after) >>
  simp[] >> strip_tac >>
  ‘grun_ok (EI lfdn) (PM P resp lfdn) s0’ by metis_tac[proto_grun_ok] >>
  qabbrev_tac ‘M = wmeas (n2w lfdn) (EI lfdn) (PM P resp lfdn) s0
                     (ksg (EI lfdn) (PM P resp lfdn) s0 N)’ >>
  ‘∀v n. M n = v ∧ N ≤ n ⇒
         ∃n1. n ≤ n1 ∧ ∀j. n1 ≤ j ⇒ gacts (EI lfdn) (PM P resp lfdn) s0 j = []’
    suffices_by (disch_then (qspecl_then [‘M N’, ‘N’] mp_tac) >> simp[] >>
                 strip_tac >> qexistsl [‘N’, ‘n1’] >> simp[]) >>
  completeInduct_on ‘v’ >> rpt strip_tac >>
  Cases_on ‘∀j. n ≤ j ⇒ gacts (EI lfdn) (PM P resp lfdn) s0 j = []’
  >- (qexists_tac ‘n’ >> simp[]) >>
  gvs[] >>
  ‘M (SUC j) < M j’
    by (simp[Abbr ‘M’] >> irule meas_act >> fs[]) >>
  ‘M j ≤ M n’
    by (qspecl_then [‘EI lfdn’, ‘PM P resp lfdn’, ‘s0’, ‘N’, ‘n2w lfdn’,
                     ‘ksg (EI lfdn) (PM P resp lfdn) s0 N’] mp_tac
          (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘N’, ‘l’, ‘ks’] wmeas_le) >>
        impl_tac >- fs[] >>
        disch_then (qspecl_then [‘j − n’, ‘n’] mp_tac) >> simp[Abbr ‘M’]) >>
  first_x_assum (qspec_then ‘M (SUC j)’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘SUC j’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘n1’ >> simp[]
QED
