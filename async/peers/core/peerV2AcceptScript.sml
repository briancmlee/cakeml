(*
  A program that answers every client that sends a given request accepts
  every client that connects (version 2).

  If client j connects but the run never accepts it, change the world:
  right after j's connect, j sends the bytes bs (addreq).  The run cannot
  tell (peerV2Hide), so it is the program's run there too, and there
  j has sent bs, so the program accepts it: a contradiction.
*)
Theory peerV2Accept
Ancestors
  llist ffi semantics socketWorld lifetimeWorld lifetimeFair EchoEpisodesSpec
  peerV2Sim peerEchoEpisodes peerEchoEpisodesConv peerV2Hide
Libs
  preamble

val _ = numLib.prefer_num ();

(* ------------------------------------------------------------------------
   Clients not yet connected have sent nothing
   ------------------------------------------------------------------------ *)

Theorem step_ok2_data[local]:
  ∀xs s. step_ok2 s xs ∧ data_of j xs ≠ [] ⇒
         j < LENGTH s.clients + LENGTH (FILTER is_conn2 xs)
Proof
  Induct >- simp[data_of_def] >> Cases >> rpt gen_tac >> strip_tac >>
  fs[step_ok2_def, arrival_ok2_def, is_conn2_def] >>
  first_x_assum drule >>
  fs[data_of_def, deliver2_def, update_client_def] >> rw[] >> fs[] >>
  Cases_on ‘n = j’ >> fs[]
QED

Theorem sent2_unconn:
  lifetime_world lfd sk ∧ nconn sk n ≤ j ⇒ sent2_upto j n sk = []
Proof
  strip_tac >>
  ‘∀m. m ≤ n ⇒ sent2_upto j m sk = []’ suffices_by simp[] >>
  Induct >- simp[sent2_upto_def, arrivals2_upto_def] >> strip_tac >>
  ‘sent2_upto j m sk = []’ by fs[] >> simp[sent2_upto_SUC] >>
  CCONTR_TAC >>
  ‘step_ok2 (ticks2 m sk) (fut_step sk.future m)’
    by (fs[lifetime_world_def, lifetime_fair_def] >>
        first_x_assum (qspec_then ‘m’ mp_tac) >> simp[next_step2_fut, ticks2_future]) >>
  drule_all step_ok2_data >>
  ‘LENGTH (ticks2 m sk).clients = nconn sk m’
    by (fs[lifetime_world_def] >> drule ticks2_clients >> simp[]) >>
  ‘nconn sk (SUC m) = nconn sk m + LENGTH (FILTER is_conn2 (fut_step sk.future m))’
    by simp[nconn_def, arrivals2_upto_SUC, FILTER_APPEND] >>
  ‘nconn sk (SUC m) ≤ nconn sk n’ by simp[nconn_mono] >>
  decide_tac
QED

(* ------------------------------------------------------------------------
   One step changed
   ------------------------------------------------------------------------ *)

Definition lmod_def:
  lmod n g (f : 'a llist) =
    LUNFOLD (λ(i, l). case LHD l of
                      | NONE => NONE
                      | SOME x => SOME ((i + 1, THE (LTL l)), if i = n then g x else x)) (0, f)
End

Theorem LNTH_lmod_from[local]:
  ∀m i l. LNTH m (LUNFOLD (λ(i, l). case LHD l of
                                    | NONE => NONE
                                    | SOME x => SOME ((i + 1, THE (LTL l)),
                                                      if i = n then g x else x)) (i, l)) =
          OPTION_MAP (λx. if i + m = n then g x else x) (LNTH m l)
Proof
  Induct >> rpt gen_tac >> qspec_then ‘l’ strip_assume_tac llist_CASES >> simp[] >>
  simp[ADD1]
QED

Theorem LNTH_lmod:
  LNTH m (lmod n g f) = OPTION_MAP (λx. if m = n then g x else x) (LNTH m f)
Proof
  simp[lmod_def, LNTH_lmod_from]
QED

Theorem fut_step_lmod:
  fut_step (lmod n g f) m =
    if m = n ∧ LNTH n f ≠ NONE then g (fut_step f n) else fut_step f m
Proof
  simp[fut_step_def, LNTH_lmod] >> Cases_on ‘LNTH m f’ >> rw[] >> fs[]
QED

(* Insert d right after the c-th connect of a step *)
Definition ins_conn_def:
  ins_conn c d [] = [] ∧
  ins_conn c d (a :: as) =
    if is_conn2 a then (if c = 0 then a :: d :: as else a :: ins_conn (c − 1) d as)
    else a :: ins_conn c d as
End

Theorem ins_conn_filter[local]:
  ∀st c. FILTER (λa. ¬touches j a) (ins_conn c (Data2 j bs) st) = FILTER (λa. ¬touches j a) st
Proof
  Induct >> rw[ins_conn_def, touches_def]
QED

Theorem ins_conn_conns[local]:
  ∀st c. FILTER is_conn2 (ins_conn c (Data2 j bs) st) = FILTER is_conn2 st
Proof
  Induct >> rw[ins_conn_def, is_conn2_def]
QED

(* ------------------------------------------------------------------------
   Worlds that differ in one client's unread bytes
   ------------------------------------------------------------------------ *)

Definition dsame_def:
  dsame j (s:sockets2) (s':sockets2) ⇔
    s'.listening = s.listening ∧ s'.open_fds = s.open_fds ∧ s'.reserved = s.reserved ∧
    s'.alloc = s.alloc ∧ LENGTH s'.clients = LENGTH s.clients ∧
    (∀i. i ≠ j ⇒ EL i s'.clients = EL i s.clients) ∧
    (j < LENGTH s.clients ⇒ (EL j s'.clients).peer_closed = (EL j s.clients).peer_closed)
End

Theorem dsame_deliver2[local]:
  dsame j s s' ⇒ dsame j (deliver2 s a) (deliver2 s' a)
Proof
  Cases_on ‘a’ >> rw[dsame_def, deliver2_def, update_client_def] >> gvs[] >>
  gvs[EL_APPEND_EQN, EL_LUPDATE] >> rw[] >> gvs[] >>
  Cases_on ‘n = j’ >> gvs[]
QED

Theorem dsame_data[local]:
  dsame j s s' ⇒ dsame j s (deliver2 s' (Data2 j bs))
Proof
  rw[dsame_def, deliver2_def, update_client_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem arrival_ok2_dsame[local]:
  dsame j s s' ⇒ (arrival_ok2 s' a ⇔ arrival_ok2 s a)
Proof
  Cases_on ‘a’ >> rw[dsame_def, arrival_ok2_def] >> Cases_on ‘n = j’ >> gvs[] >>
  Cases_on ‘j < LENGTH s.clients’ >> fs[]
QED

Theorem FOLDL_dsame[local]:
  ∀st s s'. dsame j s s' ⇒ dsame j (FOLDL deliver2 s st) (FOLDL deliver2 s' st)
Proof
  Induct >> simp[dsame_deliver2]
QED

Theorem step_ok2_dsame[local]:
  ∀st s s'. dsame j s s' ⇒ (step_ok2 s' st ⇔ step_ok2 s st)
Proof
  Induct >> simp[step_ok2_def] >> rpt strip_tac >>
  drule_then (qspec_then ‘h’ assume_tac) arrival_ok2_dsame >>
  metis_tac[dsame_deliver2]
QED

Theorem FOLDL_dsame_ins[local]:
  ∀st c s s'. dsame j s s' ⇒
              dsame j (FOLDL deliver2 s st) (FOLDL deliver2 s' (ins_conn c (Data2 j bs) st))
Proof
  Induct >> rw[ins_conn_def] >>
  TRY (first_x_assum irule >> simp[dsame_deliver2] >> NO_TAC) >>
  irule FOLDL_dsame >> irule dsame_data >> simp[dsame_deliver2]
QED

(* The inserted arrival is effective: client jj has just connected *)
Theorem step_ok2_ins[local]:
  ∀jj st c s s'. step_ok2 s st ∧ dsame jj s s' ∧ LENGTH s.clients + c = jj ∧
                 c < LENGTH (FILTER is_conn2 st) ⇒
                 step_ok2 s' (ins_conn c (Data2 jj bs) st)
Proof
  gen_tac >> Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘step_ok2 _ (_ :: _)’ (strip_assume_tac o REWRITE_RULE[step_ok2_def]) >>
  ‘arrival_ok2 s' h’
    by (drule_then (qspec_then ‘h’ assume_tac) arrival_ok2_dsame >> fs[]) >>
  ‘dsame jj (deliver2 s h) (deliver2 s' h)’ by (irule dsame_deliver2 >> fs[]) >>
  ‘LENGTH s'.clients = LENGTH s.clients ∧ s'.listening = s.listening’ by fs[dsame_def] >>
  reverse (Cases_on ‘is_conn2 h’)
  >- (‘LENGTH (deliver2 s h).clients = LENGTH s.clients’
        by (Cases_on ‘h’ >> fs[is_conn2_def, deliver2_def, update_client_def] >> rw[]) >>
      simp[ins_conn_def, step_ok2_def] >>
      first_x_assum (qspecl_then [‘c’, ‘deliver2 s h’, ‘deliver2 s' h’] mp_tac) >>
      impl_tac >- fs[] >> simp[]) >>
  Cases_on ‘h’ >> RULE_ASSUM_TAC (REWRITE_RULE[is_conn2_def]) >> fs[] >>
  ‘LENGTH (deliver2 s (Connect2 c')).clients = LENGTH s.clients + 1’
    by fs[arrival_ok2_def, deliver2_def] >>
  Cases_on ‘c = 0’
  >- (simp[ins_conn_def, is_conn2_def, step_ok2_def] >> conj_tac
      >- (fs[arrival_ok2_def, deliver2_def] >> simp[EL_APPEND_EQN, empty_conn_def]) >>
      ‘dsame jj (deliver2 s (Connect2 c'))
                (deliver2 (deliver2 s' (Connect2 c')) (Data2 jj bs))’
        by (irule dsame_data >> fs[]) >>
      drule step_ok2_dsame >> disch_then (fn th => simp[th])) >>
  simp[ins_conn_def, is_conn2_def, step_ok2_def] >>
  first_x_assum (qspecl_then [‘c − 1’, ‘deliver2 s (Connect2 c')’,
                              ‘deliver2 s' (Connect2 c')’] mp_tac) >>
  impl_tac >- fs[is_conn2_def] >> simp[]
QED

Theorem data_of_cons[local]:
  data_of j (a :: as) = data_of j [a] ++ data_of j as
Proof
  simp[data_of_def]
QED

(* Client jj's first bytes are those inserted *)
Theorem data_ins[local]:
  ∀jj st c s. step_ok2 s st ∧ LENGTH s.clients + c = jj ∧ c < LENGTH (FILTER is_conn2 st) ⇒
              bs ≼ data_of jj (ins_conn c (Data2 jj bs) st)
Proof
  gen_tac >> Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘step_ok2 _ (_ :: _)’ (strip_assume_tac o REWRITE_RULE[step_ok2_def]) >>
  reverse (Cases_on ‘is_conn2 h’)
  >- (‘LENGTH (deliver2 s h).clients = LENGTH s.clients’
        by (Cases_on ‘h’ >> fs[is_conn2_def, deliver2_def, update_client_def] >> rw[]) >>
      ‘data_of jj [h] = []’
        by (Cases_on ‘h’ >> fs[is_conn2_def, data_of_def, arrival_ok2_def] >>
            rw[] >> decide_tac) >>
      simp[ins_conn_def] >> ONCE_REWRITE_TAC[data_of_cons] >> simp[] >>
      first_x_assum (qspecl_then [‘c’, ‘deliver2 s h’] mp_tac) >>
      impl_tac >- fs[] >> simp[]) >>
  Cases_on ‘h’ >> RULE_ASSUM_TAC (REWRITE_RULE[is_conn2_def]) >> fs[] >>
  Cases_on ‘c = 0’ >> simp[ins_conn_def, is_conn2_def]
  >- simp[data_of_def] >>
  ONCE_REWRITE_TAC[data_of_cons] >> simp[data_of_def] >> REWRITE_TAC[GSYM data_of_def] >>
  first_x_assum (qspecl_then [‘c − 1’, ‘deliver2 s (Connect2 c')’] mp_tac) >>
  impl_tac
  >- (‘LENGTH (deliver2 s (Connect2 c')).clients = LENGTH s.clients + 1’
        by fs[arrival_ok2_def, deliver2_def] >>
      fs[is_conn2_def]) >>
  simp[]
QED

Theorem tick2_FOLDL[local]:
  ∀t. ∃f. tick2 t = FOLDL deliver2 t (next_step2 t) with future := f
Proof
  rw[tick2_def, next_step2_def] >> CASE_TAC >> simp[FOLDL_deliver2_with_future]
  >- (qexists_tac ‘t.future’ >> simp[lifetimeWorldTheory.sockets2_component_equality]) >>
  metis_tac[]
QED

Theorem dsame_with_future[local]:
  (dsame j (s with future := f) s' ⇔ dsame j s s') ∧
  (dsame j s (s' with future := f) ⇔ dsame j s s')
Proof
  simp[dsame_def]
QED

(* ------------------------------------------------------------------------
   The world with the request
   ------------------------------------------------------------------------ *)

(* Client j connects in step n0 *)
Theorem conn_step[local]:
  ∀n. j < nconn sk n ⇒ ∃n0. nconn sk n0 ≤ j ∧ j < nconn sk (SUC n0)
Proof
  Induct >- simp[nconn_def, arrivals2_upto_def] >>
  rpt strip_tac >> Cases_on ‘j < nconn sk n’ >- metis_tac[] >>
  qexists_tac ‘n’ >> fs[]
QED

Definition addreq_def:
  addreq j bs n0 (sk:sockets2) =
    sk with future := lmod n0 (ins_conn (j − nconn sk n0) (Data2 j bs)) sk.future
End

Theorem nconn_SUC[local]:
  nconn s (SUC n) = nconn s n + LENGTH (FILTER is_conn2 (fut_step s.future n))
Proof
  simp[nconn_def, arrivals2_upto_SUC, FILTER_APPEND]
QED

(* MAIN: the world with client j's request *)
Theorem addreq_props:
  lifetime_world lfd sk ∧ nconn sk n0 ≤ j ∧ j < nconn sk (SUC n0) ⇒
  let sk' = addreq j bs n0 sk in
  lifetime_world lfd sk' ∧ hrel j sk sk' ∧ (∀n. nconn sk' n = nconn sk n) ∧
  sk'.reserved = sk.reserved ∧ bs ≼ sent2_upto j (SUC n0) sk'
Proof
  strip_tac >> simp[] >> qabbrev_tac ‘sk' = addreq j bs n0 sk’ >>
  qabbrev_tac ‘c = j − nconn sk n0’ >>
  ‘LNTH n0 sk.future ≠ NONE’
    by (strip_tac >> fs[nconn_SUC, fut_step_def]) >>
  ‘∀m. fut_step sk'.future m =
       if m = n0 then ins_conn c (Data2 j bs) (fut_step sk.future n0) else fut_step sk.future m’
    by rw[Abbr ‘sk'’, addreq_def, fut_step_lmod] >>
  ‘sk'.listening = sk.listening ∧ sk'.clients = sk.clients ∧ sk'.open_fds = sk.open_fds ∧
   sk'.alloc = sk.alloc ∧ sk'.reserved = sk.reserved’ by simp[Abbr ‘sk'’, addreq_def] >>
  ‘∀n. nconn sk' n = nconn sk n’
    by (Induct >- simp[nconn_def, arrivals2_upto_def] >>
        asm_simp_tac (srw_ss()) [nconn_SUC] >> rw[ins_conn_conns]) >>
  ‘hfut j sk'.future = hfut j sk.future’
    by (simp[LNTH_EQ, Abbr ‘sk'’, addreq_def, LNTH_lmod] >> rw[] >>
        Cases_on ‘LNTH n sk.future’ >> rw[ins_conn_filter]) >>
  ‘hrel j sk sk'’ by simp[hrel_def] >>
  simp[] >>
  (* the steps along the way *)
  ‘lifetime_fair sk’ by fs[lifetime_world_def] >>
  ‘∀m. dsame j (ticks2 m sk) (ticks2 m sk')’
    by (Induct >- simp[ticks2_def, dsame_def] >>
        simp[ticks2_SUC'] >>
        qspec_then ‘ticks2 m sk’ strip_assume_tac tick2_FOLDL >>
        qspec_then ‘ticks2 m sk'’ strip_assume_tac tick2_FOLDL >>
        simp[dsame_with_future, next_step2_fut, ticks2_future] >>
        rw[] >- (irule FOLDL_dsame_ins >> simp[]) >> irule FOLDL_dsame >> simp[]) >>
  ‘LENGTH (ticks2 n0 sk).clients = nconn sk n0’
    by (fs[lifetime_world_def] >> drule ticks2_clients >> simp[]) >>
  ‘step_ok2 (ticks2 n0 sk) (fut_step sk.future n0)’
    by (qpat_x_assum ‘lifetime_fair sk’ mp_tac >>
        simp[lifetime_fair_def, next_step2_fut, ticks2_future] >> metis_tac[ADD_0]) >>
  ‘LENGTH (ticks2 n0 sk).clients + c = j ∧
   c < LENGTH (FILTER is_conn2 (fut_step sk.future n0))’
    by (fs[Abbr ‘c’, nconn_SUC] >> decide_tac) >>
  ‘lifetime_world lfd sk'’
    by (‘sk.listening = [(lfd,[])] ∧ sk.clients = [] ∧ sk.open_fds = [] ∧ alloc_ok sk.alloc’
          by fs[lifetime_world_def] >>
        simp[lifetime_world_def, lifetime_fair_def] >> gen_tac >>
        simp[next_step2_fut, ticks2_future] >>
        qpat_assum ‘∀m. fut_step sk'.future m = _’ (fn th => REWRITE_TAC[th]) >>
        ‘step_ok2 (ticks2 n sk) (fut_step sk.future n)’
          by (qpat_x_assum ‘lifetime_fair sk’ mp_tac >>
              simp[lifetime_fair_def, next_step2_fut, ticks2_future]) >>
        first_assum (qspec_then ‘n’ assume_tac) >>
        Cases_on ‘n = n0’
        >- (qpat_x_assum ‘n = n0’ SUBST_ALL_TAC >> simp[] >>
            irule step_ok2_ins >> conj_tac >- fs[] >>
            qexists_tac ‘ticks2 n0 sk’ >> fs[]) >>
        simp[] >> drule step_ok2_dsame >> disch_then (fn th => simp[th])) >>
  simp[] >>
  simp[sent2_upto_SUC] >>
  ‘sent2_upto j n0 sk' = []’ by (irule sent2_unconn >> simp[] >> qexists_tac ‘lfd’ >> simp[]) >>
  simp[] >>
  qpat_assum ‘∀m. fut_step sk'.future m = _’ (fn th => REWRITE_TAC[th]) >> simp[] >>
  irule data_ins >> conj_tac >- fs[] >> qexists_tac ‘ticks2 n0 sk’ >> fs[]
QED

(* ------------------------------------------------------------------------
   Every client is accepted
   ------------------------------------------------------------------------ *)

(* MAIN: if, in every bounded version-2 server world, the program accepts
   each client that has sent bs, then it accepts each client that
   connects *)
Theorem accept_all:
  (∀sk io j n.
     lifetime_world lfd sk ∧ (∀m. nconn sk m ≤ N) ∧ LENGTH sk.reserved + N + 3 < dimword (:64) ∧
     semantics_prog (init_state (lifetime_ffi sk)) init_env prog (Diverge io) ∧
     bs ≼ sent2_upto j n sk ⇒
     ∃evs. LPREFIX (fromList evs) io ∧ j < LENGTH (accepted_fds evs)) ∧
  lifetime_world lfd sk ∧ (∀m. nconn sk m ≤ N) ∧ LENGTH sk.reserved + N + 3 < dimword (:64) ∧
  semantics_prog (init_state (lifetime_ffi sk)) init_env prog (Diverge io) ∧ j < nconn sk n ⇒
  ∃evs. LPREFIX (fromList evs) io ∧ j < LENGTH (accepted_fds evs)
Proof
  strip_tac >> CCONTR_TAC >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ LENGTH (accepted_fds evs) ≤ j’
    by (rpt strip_tac >> CCONTR_TAC >> fs[NOT_LESS_EQUAL] >> metis_tac[]) >>
  drule_all conn_step >> strip_tac >>
  drule_all addreq_props >>
  disch_then (qspec_then ‘bs’ (strip_assume_tac o SIMP_RULE std_ss [LET_THM])) >>
  ‘semantics_prog (init_state (lifetime_ffi (addreq j bs n0 sk))) init_env prog (Diverge io)’
    by (irule hide_diverge >> simp[] >> metis_tac[lifetime_world_qinv]) >>
  qpat_x_assum ‘∀sk io j n. _’ (qspecl_then [‘addreq j bs n0 sk’, ‘io’, ‘j’, ‘SUC n0’] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >> metis_tac[]
QED
