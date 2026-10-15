(*
  The echo handler does nothing on its connection after reading its EOF:
  in its transcript, a read answered Eof is the last pair
  (handler_eof_last).  So in the version-1 run of the echo server, once a
  read of a connection has returned EOF, no later action reads or writes
  that connection (echo_sock_eof_last); the handle layer, which closes a
  connection as soon as a read returns EOF, drops nothing the server does.
*)
Theory asyncHLEof
Ancestors
  words asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncM4ServerUses asyncM4SockModel ffiSpikeSocketFFI
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4SockInv asyncM4EchoRunOk
  asyncM4LiveProg asyncM4ReadSoon
Libs
  preamble

(* In tt, a read of fd answered Eof is the last pair *)
Definition eof_last_def:
  eof_last fd [] = T ∧
  eof_last fd (p :: tt) =
    if p = (asyncServer$Read fd, SOME asyncServer$Eof) then tt = [] else eof_last fd tt
End

Theorem eof_last_APPEND:
  ∀tt1 tt2. eof_last fd (tt1 ++ tt2) ⇔
            eof_last fd tt1 ∧
            (MEM (asyncServer$Read fd, SOME asyncServer$Eof) tt1 ⇒
             tt2 = [] ∧ LAST tt1 = (asyncServer$Read fd, SOME asyncServer$Eof)) ∧
            (¬MEM (asyncServer$Read fd, SOME asyncServer$Eof) tt1 ⇒ eof_last fd tt2)
Proof
  Induct >> rw[eof_last_def] >> Cases_on ‘tt1’ >> gvs[eof_last_def] >> metis_tac[]
QED

(* MAIN: the handler's transcript ends at its EOF *)
Theorem handler_eof_last:
  ∀h. eof_last fd (trans (handler fd) h)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ONCE_REWRITE_TAC[handler_unfold] >> REWRITE_TAC[handler_body_def]
  (* wait until fd is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) h’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[eof_last_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  (* read fd *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (asyncServer$Read fd)) K1) h2’
  >> qspecl_then [‘emit (asyncServer$Read fd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit] >> rw[eof_last_def])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, eof_last_def]
  >> Cases_on ‘res’ >> simp[]
  (* data d: write it back, then continue *)
  >> TRY (rename1 ‘asyncServer$Write fd d’
          >> qspecl_then [‘emit (asyncServer$Write fd d)’, ‘λw. handler fd’, ‘h2'’] mp_tac
               (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
          >> simp[wf_emit, settled_emit] >> strip_tac
          >- simp[trans_emit, eof_last_def]
          >> drule first_done_emit >> strip_tac >> gvs[trans_emit, eof_last_def]
          >> first_x_assum (qspec_then ‘h2''’ mp_tac) >> simp[] >> NO_TAC)
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED

Theorem eof_last_split[local]:
  ∀X. eof_last fd (X ++ (asyncServer$Read fd, SOME asyncServer$Eof) :: Y) ⇒ Y = []
Proof
  Induct >> rw[eof_last_def] >> gvs[]
QED

(* ------------------------------------------------------------------------
   In the version-1 run
   ------------------------------------------------------------------------ *)

(* The socket action reads or writes c *)
Definition sock_on_def:
  sock_on c (asyncM3World$Read c' k) = (c' = c) ∧
  sock_on c (asyncM3World$Write c' bs) = (c' = c) ∧
  sock_on c (asyncM3World$Accept l) = F
End

Theorem sfa_sock_on[local]:
  sock_on c (sfa a) ⇒ ∃fd. n2w fd = c ∧ on_fd fd (a, r)
Proof
  Cases_on ‘a’ >> simp[sfa_def, sock_on_def]
QED

Theorem sfa_eof_read[local]:
  sfa a = asyncM3World$Read c k ⇒ ∃fd. a = asyncServer$Read fd ∧ n2w fd = c
Proof
  Cases_on ‘a’ >> simp[sfa_def]
QED

(* A pair of the model transcript on fd comes after fd's accept, and the
   accepted fds are the handed-out connections *)
Theorem TS_on_fd_lt[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  TS lfdn ifds s0 n = t1 ++ p :: t2 ∧ on_fd fd p ⇒
  MEM fd (accepted (TS lfdn ifds s0 n)) ∧ fd < dimword (:64)
Proof
  strip_tac >>
  qspec_then ‘MAP sfs (ghist ifds (srelabel (server lfdn)) s0 n)’ strip_assume_tac
    (Q.INST [‘lfd’ |-> ‘lfdn’] server_uses_accepted) >>
  first_x_assum (qspec_then ‘fd’ mp_tac) >> REWRITE_TAC[acc_first_MEM] >>
  disch_then (qspecl_then [‘t1’, ‘p’, ‘t2’] mp_tac) >> impl_tac >- fs[] >>
  strip_tac >>
  ‘MEM fd (accepted (TS lfdn ifds s0 n))’
    by (qpat_x_assum ‘TS _ _ _ _ = _’ SUBST1_TAC >> simp[] >>
        disj1_tac >> irule MEM_accepted >> first_assum ACCEPT_TAC) >>
  drule_all accepted_TS >> strip_tac >> gvs[MEM_MAP] >>
  qspec_then ‘y’ mp_tac w2n_lt >> simp[]
QED

Theorem split_EL[local]:
  j < LENGTH l ⇒ l = TAKE j l ++ EL j l :: DROP (j + 1) l
Proof
  strip_tac >>
  ‘DROP j l = EL j l :: DROP (j + 1) l’ by fs[DROP_CONS_EL, ADD1] >>
  ‘l = TAKE j l ++ DROP j l’ by simp[TAKE_DROP] >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  fs[]
QED

(* MAIN: in the version-1 run of the echo server, once a read of c has
   returned EOF, no later performed action reads or writes c *)
Theorem echo_sock_eof_last:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  SP lfdn ifds s0 n = p1 ++ [(asyncM3World$Read c k, Got (SOME []))] ++ p2 ∧
  MEM (a, r) p2 ⇒
  ¬sock_on c a
Proof
  rpt strip_tac >>
  mp_tac echo_sinv >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule echo_trans_split >> strip_tac >>
  ‘grun_ok ifds (srelabel (server lfdn)) s0’ by (irule echo_grun_ok >> simp[]) >>
  (* the model pairs at the two positions *)
  ‘LENGTH tt1 = LENGTH (SP lfdn ifds s0 n)’
    by metis_tac[LENGTH_MAP] >>
  qabbrev_tac ‘i = LENGTH p1’ >>
  ‘∃i'. i < i' ∧ i' < LENGTH (SP lfdn ifds s0 n) ∧ EL i' (SP lfdn ifds s0 n) = (a, r)’
    by (gvs[MEM_EL] >> qexists_tac ‘i + 1 + n'’ >>
        simp[Abbr ‘i’, EL_APPEND2, EL_APPEND1]) >>
  ‘EL i (SP lfdn ifds s0 n) = (asyncM3World$Read c k, Got (SOME []))’
    by (qpat_x_assum ‘SP _ _ _ _ = _’ SUBST1_TAC >>
        qunabbrev_tac ‘i’ >> simp[EL_APPEND_EQN]) >>
  ‘∀j. j < LENGTH tt1 ⇒
       sfa (FST (EL j tt1)) = FST (EL j (SP lfdn ifds s0 n)) ∧
       SND (EL j tt1) = SOME (sfr (SND (EL j (SP lfdn ifds s0 n))))’
    by (rpt gen_tac >> strip_tac >> qpat_x_assum ‘_ = _ ++ p2’ kall_tac >>
        qpat_x_assum ‘MAP _ tt1 = _’ (mp_tac o Q.AP_TERM ‘EL j’) >>
        ‘j < LENGTH (SP lfdn ifds s0 n)’ by fs[] >>
        fs[EL_MAP] >> Cases_on ‘EL j tt1’ >> Cases_on ‘EL j (SP lfdn ifds s0 n)’ >>
        fs[]) >>
  ‘i' < LENGTH tt1’
    by (qpat_x_assum ‘LENGTH tt1 = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  ‘i < LENGTH tt1’
    by (irule LESS_TRANS >> qexists_tac ‘i'’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘_ = _ ++ p2’ kall_tac >> qpat_x_assum ‘MEM _ p2’ kall_tac >>
  (* the model pairs at the two positions *)
  first_assum (qspec_then ‘i’ mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
  qpat_assum ‘EL i _ = (_, Got (SOME []))’ (fn th => REWRITE_TAC[th]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [sfr_def]) >>
  first_assum (qspec_then ‘i'’ mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
  qpat_assum ‘EL i' _ = (a, r)’ (fn th => REWRITE_TAC[th]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum ‘∀j. j < LENGTH tt1 ⇒ _’ kall_tac >>
  qpat_x_assum ‘MAP _ tt1 = _’ kall_tac >>
  qpat_x_assum ‘sfa (FST (EL i tt1)) = _’ (strip_assume_tac o MATCH_MP sfa_eof_read) >>
  ‘EL i tt1 = (asyncServer$Read fd, SOME asyncServer$Eof)’
    by (Cases_on ‘EL i tt1’ >> fs[]) >>
  qspecl_then [‘c’, ‘FST (EL i' tt1)’, ‘SND (EL i' tt1)’] mp_tac
    (Q.GENL [‘c’, ‘a’, ‘r’] sfa_sock_on) >>
  impl_tac >- fs[] >> strip_tac >> rename1 ‘on_fd fd' _’ >>
  ‘on_fd fd' (EL i' tt1)’ by (Cases_on ‘EL i' tt1’ >> fs[]) >>
  (* both fds are handed-out connections, so they are the same *)
  ‘TS lfdn ifds s0 n =
     TAKE i tt1 ++ (asyncServer$Read fd, SOME asyncServer$Eof) :: (DROP (i + 1) tt1 ++ tt2)’
    by (qpat_x_assum ‘TS _ _ _ _ = _’ SUBST1_TAC >>
        qpat_x_assum ‘EL i tt1 = _’ (SUBST1_TAC o SYM) >>
        qspecl_then [‘i’, ‘tt1’] mp_tac (Q.GENL [‘j’, ‘l’] split_EL) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >> simp[]) >>
  ‘TS lfdn ifds s0 n = TAKE i' tt1 ++ EL i' tt1 :: (DROP (i' + 1) tt1 ++ tt2)’
    by (qpat_x_assum ‘TS _ _ _ _ = tt1 ++ _’ SUBST1_TAC >>
        qspecl_then [‘i'’, ‘tt1’] mp_tac (Q.GENL [‘j’, ‘l’] split_EL) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >> simp[]) >>
  ‘MEM fd (accepted (TS lfdn ifds s0 n)) ∧ fd < dimword (:64)’
    by (qspecl_then [‘DROP (i + 1) tt1 ++ tt2’, ‘TAKE i tt1’, ‘s0’,
                     ‘(asyncServer$Read fd, SOME asyncServer$Eof)’, ‘n’, ‘lfdn’, ‘ifds’, ‘fd’]
          mp_tac (Q.GENL [‘t2’, ‘t1’, ‘s0’, ‘p’, ‘n’, ‘lfdn’, ‘ifds’, ‘fd’] TS_on_fd_lt) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
        simp[]) >>
  ‘fd' < dimword (:64)’
    by (qspecl_then [‘DROP (i' + 1) tt1 ++ tt2’, ‘TAKE i' tt1’, ‘s0’, ‘EL i' tt1’, ‘n’,
                     ‘lfdn’, ‘ifds’, ‘fd'’] mp_tac
          (Q.GENL [‘t2’, ‘t1’, ‘s0’, ‘p’, ‘n’, ‘lfdn’, ‘ifds’, ‘fd’] TS_on_fd_lt) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
        simp[]) >>
  ‘fd' = fd’ by (qpat_x_assum ‘n2w fd' = c’ mp_tac >> qpat_x_assum ‘n2w fd = c’ mp_tac >>
                 rpt strip_tac >> rveq >>
                 ‘fd MOD dimword (:64) = fd’ by (irule LESS_MOD >> first_assum ACCEPT_TAC) >>
                 ‘fd' MOD dimword (:64) = fd'’ by (irule LESS_MOD >> first_assum ACCEPT_TAC) >>
                 qpat_x_assum ‘n2w fd = n2w fd'’ mp_tac >> REWRITE_TAC[n2w_11] >>
                 metis_tac[]) >>
  qpat_x_assum ‘fd' = fd’ SUBST_ALL_TAC >>
  (* the handler's transcript ends at the EOF *)
  ‘fresh (TS lfdn ifds s0 n)’ by (irule echo_fresh >> simp[]) >>
  ‘prompt (server lfdn) (MAP sfs (ghist ifds (srelabel (server lfdn)) s0 n))’
    by (irule prompt_ghist >> first_assum ACCEPT_TAC) >>
  qspecl_then [‘lfdn’, ‘fd’] mp_tac (Q.GENL [‘lfd’, ‘fd’] server_handler_view) >>
  disch_then drule_all >> strip_tac >>
  ‘eof_last fd (FILTER (on_fd fd) (TS lfdn ifds s0 n))’ by simp[handler_eof_last] >>
  qpat_x_assum ‘TS _ _ _ _ = TAKE i tt1 ++ _’ (fn th => pop_assum (mp_tac o REWRITE_RULE[th])) >>
  simp[FILTER_APPEND] >> strip_tac >> drule eof_last_split >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >>
  disj1_tac >> qexists_tac ‘EL i' tt1’ >>
  conj_tac >- (simp[MEM_EL] >> qexists_tac ‘i' − (i + 1)’ >> fs[EL_DROP]) >>
  first_assum ACCEPT_TAC
QED
