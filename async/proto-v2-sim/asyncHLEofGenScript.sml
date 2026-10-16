(*
  asyncHLEof's echo_sock_eof_last for ANY server m that uses only the
  connections the world hands it (uses_ok) and ends each connection's
  transcript at its EOF (srv_eof_last): in the version-1 run, once a read
  of c has returned EOF, no later action reads or writes c
  (gen_sock_eof_last).  The proof is echo's, with asyncRunOkGen's generic
  invariant for echo's.
*)
Theory asyncHLEofGen
Ancestors
  words asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncM4ServerUses asyncM4SockModel ffiSpikeSocketFFI
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4SockInv asyncRunOkGen
  asyncM4LiveProg asyncM4ReadSoon asyncHLEof asyncProtoEof
Libs
  preamble

(* The handed-out connections are those the model accepted *)
Theorem accepted_TSg:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  accepted (TSg m ifds s0 n) = MAP w2n (wacc (SPg m ifds s0 n))
Proof
  strip_tac >> drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
  simp[accepted_NONE]
QED

Theorem sfa_sock_on_g[local]:
  sock_on c (sfa a) ⇒ ∃fd. n2w fd = c ∧ on_fd fd (a, r)
Proof
  Cases_on ‘a’ >> simp[sfa_def, sock_on_def]
QED

Theorem sfa_eof_read_g[local]:
  sfa a = asyncM3World$Read c k ⇒ ∃fd. a = asyncServer$Read fd ∧ n2w fd = c
Proof
  Cases_on ‘a’ >> simp[sfa_def]
QED

(* A pair of the model transcript on fd comes after fd's accept, and the
   accepted fds are the handed-out connections *)
Theorem TS_on_fd_lt_g[local]:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  TSg m ifds s0 n = t1 ++ p :: t2 ∧ on_fd fd p ⇒
  MEM fd (accepted (TSg m ifds s0 n)) ∧ fd < dimword (:64)
Proof
  strip_tac >>
  qpat_x_assum ‘uses_ok _ _’ (strip_assume_tac o REWRITE_RULE [uses_ok_def]) >>
  first_x_assum (qspec_then ‘MAP sfs (ghist ifds (srelabel m) s0 n)’ strip_assume_tac) >>
  first_x_assum (qspec_then ‘fd’ mp_tac) >> REWRITE_TAC[acc_first_MEM] >>
  disch_then (qspecl_then [‘t1’, ‘p’, ‘t2’] mp_tac) >> impl_tac >- fs[] >>
  strip_tac >>
  ‘MEM fd (accepted (TSg m ifds s0 n))’
    by (qpat_x_assum ‘TSg _ _ _ _ = _’ SUBST1_TAC >> simp[] >>
        disj1_tac >> irule MEM_accepted >> first_assum ACCEPT_TAC) >>
  drule_all accepted_TSg >> strip_tac >> gvs[MEM_MAP] >>
  qspec_then ‘y’ mp_tac w2n_lt >> simp[]
QED

Theorem split_EL_g[local]:
  j < LENGTH l ⇒ l = TAKE j l ++ EL j l :: DROP (j + 1) l
Proof
  strip_tac >>
  ‘DROP j l = EL j l :: DROP (j + 1) l’ by fs[DROP_CONS_EL, ADD1] >>
  ‘l = TAKE j l ++ DROP j l’ by simp[TAKE_DROP] >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  fs[]
QED

(* MAIN: in the version-1 run of a server m that uses only handed-out
   connections and ends each connection's transcript at its EOF, once a
   read of c has returned EOF, no later performed action reads or writes c *)
Theorem gen_sock_eof_last:
  uses_ok lfdn m ∧ srv_eof_last m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  SPg m ifds s0 n = p1 ++ [(asyncM3World$Read c k, Got (SOME []))] ++ p2 ∧
  MEM (a, r) p2 ⇒
  ¬sock_on c a
Proof
  rpt strip_tac >>
  drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  ‘grun_ok ifds (srelabel m) s0’ by (irule gen_grun_ok >> simp[]) >>
  (* the model pairs at the two positions *)
  ‘LENGTH tt1 = LENGTH (SPg m ifds s0 n)’
    by metis_tac[LENGTH_MAP] >>
  qabbrev_tac ‘i = LENGTH p1’ >>
  ‘∃i'. i < i' ∧ i' < LENGTH (SPg m ifds s0 n) ∧ EL i' (SPg m ifds s0 n) = (a, r)’
    by (gvs[MEM_EL] >> qexists_tac ‘i + 1 + n'’ >>
        simp[Abbr ‘i’, EL_APPEND2, EL_APPEND1]) >>
  ‘EL i (SPg m ifds s0 n) = (asyncM3World$Read c k, Got (SOME []))’
    by (qpat_x_assum ‘SPg _ _ _ _ = _’ SUBST1_TAC >>
        qunabbrev_tac ‘i’ >> simp[EL_APPEND_EQN]) >>
  ‘∀j. j < LENGTH tt1 ⇒
       sfa (FST (EL j tt1)) = FST (EL j (SPg m ifds s0 n)) ∧
       SND (EL j tt1) = SOME (sfr (SND (EL j (SPg m ifds s0 n))))’
    by (rpt gen_tac >> strip_tac >> qpat_x_assum ‘_ = _ ++ p2’ kall_tac >>
        qpat_x_assum ‘MAP _ tt1 = _’ (mp_tac o Q.AP_TERM ‘EL j’) >>
        ‘j < LENGTH (SPg m ifds s0 n)’ by fs[] >>
        fs[EL_MAP] >> Cases_on ‘EL j tt1’ >> Cases_on ‘EL j (SPg m ifds s0 n)’ >>
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
  qpat_x_assum ‘sfa (FST (EL i tt1)) = _’ (strip_assume_tac o MATCH_MP sfa_eof_read_g) >>
  ‘EL i tt1 = (asyncServer$Read fd, SOME asyncServer$Eof)’
    by (Cases_on ‘EL i tt1’ >> fs[]) >>
  qspecl_then [‘c’, ‘FST (EL i' tt1)’, ‘SND (EL i' tt1)’] mp_tac
    (Q.GENL [‘c’, ‘a’, ‘r’] sfa_sock_on_g) >>
  impl_tac >- fs[] >> strip_tac >> rename1 ‘on_fd fd' _’ >>
  ‘on_fd fd' (EL i' tt1)’ by (Cases_on ‘EL i' tt1’ >> fs[]) >>
  (* both fds are handed-out connections, so they are the same *)
  ‘TSg m ifds s0 n =
     TAKE i tt1 ++ (asyncServer$Read fd, SOME asyncServer$Eof) :: (DROP (i + 1) tt1 ++ tt2)’
    by (qpat_x_assum ‘TSg _ _ _ _ = _’ SUBST1_TAC >>
        qpat_x_assum ‘EL i tt1 = _’ (SUBST1_TAC o SYM) >>
        qspecl_then [‘i’, ‘tt1’] mp_tac (Q.GENL [‘j’, ‘l’] split_EL_g) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >> simp[]) >>
  ‘TSg m ifds s0 n = TAKE i' tt1 ++ EL i' tt1 :: (DROP (i' + 1) tt1 ++ tt2)’
    by (qpat_x_assum ‘TSg _ _ _ _ = tt1 ++ _’ SUBST1_TAC >>
        qspecl_then [‘i'’, ‘tt1’] mp_tac (Q.GENL [‘j’, ‘l’] split_EL_g) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >> simp[]) >>
  ‘MEM fd (accepted (TSg m ifds s0 n)) ∧ fd < dimword (:64)’
    by (qspecl_then [‘DROP (i + 1) tt1 ++ tt2’, ‘TAKE i tt1’, ‘s0’,
                     ‘(asyncServer$Read fd, SOME asyncServer$Eof)’, ‘n’, ‘lfdn’, ‘ifds’, ‘fd’]
          mp_tac (Q.GENL [‘t2’, ‘t1’, ‘s0’, ‘p’, ‘n’, ‘lfdn’, ‘ifds’, ‘fd’] TS_on_fd_lt_g) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
        simp[]) >>
  ‘fd' < dimword (:64)’
    by (qspecl_then [‘DROP (i' + 1) tt1 ++ tt2’, ‘TAKE i' tt1’, ‘s0’, ‘EL i' tt1’, ‘n’,
                     ‘lfdn’, ‘ifds’, ‘fd'’] mp_tac
          (Q.GENL [‘t2’, ‘t1’, ‘s0’, ‘p’, ‘n’, ‘lfdn’, ‘ifds’, ‘fd’] TS_on_fd_lt_g) >>
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
  ‘fresh (TSg m ifds s0 n)’ by (irule gen_fresh >> simp[]) >>
  ‘prompt m (MAP sfs (ghist ifds (srelabel m) s0 n))’
    by (irule prompt_ghist >> first_assum ACCEPT_TAC) >>
  ‘eof_last fd (FILTER (on_fd fd) (TSg m ifds s0 n))’
    by metis_tac[srv_eof_last_def] >>
  qpat_x_assum ‘TSg _ _ _ _ = TAKE i tt1 ++ _’ (fn th => pop_assum (mp_tac o REWRITE_RULE[th])) >>
  simp[FILTER_APPEND] >> strip_tac >> drule eof_last_split >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >>
  disj1_tac >> qexists_tac ‘EL i' tt1’ >>
  conj_tac >- (simp[MEM_EL] >> qexists_tac ‘i' − (i + 1)’ >> fs[EL_DROP]) >>
  first_assum ACCEPT_TAC
QED
