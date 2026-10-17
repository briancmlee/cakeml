(*
  Moonshot liveness: the composition from the obligations,
  moonshot_served_of_obs_claim PROVED.

  Per logical connection i (conn_done_of_obs): the client's episode ep i
  has a channel c (the run's ghost run_css, by B2's sinv), connected to
  a; connect_pairs pairs it with a front ja of the proxy (topology_ob);
  proxy_ob gives the backend jb, which connect_pairs pairs with KV's jk;
  then chain_served and moonshot_chain_drains, with their X instantiated
  as "X or the connection is done", give served and sent-all, hence done.
  Every escape "an own chain end has ended" is X or done by closes_ob.

   - episodes and channels: run_css grows by appending (run_css_prefix),
     traces grow by appending (ptr_prefix), so roles, sent and received
     bytes of an episode only grow;
   - ep_sent_chan: an episode's sent bytes are a prefix of its channel's
     (pinv; an episode on fd 0 gets no bytes, ep_io_fd0).
*)
Theory moonshotLiveCompose
Ancestors
  moonshotLiveSetup moonshotLiveObs moonshotLiveServed moonshotLiveChain moonshotLiveDrains
  moonshotLiveDeliver moonshotLiveProjInf moonshotLiveStmts l0sysStep l0sysInv l0sysRun
  l0sysEpisodes l0sysFair l0sys l0sysMono l0sysCausal
Libs
  preamble

(* ------------------------------------------------------------------------
   The ghost along the run
   ------------------------------------------------------------------------ *)

Theorem irun_sinv_css:
  l0sys_irun ps ss rs ⇒ ∀n. sinv (GENLIST rs n) (ss n) (run_css ss rs n)
Proof
  strip_tac >> Induct
  >- (simp[run_css_def] >> irule sinv_init >> qexists_tac ‘ps’ >>
      fs[l0sys_irun_def] >> rw[] >> irule l0_rely_small_ch >> fs[sys_init_def, LET_THM]) >>
  simp[run_css_def, GENLIST, SNOC_APPEND] >> irule sinv_step >> fs[l0sys_irun_def]
QED

Theorem run_css_prefix:
  ∀d n. ∃l. run_css ss rs (n + d) k = run_css ss rs n k ++ l
Proof
  Induct >> simp[] >> gen_tac >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  rewrite_tac[run_css_def] >> Cases_on ‘rs (n + d)’ >>
  rw[step_css_def, call_css_def, combinTheory.APPLY_UPDATE_THM] >> gs[]
QED

Theorem run_css_EL:
  j < LENGTH (run_css ss rs n k) ∧ n ≤ n' ⇒
  j < LENGTH (run_css ss rs n' k) ∧ EL j (run_css ss rs n' k) = EL j (run_css ss rs n k)
Proof
  strip_tac >> qspecl_then [‘n' − n’, ‘n’] strip_assume_tac run_css_prefix >>
  ‘n + (n' − n) = n'’ by simp[] >> fs[EL_APPEND1]
QED

Theorem ptr_prefix:
  n ≤ n' ⇒ ∃l. ptr rs k n' = ptr rs k n ++ l
Proof
  rw[ptr_def] >> ‘∃d. n' = d + n’ by (qexists_tac ‘n' − n’ >> simp[]) >>
  pop_assum SUBST1_TAC >> rewrite_tac[GENLIST_APPEND, proc_events_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Episodes only grow
   ------------------------------------------------------------------------ *)

Theorem ep_io_append:
  ∀evs opn n. ep_io sel j opn n evs ≼ ep_io sel j opn n (evs ++ evs')
Proof
  Induct >> simp[ep_io_def] >> rpt gen_tac >> every_case_tac >> simp[]
QED

Theorem ep_roles_append:
  ∀evs lst. ep_roles lst evs ≼ ep_roles lst (evs ++ evs')
Proof
  Induct >> simp[ep_roles_def] >> rpt gen_tac >> every_case_tac >> simp[]
QED

Theorem ep_sent_mono:
  n ≤ n' ⇒ l0_ep_sent j (ptr rs k n) ≼ l0_ep_sent j (ptr rs k n')
Proof
  strip_tac >> drule ptr_prefix >> disch_then (qspecl_then [‘rs’, ‘k’] strip_assume_tac) >>
  simp[l0_ep_sent_def, ep_io_append]
QED

Theorem ep_recvd_mono:
  n ≤ n' ⇒ l0_ep_recvd j (ptr rs k n) ≼ l0_ep_recvd j (ptr rs k n')
Proof
  strip_tac >> drule ptr_prefix >> disch_then (qspecl_then [‘rs’, ‘k’] strip_assume_tac) >>
  simp[l0_ep_recvd_def, ep_io_append]
QED

Theorem ep_role_mono:
  l0_ep_role j (ptr rs k n) = SOME r ∧ n ≤ n' ⇒ l0_ep_role j (ptr rs k n') = SOME r
Proof
  strip_tac >> drule ptr_prefix >> disch_then (qspecl_then [‘rs’, ‘k’] strip_assume_tac) >>
  qspecl_then [‘ptr rs k n’, ‘[]’] mp_tac (Q.GEN ‘evs'’ ep_roles_append |> Q.SPEC ‘l’) >>
  fs[l0_ep_role_def, IS_PREFIX_APPEND] >> rw[] >> fs[EL_APPEND1]
QED

Theorem served_by_mono:
  served_by rs cl jep rq n ∧ n ≤ n' ⇒ served_by rs cl jep rq n'
Proof
  rw[served_by_def] >> qexists_tac ‘ans’ >> simp[] >>
  metis_tac[IS_PREFIX_TRANS, ep_recvd_mono]
QED

Theorem done_by_mono:
  done_by rs jep rq n ∧ n ≤ n' ∧ (∀n. l0_ep_sent jep (ptr rs 0 n) ≼ brequests rq) ⇒
  done_by rs jep rq n'
Proof
  rw[done_by_def] >- metis_tac[IS_PREFIX_ANTISYM, ep_sent_mono] >>
  metis_tac[served_by_mono]
QED

Theorem kv_answers_mono:
  kv_answers m X ss e ∧ (X ⇒ Y) ⇒ kv_answers m Y ss e
Proof
  rw[kv_answers_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   An episode's channel
   ------------------------------------------------------------------------ *)

Theorem ep_fds_cons:
  (ev_new ev = NONE ⇒ ep_fds (ev :: evs) = ep_fds evs) ∧
  (ev_new ev = SOME (f, r) ⇒ ep_fds (ev :: evs) = f :: ep_fds evs)
Proof
  simp[ep_fds_def]
QED

(* An episode on fd 0 gets no bytes: its number never enters opn *)
Theorem ep_io_fd0:
  ∀evs opn n. (∀f. ALOOKUP opn f ≠ SOME j) ∧
              (n ≤ j ∧ j − n < LENGTH (ep_fds evs) ⇒ EL (j − n) (ep_fds evs) = 0w) ⇒
              ep_io sel j opn n evs = []
Proof
  Induct >> simp[ep_io_def] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (every_case_tac >> fs[]) >>
  Cases_on ‘ev_new h’ >> simp[]
  >- (first_x_assum irule >> fs[ep_fds_cons]) >>
  PairCases_on ‘x’ >> simp[] >>
  ‘ep_fds (h::evs) = x0 :: ep_fds evs’ by metis_tac[ep_fds_cons] >>
  pop_assum (fn th => fs[th]) >>
  first_x_assum irule >> conj_tac
  >- (rw[] >> gvs[] >> rw[] >> strip_tac >> gvs[]) >>
  rw[] >> ‘j − n = SUC (j − (n + 1))’ by simp[] >> fs[]
QED

Theorem ep_sent_chan:
  pinv evs w cs ∧ j < LENGTH cs ⇒ l0_ep_sent j evs ≼ (EL (EL j cs) w.chans).sent
Proof
  strip_tac >> Cases_on ‘EL j (ep_fds evs) = 0w’
  >- (‘l0_ep_sent j evs = []’ suffices_by simp[] >>
      simp[l0_ep_sent_def] >> irule ep_io_fd0 >> simp[]) >>
  fs[pinv_def, l0_ep_sent_def]
QED

Theorem irun_pk:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ⇒ pk (GENLIST rs n) (ss n) (run_css ss rs n) k
Proof
  strip_tac >> drule irun_sinv_css >> disch_then (qspec_then ‘n’ mp_tac) >>
  ‘LENGTH (ss n).procs = LENGTH ps’ by metis_tac[irun_procs_length] >>
  simp[sinv_def]
QED

Theorem ep_connected_chan:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ l0_ep_role j (ptr rs k n) = SOME (Connected p) ⇒
  j < LENGTH (run_css ss rs n k) ∧ ep_chan ss rs k j (EL j (run_css ss rs n k)) ∧
  is_end (ss n) (k, EL j (run_css ss rs n k)) ∧
  (ss n).target (k, EL j (run_css ss rs n k)) = SOME p
Proof
  strip_tac >> drule_all irun_pk >> disch_then (qspec_then ‘n’ mp_tac) >>
  ‘LENGTH (ss n).procs = LENGTH ps’ by metis_tac[irun_procs_length] >>
  fs[ptr_def, l0_ep_role_def, LENGTH_ep_roles] >> simp[pk_def, LET_THM] >> strip_tac >>
  ‘j < LENGTH (run_css ss rs n k)’ by fs[pinv_def] >>
  rpt conj_tac
  >- simp[]
  >- (simp[ep_chan_def] >> metis_tac[])
  >- (simp[is_end_def] >> fs[pinv_def, EVERY_EL])
  >- (first_x_assum irule >> simp[])
QED

Theorem ep_sent_le:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ j < LENGTH (run_css ss rs n k) ⇒
  l0_ep_sent j (ptr rs k n) ≼ sent_at ss (k, EL j (run_css ss rs n k)) n
Proof
  strip_tac >> drule_all irun_pk >> disch_then (qspec_then ‘n’ mp_tac) >>
  simp[pk_def, LET_THM, sent_at_def, sys_chan_def, ptr_def] >> strip_tac >>
  irule ep_sent_chan >> metis_tac[]
QED

(* Two instants at which e is an end see the same target *)
Theorem irun_target_eq:
  l0sys_irun ps ss rs ∧ is_end (ss n) e ∧ is_end (ss n') e ⇒ (ss n').target e = (ss n).target e
Proof
  strip_tac >> Cases_on ‘n ≤ n'’ >- metis_tac[irun_target] >>
  ‘n' ≤ n’ by simp[] >> metis_tac[irun_target]
QED

(* A chain end lost at n, existing at some m ≤ n, has ended *)
Theorem lost_ended:
  l0sys_irun ps ss rs ∧ is_end (ss m) e ∧ m ≤ n ∧ lost ss e n ⇒ ended ss e n
Proof
  rw[ended_def, frozen_def, lost_def] >> metis_tac[irun_target]
QED

(* ------------------------------------------------------------------------
   closes_ob, per chain end
   ------------------------------------------------------------------------ *)

Theorem closes_ob_cl:
  closes_ob X ss rs bk jep rq ∧ ep_chan ss rs 0 jep jc ∧ ended ss (0, jc) n ⇒
  X ∨ done_by rs jep rq n
Proof
  rw[closes_ob_def] >> metis_tac[]
QED

Theorem closes_ob_front:
  closes_ob X ss rs bk jep rq ∧ ep_chan ss rs 0 jep jc ∧ (ss m).peer (0, jc) = SOME (1, ja) ∧
  ended ss (1, ja) n ⇒ X ∨ done_by rs jep rq n
Proof
  rw[closes_ob_def] >> metis_tac[]
QED

Theorem closes_ob_back:
  closes_ob X ss rs bk jep rq ∧ ep_chan ss rs 0 jep jc ∧ (ss m).peer (0, jc) = SOME (1, ja) ∧
  bk ja = SOME jb ∧ ended ss (1, jb) n ⇒ X ∨ done_by rs jep rq n
Proof
  rw[closes_ob_def] >> metis_tac[]
QED

Theorem closes_ob_kv:
  closes_ob X ss rs bk jep rq ∧ ep_chan ss rs 0 jep jc ∧ (ss m).peer (0, jc) = SOME (1, ja) ∧
  bk ja = SOME jb ∧ (ss m').peer (1, jb) = SOME e ∧ ended ss e n ⇒ X ∨ done_by rs jep rq n
Proof
  rw[closes_ob_def] >> metis_tac[]
QED

Theorem connect_pairs_at = REWRITE_RULE [connect_pairs_claim_def] connect_pairs
Theorem chain_served_at = REWRITE_RULE [chain_served_claim_def] chain_served

(* ------------------------------------------------------------------------
   One logical connection
   ------------------------------------------------------------------------ *)

Theorem conn_done_of_obs:
  l0sys_irun ps ss rs ∧ LENGTH ps = 3 ∧ kernel_fair_obs ss rs ∧ isolated [a; b] ss rs ∧
  topology_ob a b ss ∧ proxy_ob X a b ss rs bk ∧ kv_ob X b ss rs ∧
  client_conn_ob X ss rs jep rq ∧ closes_ob X ss rs bk jep rq ∧ EVERY valid_brequest rq ∧
  l0_ep_role jep (ptr rs 0 n0) = SOME (Connected a) ⇒
  X ∨ ∃n. n0 ≤ n ∧ done_by rs jep rq n
Proof
  strip_tac >>
  qabbrev_tac ‘c = EL jep (run_css ss rs n0 0)’ >>
  ‘jep < LENGTH (run_css ss rs n0 0) ∧ ep_chan ss rs 0 jep c ∧ is_end (ss n0) (0, c) ∧
   (ss n0).target (0, c) = SOME a’ by
    (mp_tac (ep_connected_chan |> Q.INST [‘k’ |-> ‘0’, ‘j’ |-> ‘jep’, ‘n’ |-> ‘n0’, ‘p’ |-> ‘a’]) >>
     simp[Abbr‘c’]) >>
  (* the client's clauses on c *)
  ‘(conn_done X rs jep rq ∨ io (asks_in ss rs 0 c)) ∧
   (sys_drains ss (0, c) ⇒
    conn_done X rs jep rq ∨ ∃n. brequests rq ≼ l0_ep_sent jep (ptr rs 0 n)) ∧
   (∀n. l0_ep_sent jep (ptr rs 0 n) ≼ brequests rq) ∧
   (∀m. is_end (ss m) (0, c) ⇒
        conn_done X rs jep rq ∨ ev_ext m (dlv_at ss (0, c)) (λn. l0_ep_recvd jep (ptr rs 0 n)))’ by
    (qpat_x_assum ‘client_conn_ob _ _ _ _ _’ mp_tac >> rewrite_tac[client_conn_ob_def] >>
     disch_then (qspec_then ‘c’ mp_tac) >> simp[]) >>
  (* it suffices: done at some instant (then at one from n0 on) *)
  ‘conn_done X rs jep rq’ suffices_by
    (rewrite_tac[conn_done_def] >> strip_tac >> simp[] >> disj2_tac >>
     qexists_tac ‘MAX n n0’ >> simp[] >> irule done_by_mono >> simp[] >>
     qexists_tac ‘n’ >> simp[]) >>
  CCONTR_TAC >>
  ‘¬X ∧ ∀n. ¬done_by rs jep rq n’ by fs[conn_done_def] >>
  qpat_x_assum ‘¬conn_done _ _ _ _’ (fn th => fs[th]) >>
  ‘∀n. ¬ended ss (0, c) n’ by metis_tac[closes_ob_cl] >>
  (* the client's end is paired with a front ja *)
  ‘∃n1 ja. (ss n1).peer (0, c) = SOME (1, ja)’ by
    (qspecl_then [‘ps’, ‘ss’, ‘rs’, ‘[a; b]’, ‘n0’, ‘(0, c)’, ‘a’, ‘1’] mp_tac connect_pairs_at >>
     impl_tac
     >- (simp[] >> qpat_x_assum ‘topology_ob _ _ _’ mp_tac >> rewrite_tac[topology_ob_def] >>
         rpt strip_tac >> first_x_assum (qspecl_then [‘n’, ‘k’] mp_tac) >> simp[]) >>
     simp[]) >>
  ‘∀n. ¬ended ss (1, ja) n’ by metis_tac[closes_ob_front] >>
  ‘kinv (ss n1)’ by metis_tac[irun_kinv] >>
  ‘is_end (ss n1) (0, c) ∧ (ss n1).peer (1, ja) = SOME (0, c)’ by metis_tac[kinv_peer_end] >>
  ‘(ss n1).target (0, c) = SOME a’ by
    (mp_tac (Q.INST [‘e’ |-> ‘(0, c)’, ‘n’ |-> ‘n0’, ‘n'’ |-> ‘n1’] irun_target_eq) >>
     simp[]) >>
  (* its backend jb *)
  ‘∃jb n2. bk ja = SOME jb ∧ is_end (ss n2) (1, jb) ∧ (ss n2).target (1, jb) = SOME b ∧
           proxy_pair_ob X ss rs ja jb’ by
    (qpat_x_assum ‘proxy_ob _ _ _ _ _ _’ mp_tac >> rewrite_tac[proxy_ob_def] >>
     disch_then (qspecl_then [‘ja’, ‘n1’, ‘(0, c)’] mp_tac) >> simp[] >> metis_tac[]) >>
  ‘∀n. ¬ended ss (1, jb) n’ by metis_tac[closes_ob_back] >>
  (* the backend is paired with KV's jk *)
  ‘∃n3 jk. (ss n3).peer (1, jb) = SOME (2, jk)’ by
    (qspecl_then [‘ps’, ‘ss’, ‘rs’, ‘[a; b]’, ‘n2’, ‘(1, jb)’, ‘b’, ‘2’] mp_tac connect_pairs_at >>
     impl_tac
     >- (simp[] >> qpat_x_assum ‘topology_ob _ _ _’ mp_tac >> rewrite_tac[topology_ob_def] >>
         rpt strip_tac >> first_x_assum (qspecl_then [‘n’, ‘k’] mp_tac) >> simp[]) >>
     simp[]) >>
  ‘∀n. ¬ended ss (2, jk) n’ by metis_tac[closes_ob_kv] >>
  ‘kinv (ss n3)’ by metis_tac[irun_kinv] >>
  ‘is_end (ss n3) (1, jb) ∧ (ss n3).peer (2, jk) = SOME (1, jb)’ by metis_tac[kinv_peer_end] >>
  ‘(ss n3).target (1, jb) = SOME b’ by
    (mp_tac (Q.INST [‘e’ |-> ‘(1, jb)’, ‘n’ |-> ‘n2’, ‘n'’ |-> ‘n3’] irun_target_eq) >>
     simp[]) >>
  (* from M on, both pairs stand *)
  qabbrev_tac ‘M = MAX n1 n3’ >>
  ‘n1 ≤ M ∧ n3 ≤ M’ by simp[Abbr‘M’] >>
  ‘(ss M).peer (0, c) = SOME (1, ja) ∧ (ss M).peer (1, jb) = SOME (2, jk)’ by
    metis_tac[irun_mono] >>
  ‘kinv (ss M)’ by metis_tac[irun_kinv] >>
  ‘is_end (ss M) (0, c) ∧ is_end (ss M) (1, ja) ∧ is_end (ss M) (1, jb) ∧ is_end (ss M) (2, jk)’ by
    metis_tac[kinv_peer_end] >>
  (* the proxy's and KV's clauses, their escapes false *)
  ‘(sys_drains ss (1, ja) ⇒ io (asks_in ss rs 1 jb)) ∧
   (sys_drains ss (1, jb) ⇒ io (asks_in ss rs 1 ja)) ∧
   (sys_drains ss (1, jb) ⇒ ev_ext M (dlv_at ss (1, ja)) (sent_at ss (1, jb))) ∧
   (sys_drains ss (1, ja) ⇒ ev_ext M (dlv_at ss (1, jb)) (sent_at ss (1, ja)))’ by
    (qpat_x_assum ‘proxy_pair_ob _ _ _ _ _’ mp_tac >> simp[proxy_pair_ob_def, LET_THM] >>
     strip_tac >> first_x_assum (qspec_then ‘M’ mp_tac) >> simp[]) >>
  ‘(sys_drains ss (2, jk) ⇒ io (asks_in ss rs 2 jk)) ∧
   (sys_drains ss (2, jk) ⇒ kv_answers M F ss (2, jk))’ by
    (qpat_x_assum ‘kv_ob _ _ _ _’ mp_tac >> rewrite_tac[kv_ob_def] >>
     disch_then (qspecl_then [‘jk’, ‘n3’, ‘(1, jb)’] mp_tac) >> simp[LET_THM] >>
     rpt strip_tac >> irule kv_answers_mono >> qexists_tac ‘X ∨ ∃n. ended ss (2, jk) n’ >>
     simp[]) >>
  (* the client sends all of rq, under drains *)
  ‘sys_drains ss (0, c) ⇒ ∃n. M ≤ n ∧ brequests rq ≼ sent_at ss (0, c) n’ by
    (strip_tac >>
     ‘∃nt. brequests rq ≼ l0_ep_sent jep (ptr rs 0 nt)’ by metis_tac[] >>
     qabbrev_tac ‘n' = MAX (MAX M nt) n0’ >>
     ‘M ≤ n' ∧ nt ≤ n' ∧ n0 ≤ n'’ by simp[Abbr‘n'’] >>
     qexists_tac ‘n'’ >> simp[] >>
     ‘jep < LENGTH (run_css ss rs n' 0) ∧ EL jep (run_css ss rs n' 0) = c’ by
       (mp_tac (Q.INST [‘j’ |-> ‘jep’, ‘n’ |-> ‘n0’, ‘k’ |-> ‘0’] run_css_EL) >>
        simp[Abbr‘c’]) >>
     ‘l0_ep_sent jep (ptr rs 0 n') ≼ sent_at ss (0, c) n'’ by
       (qpat_x_assum ‘EL jep _ = c’ (SUBST1_TAC o GSYM) >>
        mp_tac (Q.INST [‘j’ |-> ‘jep’, ‘n’ |-> ‘n'’, ‘k’ |-> ‘0’] ep_sent_le) >> simp[]) >>
     ‘l0_ep_sent jep (ptr rs 0 nt) ≼ l0_ep_sent jep (ptr rs 0 n')’ by
       (irule ep_sent_mono >> simp[]) >>
     metis_tac[IS_PREFIX_TRANS]) >>
  (* no chain end is lost from M on *)
  ‘∀n e. M ≤ n ∧ MEM e [(0, c); (1, ja); (1, jb); (2, jk)] ∧ lost ss e n ⇒ F’ by
    (rw[] >> metis_tac[lost_ended]) >>
  (* the data chain, with X := F *)
  ‘sys_drains ss (0, c)’ by
    (mp_tac (moonshot_chain_drains |> Q.INST [‘X’ |-> ‘F’, ‘m’ |-> ‘M’, ‘cl’ |-> ‘0’,
                                              ‘jc’ |-> ‘c’, ‘px’ |-> ‘1’, ‘kv’ |-> ‘2’]) >>
     simp[]) >>
  ‘∃ns. served_by rs 0 jep rq ns’ by
    (qspecl_then [‘ps’, ‘ss’, ‘rs’, ‘M’, ‘F’, ‘0’, ‘c’, ‘1’, ‘ja’, ‘jb’, ‘2’, ‘jk’, ‘jep’, ‘rq’]
       mp_tac chain_served_at >>
     impl_tac
     >- (simp[] >> rpt gen_tac >>
         qpat_x_assum ‘∀n e. _ ⇒ F’ (qspecl_then [‘n’, ‘e’] mp_tac) >> rewrite_tac[MEM] >>
         tautLib.TAUT_TAC) >> simp[]) >>
  (* sent exactly rq and served: done *)
  ‘∃nt. brequests rq ≼ l0_ep_sent jep (ptr rs 0 nt)’ by metis_tac[] >>
  qpat_x_assum ‘∀n. ¬done_by _ _ _ n’ (qspec_then ‘MAX ns nt’ mp_tac) >>
  simp[done_by_def] >> conj_tac
  >- (irule IS_PREFIX_ANTISYM >> simp[] >> irule IS_PREFIX_TRANS >>
      qexists_tac ‘l0_ep_sent jep (ptr rs 0 nt)’ >> simp[] >> irule ep_sent_mono >> simp[]) >>
  irule served_by_mono >> qexists_tac ‘ns’ >> simp[]
QED

(* ------------------------------------------------------------------------
   All N logical connections
   ------------------------------------------------------------------------ *)

Theorem moonshot_served_of_obs:
  moonshot_served_of_obs_claim
Proof
  rewrite_tac[moonshot_served_of_obs_claim_def] >> rpt strip_tac >>
  rename1 ‘l0sys_irun ps _ _’ >>
  Cases_on ‘X’ >> simp[] >>
  qpat_x_assum ‘moonshot_obs _ _ _ _ _ _ _’ mp_tac >>
  simp[moonshot_obs_def, client_open_def] >> strip_tac >>
  simp[client_served_def] >> qexists_tac ‘ep’ >> simp[] >> rpt strip_tac >>
  ‘∃n0. l0_ep_role (ep i) (ptr rs 0 n0) = SOME (Connected a)’ by simp[] >>
  ‘∃n. n0 ≤ n ∧ done_by rs (ep i) (rqs i) n’ by
    (mp_tac (Q.INST [‘X’ |-> ‘F’, ‘jep’ |-> ‘(ep : num -> num) i’,
                     ‘rq’ |-> ‘(rqs : num -> brequest list) i’] conn_done_of_obs) >>
     simp[]) >>
  fs[done_by_def, served_by_def] >>
  qexistsl_tac [‘n’, ‘ans’] >> simp[] >>
  irule ep_role_mono >> qexists_tac ‘n0’ >> simp[]
QED
