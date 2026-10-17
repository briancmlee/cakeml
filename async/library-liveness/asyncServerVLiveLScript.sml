(*
  The library's liveness (asyncServerVLive, asyncServerVLiveP) for the loop
  polled through the live interest list (D26, asyncM4LiveInterest):
  LVg m lfdn = live [n2w lfdn] (log_of (srelabel m)).  The proofs are
  asyncServerVLive's and asyncServerVLiveP's, with live_accepted for
  interest_accepted.  live_accepted's no-end-of-file premise is:
   - for the listener: a server meeting uses_ok never reads it
     (m_no_listener_read, as asyncM4NoListenRead's echo_no_listener_read);
   - for a connection: m_view_henv_e asks for the interest list only on
     fds that have not read end-of-file (interest_covers_e).

  MAIN: m_conn_accepted_l, server_v_queue_progress_l, server_v_live_l,
  server_v_live_p_l.
*)
Theory asyncServerVLiveL
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec HttpSpec
  asyncM3World asyncM4GRounds asyncM4Relabel asyncM4RelabelDist
  asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop asyncM4EchoRunOk
  asyncM4Sched asyncM4Account asyncM4LiveProg asyncM4LiveWorld asyncM4ReadSoon
  asyncM4Queue asyncM4AcceptSoon asyncM4Drain asyncRunOkGen asyncServerWith
  asyncM4ServerUses asyncServerWithUses asyncSWProgress asyncSWSock
  asyncServerWithLive asyncServerV asyncServerVProgress asyncServerVLive
  asyncServerVLiveA asyncServerVLiveP asyncM4LiveInterest asyncM4LiveAcc
  asyncM4NoListenRead
Libs
  preamble

Overload LVg = “λ(m : 'mx smach) lfdn.
                  asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel m))”

(* ------------------------------------------------------------------------
   1. Any socket machine M
   ------------------------------------------------------------------------ *)

(* M never reads its listener: it reads only connections it was handed,
   and the listener's fd is never a connection (nl_gstate) *)
Theorem m_no_listener_read:
  uses_ok lfdn (M : 'mx smach) ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀j k r. ¬MEM (asyncM3World$Read (n2w lfdn) k, r) (SPg M ifds s0 j)
Proof
  rpt strip_tac >>
  ‘grun_ok ifds (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[]) >>
  fs[gperf_def, MEM_FLAT, MEM_GENLIST] >> rename1 ‘i < j’ >>
  ‘MEM (asyncM3World$Read (n2w lfdn) k) (SAg M ifds s0 i)’
    by (gvs[MEM_ZIP, LENGTH_gres] >> metis_tac[EL_MEM]) >>
  ‘gok_upto ifds (srelabel M) s0 i’ by simp[grun_ok_gok_upto] >>
  ‘action_ok (n2w lfdn) (wacc (SPg M ifds s0 i)) (asyncM3World$Read (n2w lfdn) k)’
    by (drule_all gen_round_actions_ok >> rw[EVERY_MEM]) >>
  fs[action_ok_def] >>
  ‘sinv (n2w lfdn) (wacc (SPg M ifds s0 i)) (gstate ifds (srelabel M) s0 i)’
    by (drule_all gen_sinv >> simp[]) >>
  ‘is_conn (gstate ifds (srelabel M) s0 i) (n2w lfdn)’ by fs[sinv_def] >>
  ‘nl (n2w lfdn) (gstate ifds (srelabel M) s0 i)’ by simp[nl_gstate] >>
  fs[nl_def]
QED

(* The live list keeps every handed-out fd that has not read end-of-file *)
Theorem interest_covers_e_live:
  grun_ok (LVg M lfdn) (srelabel M) s0 ⇒ interest_covers_e (LVg M lfdn) (srelabel M) s0
Proof
  rw[interest_covers_e_def] >> irule live_accepted >> fs[]
QED

(* m_accept_soon_s on the live list *)
Theorem m_accept_soon_s_l:
  asyncLevel1$wf (M : 'mx smach) ∧
  accepts_progress lfdn M ∧ uses_ok lfdn M ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  (∀j. n < j ∧ j ≤ n + 2 ⇒ is_ready (gstate (LVg M lfdn) (srelabel M) s0 j) (n2w lfdn)) ⇒
  ∃i. 1 ≤ i ∧ i ≤ 2 ∧ MEM (asyncM3World$Accept (n2w lfdn)) (SAg M (LVg M lfdn) s0 (n + i))
Proof
  rpt strip_tac
  >> ‘grun_ok (LVg M lfdn) (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[])
  (* M sees the listener readable in snapshots n, n + 1 *)
  >> ‘∀j. n ≤ j ∧ j < n + 2 ⇒
          Readable lfdn ∈ (EL j (MAP sfs (ghist (LVg M lfdn) (srelabel M) s0 (n + 2)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> qexists_tac ‘n2w lfdn’ >> simp[]
           (* the listener is in the live list: it never reads end-of-file *)
           >> irule live_accepted >> rpt conj_tac
           >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
                     gen_tac >> irule m_no_listener_read >> ASM_REWRITE_TAC[]])
  >> ‘prompt M (MAP sfs (ghist (LVg M lfdn) (srelabel M) s0 (n + 2)))’ by simp[prompt_ghist]
  >> qpat_x_assum ‘accepts_progress _ _’
       (qspecl_then [‘MAP sfs (ghist (LVg M lfdn) (srelabel M) s0 (n + 2))’, ‘n’] mp_tac o
        REWRITE_RULE [accepts_progress_def])
  >> impl_tac >- simp[]
  >> ‘∀k. k ≤ n + 2 ⇒ TAKE k (MAP sfs (ghist (LVg M lfdn) (srelabel M) s0 (n + 2))) =
                       MAP sfs (ghist (LVg M lfdn) (srelabel M) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> strip_tac
  >> qspecl_then [‘2’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (LVg M lfdn) (srelabel M) s0 (n + 2))’] m_naccepts_step)
  >> impl_tac >- simp[] >> strip_tac
  (* an accept of M is an accept of the socket program *)
  >> qexists_tac ‘k − n’ >> simp[]
  >> gvs[gacts_def, new_actions_relabel, MEM_MAP]
  >> qexists_tac ‘Accept lfdn’ >> simp[sfa_def]
QED

(* MAIN: a pending connection is eventually handed out to M *)
Theorem m_queue_progress_l:
  asyncLevel1$wf (M : 'mx smach) ∧
  accepts_progress lfdn M ∧ uses_ok lfdn M ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k (gstate (LVg M lfdn) (srelabel M) s0 n) ⇒
        ∃N. MEM c (wacc (SPg M (LVg M lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (LVg M lfdn) (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[])
  >> completeInduct_on ‘k’ >> rpt strip_tac
  >> Cases_on ‘MEM c (wacc (SPg M (LVg M lfdn) s0 (n + 3)))’ >- metis_tac[]
  (* not handed out by round n + 3: still pending in rounds n .. n + 3 *)
  >> ‘∀d. d ≤ 3 ⇒ ∃k'. queued (n2w lfdn) c k' (gstate (LVg M lfdn) (srelabel M) s0 (n + d)) ∧
                       k' ≤ k’
       by (rpt strip_tac
           >> qspecl_then [‘LVg M lfdn’, ‘srelabel M’, ‘s0’, ‘n’, ‘n2w lfdn’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘l’, ‘c’] rounds_queued)
           >> simp[] >> disch_then (qspecl_then [‘d’, ‘k’] mp_tac) >> simp[]
           >> strip_tac >- (‘MEM c (wacc (SPg M (LVg M lfdn) s0 (n + 3)))’
                              suffices_by metis_tac[]
                            >> irule wacc_mono >> qexists_tac ‘d + n’ >> simp[])
           >> metis_tac[])
  (* so M accepts in round n + 1 or n + 2 *)
  >> qspecl_then [‘s0’, ‘lfdn’, ‘n’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘n’] m_accept_soon_s_l)
  >> impl_tac
  >- (simp[] >> rpt strip_tac
      >> first_x_assum (qspec_then ‘j − n’ mp_tac) >> simp[] >> strip_tac
      >> ‘n + (j − n) = j’ by simp[] >> gvs[] >> metis_tac[queued_ready])
  >> strip_tac
  (* which moves c forward *)
  >> first_assum (qspec_then ‘i’ mp_tac) >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘LVg M lfdn’, ‘srelabel M’, ‘s0’, ‘n2w lfdn’, ‘c’, ‘k'’, ‘n + i’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘l’, ‘c’, ‘k’, ‘n’] round_queued)
  >> simp[] >> strip_tac >- metis_tac[]
  >> ‘0 < nacc (n2w lfdn) (SAg M (LVg M lfdn) s0 (i + n))’
       by (gvs[nacc_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >> metis_tac[])
  >> qpat_x_assum ‘∀m. m < k ⇒ _’ (qspec_then ‘k''’ mp_tac) >> impl_tac >- fs[]
  >> disch_then (qspec_then ‘SUC (i + n)’ mp_tac) >> fs[]
QED

(* MAIN: every connection of the world is eventually handed out to M *)
Theorem m_conn_accepted_l:
  asyncLevel1$wf (M : 'mx smach) ∧
  accepts_progress lfdn M ∧ uses_ok lfdn M ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  is_conn (gstate (LVg M lfdn) (srelabel M) s0 n) c ⇒
  ∃N. MEM c (wacc (SPg M (LVg M lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (LVg M lfdn) (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[])
  >> qspecl_then [‘LVg M lfdn’, ‘srelabel M’, ‘s0’, ‘n2w lfdn’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfd’] grounds_known)
  >> simp[] >> disch_then (qspec_then ‘n’ (strip_assume_tac o CONJUNCT2))
  >> fs[known_def] >> first_x_assum drule >> strip_tac >- metis_tac[]
  >> qpat_x_assum ‘MEM c (lq _ _)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’] mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘c’] m_queue_progress_l)
  >> impl_tac >- fs[] >> disch_then irule
  >> qexistsl_tac [‘LENGTH l1’, ‘n’] >> simp[queued_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   2. The skeleton inside a wrapper
   ------------------------------------------------------------------------ *)

Theorem server_v_props:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ⇒
  asyncLevel1$wf (Wr (server_v V hf lfdn)) ∧ uses_ok lfdn (Wr (server_v V hf lfdn)) ∧
  accepts_progress lfdn (Wr (server_v V hf lfdn))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  rpt conj_tac
  >- fs[wrap_ok_def]
  >- (irule uses_ok_wrap >> metis_tac[])
  >> irule accepts_progress_wrap >> metis_tac[]
QED

(* MAIN: a pending connection is eventually handed out to the skeleton *)
Theorem server_v_queue_progress_l:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k
          (gstate (LVg (Wr (server_v V hf lfdn)) lfdn) (srelabel (Wr (server_v V hf lfdn))) s0 n) ⇒
        ∃N. MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (LVg (Wr (server_v V hf lfdn)) lfdn) s0 N))
Proof
  strip_tac >> drule_all server_v_props >>
  disch_then (qspec_then ‘lfdn’ strip_assume_tac) >> rpt strip_tac >>
  irule m_queue_progress_l >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, qexistsl [‘k’, ‘n’] >> first_assum ACCEPT_TAC]
QED

(* MAIN: server_v_live on the live list *)
Theorem server_v_live_l:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_live_v V hf out B ∧ FLAT (out "") = "" ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (LVg (Wr (server_v V hf lfdn)) lfdn)
                          (srelabel (Wr (server_v V hf lfdn))) s0) N))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (Wr (server_v V hf lfdn)) ∧ uses_ok lfdn (Wr (server_v V hf lfdn)) ∧
   accepts_progress lfdn (Wr (server_v V hf lfdn))’
    by (irule server_v_props >> metis_tac[]) >>
  ‘grun_ok (LVg (Wr (server_v V hf lfdn)) lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by (irule gen_grun_ok >> metis_tac[]) >>
  (* nothing owed *)
  Cases_on ‘D = ""’
  >- (qexists_tac ‘0’ >> gvs[bytes_def]) >>
  (* otherwise something was sent on c, so c is a connection by round n *)
  ‘sent_upto c n s0 ≠ []’ by (strip_tac >> Cases_on ‘D’ >> fs[bytes_def]) >>
  ‘is_conn (gstate (LVg (Wr (server_v V hf lfdn)) lfdn) (srelabel (Wr (server_v V hf lfdn))) s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  (* it is handed out at some round N0 *)
  ‘∃N0. MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (LVg (Wr (server_v V hf lfdn)) lfdn) s0 N0))’
    by (irule m_conn_accepted_l >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘n1 = n + N0’ >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (LVg (Wr (server_v V hf lfdn)) lfdn) s0 n1))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[Abbr ‘n1’]) >>
  ‘bytes D ≼ sent_upto c n1 s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[Abbr ‘n1’, sent_upto_prefix]) >>
  (* its handler's view, B D rounds past n1 *)
  qspecl_then [‘n1’, ‘n1 + B D’] mp_tac
    (Q.GENL [‘n’, ‘N’] view_wrap |> Q.INST [‘ifds’ |-> ‘LVg (Wr (server_v V hf lfdn)) lfdn’]) >>
  impl_tac >- simp[] >> strip_tac >>
  (* the socket world gives the handler its environment *)
  ‘interest_covers_e (LVg (Wr (server_v V hf lfdn)) lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by (irule interest_covers_e_live >> first_assum ACCEPT_TAC) >>
  ‘henv_t (w2n c) (λq. sproj V (trans (hf (w2n c)) q)) g (n1 − a) D ∧
   ∀j. j ≤ LENGTH g ⇒
     bytes (FLAT (written (w2n c) ((λq. sproj V (trans (hf (w2n c)) q)) (TAKE j g)))) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (LVg (Wr (server_v V hf lfdn)) lfdn)
                           (srelabel (Wr (server_v V hf lfdn))) s0)
                        (SUC (a + j))))’
    by (irule m_view_henv_e >> simp[] >> qexists_tac ‘lfdn’ >> fs[]) >>
  (* so it writes out D *)
  qpat_x_assum ‘handler_live_v _ _ _ _’ (mp_tac o REWRITE_RULE [handler_live_v_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘n1 − a’, ‘D’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac ‘SUC (a + j)’ >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ bytes _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  REWRITE_TAC[bytes_prefix_sw] >>
  qpat_x_assum ‘out D ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* MAIN: server_v_live_p on the live list *)
Theorem server_v_live_p_l:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  wrap_kans V Wr inner ∧ vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_live_vp V hf Q B ∧ Q "" [] [] ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N ks ws. Q D ks ws ∧
    bytes (FLAT ws) =
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (LVg (Wr (server_v V hf lfdn)) lfdn)
                          (srelabel (Wr (server_v V hf lfdn))) s0) N))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (Wr (server_v V hf lfdn)) ∧ uses_ok lfdn (Wr (server_v V hf lfdn)) ∧
   accepts_progress lfdn (Wr (server_v V hf lfdn))’
    by (irule server_v_props >> metis_tac[]) >>
  ‘grun_ok (LVg (Wr (server_v V hf lfdn)) lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by (irule gen_grun_ok >> metis_tac[]) >>
  (* nothing owed *)
  Cases_on ‘D = ""’
  >- (qexistsl [‘0’, ‘[]’, ‘[]’] >> gvs[bytes_def, bytes_written_to_def]) >>
  (* otherwise something was sent on c, so c is a connection by round n *)
  ‘sent_upto c n s0 ≠ []’ by (strip_tac >> Cases_on ‘D’ >> fs[bytes_def]) >>
  ‘is_conn (gstate (LVg (Wr (server_v V hf lfdn)) lfdn) (srelabel (Wr (server_v V hf lfdn))) s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  (* it is handed out at some round N0 *)
  ‘∃N0. MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (LVg (Wr (server_v V hf lfdn)) lfdn) s0 N0))’
    by (irule m_conn_accepted_l >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘n1 = n + N0’ >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (LVg (Wr (server_v V hf lfdn)) lfdn) s0 n1))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[Abbr ‘n1’]) >>
  ‘bytes D ≼ sent_upto c n1 s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[Abbr ‘n1’, sent_upto_prefix]) >>
  (* its handler's view, B D rounds past n1 *)
  qspecl_then [‘n1’, ‘n1 + B D’] mp_tac
    (Q.GENL [‘n’, ‘N’] view_wrap_ans |> Q.INST [‘ifds’ |-> ‘LVg (Wr (server_v V hf lfdn)) lfdn’]) >>
  impl_tac >- simp[] >> strip_tac >>
  (* the socket world gives the handler its environment *)
  ‘interest_covers_e (LVg (Wr (server_v V hf lfdn)) lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by (irule interest_covers_e_live >> first_assum ACCEPT_TAC) >>
  ‘henv_t (w2n c) (λq. sproj V (trans (hf (w2n c)) q)) g (n1 − a) D ∧
   ∀j. j ≤ LENGTH g ⇒
     bytes (FLAT (written (w2n c) ((λq. sproj V (trans (hf (w2n c)) q)) (TAKE j g)))) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (LVg (Wr (server_v V hf lfdn)) lfdn)
                           (srelabel (Wr (server_v V hf lfdn))) s0)
                        (SUC (a + j))))’
    by (irule m_view_henv_e >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC,
               CONV_TAC (DEPTH_CONV BETA_CONV) >> first_assum ACCEPT_TAC,
               qexists_tac ‘n1 + B D’ >> conj_tac >> first_assum ACCEPT_TAC,
               qexists_tac ‘lfdn’ >> conj_tac >> first_assum ACCEPT_TAC]) >>
  (* the wrapper answered the handler's queries with store answers *)
  ‘∀j. j ≤ LENGTH g ⇒ kans_ok V (trans (hf (w2n c)) (TAKE j g))’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd_v _ _) _ = _’
          (qspec_then ‘j’ mp_tac) >>
        simp[] >> disch_then (SUBST1_TAC o SYM) >>
        irule kans_ok_FILTER >>
        qpat_x_assum ‘wrap_kans _ _ _’ (irule o REWRITE_RULE [wrap_kans_def]) >>
        irule wf_server_v >> qpat_assum ‘hokv _ _’ (ACCEPT_TAC o MATCH_MP hokv_wf)) >>
  (* so it reaches Q *)
  qpat_x_assum ‘handler_live_vp _ _ _ _’ (mp_tac o REWRITE_RULE [handler_live_vp_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘n1 − a’, ‘D’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl [‘SUC (a + j)’, ‘kanswers V (trans (hf (w2n c)) (TAKE j g))’,
            ‘written (w2n c) (sproj V (trans (hf (w2n c)) (TAKE j g)))’] >>
  simp[] >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ bytes _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[]
QED
