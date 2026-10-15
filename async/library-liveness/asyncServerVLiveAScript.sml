(*
  asyncServerVLiveA: the library liveness theorem for STATEFUL servers
  (design/34, KV; additive over asyncServerVLive).

  handler_live_va generalises handler_live_v: the output owed for data D
  may also depend on the answers the handler received to its queries (for
  KV: the store's answers), in order, read off its transcript (kanswers).
  server_v_live_a is server_v_live for it; and handler_live_v is the
  instance whose output ignores the answers (handler_live_v_va), so
  server_v_live's statement is a corollary (server_v_live_via_a).

  server_v_live_ans names the answers: they are connection c's handler's
  ACTUAL answers in the run (conn_answers: the query answers in c's part
  of the skeleton's transcript, before the socket projection, in the first
  N rounds), and the output owed given them is written by round N.  It
  needs view_wrap_ans (view_wrap plus: c's part of the skeleton's
  transcript is its handler's transcript, by sv_handler_view).
  asyncServerVLive's definitions are unchanged.
*)
Theory asyncServerVLiveA
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
Libs
  preamble

(* The answers to queries in a transcript, in order *)
Definition kanswers_def:
  kanswers (V : ('act, 'k, 'q, 'res) vocab) (tr : ('act # 'res option) list) =
    FLAT (MAP (λ(a, r). case r of
                          SOME x => (case V.kans x of SOME k => [k] | NONE => [])
                        | NONE => []) tr)
End

(* MAIN (definition): a handler is live if, in every environment, it
   eventually writes the output owed for D given the answers it has
   received *)
Definition handler_live_va_def:
  handler_live_va (V : ('act, 'k, 'q, 'res) vocab) (hf : num -> ('act, 'res, 'z) vmach)
                  (out : string -> 'k list -> string list) B ⇔
    ∀fd g j0 D.
      prompt (hf fd) g ∧ henv_t fd (λq. sproj V (trans (hf fd) q)) g j0 D ∧
      j0 + B D ≤ LENGTH g ⇒
      ∃j. j ≤ LENGTH g ∧
          out D (kanswers V (trans (hf fd) (TAKE j g))) ≼
            written fd (sproj V (trans (hf fd) (TAKE j g)))
End

(* handler_live_v is the case of an output that ignores the answers *)
Theorem handler_live_v_va:
  handler_live_v V hf out B ⇔ handler_live_va V hf (λD ans. out D) B
Proof
  simp[handler_live_v_def, handler_live_va_def]
QED

(* The answers connection c's handler has received in the first N rounds
   of the server's run: the query answers in c's part of the skeleton's
   transcript (before the socket projection), on the history the wrapper
   gives it *)
Definition conn_answers_def:
  conn_answers (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach)
               inner (hf : num -> ('act, 'res, 'z) vmach) lfdn ifds s0 N c =
    kanswers V
      (FILTER (on_fd_v V (w2n (c : word64)))
         (trans (server_v V hf lfdn)
            (inner (server_v V hf lfdn)
               (MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 N)))))
End

(* view_wrap (asyncServerVLive), plus: c's part of the skeleton's
   transcript, before the socket projection, is its handler's transcript;
   so the handler's answers are the run's (conn_answers) *)
Theorem view_wrap_ans:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 n)) ∧ n ≤ N ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = N ∧ prompt (hf (w2n c)) g ∧
    (∀i. i < LENGTH g ⇒
         (EL i g).ready =
         (EL (a + i) (MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 N))).ready) ∧
    (∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd (w2n c)) (TSg (Wr (server_v V hf lfdn)) ifds s0 (a + j)) =
      sproj V (trans (hf (w2n c)) (TAKE j g))) ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd_v V (w2n c))
        (trans (server_v V hf lfdn)
          (inner (server_v V hf lfdn)
             (MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 (a + j))))) =
      trans (hf (w2n c)) (TAKE j g)
Proof
  strip_tac >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  ‘grun_ok ifds (srelabel (Wr (server_v V hf lfdn))) s0’ by (irule gen_grun_ok >> metis_tac[]) >>
  ‘∀h. trans (Wr (server_v V hf lfdn)) h =
         sproj V (trans (server_v V hf lfdn) (inner (server_v V hf lfdn) h)) ∧
       (prompt (Wr (server_v V hf lfdn)) h ⇒
        prompt (server_v V hf lfdn) (inner (server_v V hf lfdn) h)) ∧
       LENGTH (inner (server_v V hf lfdn) h) = LENGTH h ∧
       (∀i. i < LENGTH h ⇒ (EL i (inner (server_v V hf lfdn) h)).ready = (EL i h).ready) ∧
       ∀j. inner (server_v V hf lfdn) (TAKE j h) = TAKE j (inner (server_v V hf lfdn) h)’
    by fs[wrap_ok_def] >>
  qabbrev_tac ‘H = MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 N)’ >>
  qabbrev_tac ‘IH = inner (server_v V hf lfdn) H’ >>
  ‘LENGTH H = N ∧ LENGTH IH = N’ by simp[Abbr ‘H’, Abbr ‘IH’] >>
  (* the loop's transcript, as the socket part of the skeleton's on IH *)
  ‘∀k. k ≤ N ⇒
       TSg (Wr (server_v V hf lfdn)) ifds s0 k = sproj V (trans (server_v V hf lfdn) (TAKE k IH))’
    by (rpt strip_tac >>
        ‘MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 k) = TAKE k H’
          by simp[Abbr ‘H’, GSYM MAP_TAKE, ghist_TAKE] >>
        simp[Abbr ‘IH’]) >>
  ‘∀k. accepted (TSg (Wr (server_v V hf lfdn)) ifds s0 k) =
       MAP w2n (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 k))’
    by metis_tac[TSg_accepted] >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 N))’
    by (irule wacc_mono >> qexists_tac ‘n’ >> simp[]) >>
  ‘TSg (Wr (server_v V hf lfdn)) ifds s0 N = sproj V (trans (server_v V hf lfdn) IH)’
    by (qpat_x_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘N’ mp_tac) >>
        simp[TAKE_LENGTH_ID_rwt]) >>
  qspec_then ‘IH’ mp_tac (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] sv_handler_view) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (‘fresh (TSg (Wr (server_v V hf lfdn)) ifds s0 N)’ by metis_tac[gen_fresh] >>
          pop_assum mp_tac >>
          qpat_assum ‘TSg _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
          simp[freshv_def, acceptedv_def, fresh_def])
      >- (‘prompt (Wr (server_v V hf lfdn)) H’ by simp[Abbr ‘H’, prompt_ghist] >>
          simp[Abbr ‘IH’])
      >> ‘MEM (w2n c) (accepted (TSg (Wr (server_v V hf lfdn)) ifds s0 N))’
           by (qpat_x_assum ‘∀k. accepted _ = _’ (fn th => REWRITE_TAC[th]) >>
               simp[MEM_MAP] >> metis_tac[])
      >> pop_assum mp_tac >> qpat_assum ‘TSg _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
      simp[acceptedv_def]) >>
  strip_tac >>
  ‘a ≤ n’
    by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> disch_then irule >>
        ‘TSg (Wr (server_v V hf lfdn)) ifds s0 n =
         sproj V (trans (server_v V hf lfdn) (TAKE n IH))’
          by (qpat_x_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘n’ mp_tac) >> simp[]) >>
        ‘MEM (w2n c) (accepted (TSg (Wr (server_v V hf lfdn)) ifds s0 n))’
          by (qpat_x_assum ‘∀k. accepted _ = _’ (fn th => REWRITE_TAC[th]) >>
              simp[MEM_MAP] >> metis_tac[]) >>
        pop_assum mp_tac >> qpat_assum ‘TSg _ _ _ n = _’ (fn th => REWRITE_TAC[th]) >>
        simp[acceptedv_def]) >>
  qexistsl_tac [‘a’, ‘g’] >> simp[] >> rpt strip_tac
  >- (‘a + i < N’ by simp[] >> simp[Abbr ‘IH’])
  >- (qpat_x_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘a + j’ mp_tac) >>
      simp[] >> disch_then kall_tac >> simp[sproj_FILTER_on_fd])
  >> ‘MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 (a + j)) =
      TAKE (a + j) H’
       by simp[Abbr ‘H’, GSYM MAP_TAKE, ghist_TAKE] >>
  simp[] >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[Abbr ‘IH’]
QED

(* MAIN: server_v_live, for outputs that depend on the answers *)
Theorem server_v_live_ans:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_live_va V hf out B ∧ (∀ans. FLAT (out "" ans) = "") ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D (conn_answers V Wr inner hf lfdn (EI lfdn) s0 N c))) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0)
                       (SUC N)))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘asyncLevel1$wf (Wr (server_v V hf lfdn))’ by fs[wrap_ok_def] >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  ‘accepts_progress lfdn (Wr (server_v V hf lfdn))’ by metis_tac[accepts_progress_wrap] >>
  ‘grun_ok (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by (irule gen_grun_ok >> metis_tac[]) >>
  (* nothing owed *)
  Cases_on ‘D = ""’
  >- (qexists_tac ‘0’ >> gvs[bytes_def]) >>
  (* otherwise something was sent on c, so c is a connection by round n *)
  ‘sent_upto c n s0 ≠ []’ by (strip_tac >> Cases_on ‘D’ >> fs[bytes_def]) >>
  ‘is_conn (gstate (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  (* it is handed out at some round N0 *)
  ‘∃N0. MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (EI lfdn) s0 N0))’
    by (irule m_conn_accepted >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘n1 = n + N0’ >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (EI lfdn) s0 n1))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[Abbr ‘n1’]) >>
  ‘bytes D ≼ sent_upto c n1 s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[Abbr ‘n1’, sent_upto_prefix]) >>
  (* its handler's view, B D rounds past n1 *)
  qspecl_then [‘n1’, ‘n1 + B D’] mp_tac
    (Q.GENL [‘n’, ‘N’] view_wrap_ans |> Q.INST [‘ifds’ |-> ‘EI lfdn’]) >>
  impl_tac >- simp[] >> strip_tac >>
  (* the socket world gives the handler its environment *)
  ‘interest_covers (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by simp[interest_covers_EI] >>
  ‘henv_t (w2n c) (λq. sproj V (trans (hf (w2n c)) q)) g (n1 − a) D ∧
   ∀j. j ≤ LENGTH g ⇒
     bytes (FLAT (written (w2n c) ((λq. sproj V (trans (hf (w2n c)) q)) (TAKE j g)))) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0)
                        (SUC (a + j))))’
    by (irule m_view_henv >> simp[] >> qexists_tac ‘lfdn’ >> fs[]) >>
  (* so it writes out D *)
  qpat_x_assum ‘handler_live_va _ _ _ _’ (mp_tac o REWRITE_RULE [handler_live_va_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘n1 − a’, ‘D’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac ‘a + j’ >>
  ‘conn_answers V Wr inner hf lfdn (EI lfdn) s0 (a + j) c =
   kanswers V (trans (hf (w2n c)) (TAKE j g))’
    by (simp[conn_answers_def] >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ bytes _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  REWRITE_TAC[bytes_prefix_sw] >>
  qpat_x_assum ‘out D _ ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* MAIN: the answers named only existentially (server_v_live_a's form) *)
Theorem server_v_live_a:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_live_va V hf out B ∧ (∀ans. FLAT (out "" ans) = "") ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N ans. bytes (FLAT (out D ans)) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0) N))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘asyncLevel1$wf (Wr (server_v V hf lfdn))’ by fs[wrap_ok_def] >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  ‘accepts_progress lfdn (Wr (server_v V hf lfdn))’ by metis_tac[accepts_progress_wrap] >>
  ‘grun_ok (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by (irule gen_grun_ok >> metis_tac[]) >>
  (* nothing owed *)
  Cases_on ‘D = ""’
  >- (qexistsl [‘0’, ‘[]’] >> gvs[bytes_def]) >>
  (* otherwise something was sent on c, so c is a connection by round n *)
  ‘sent_upto c n s0 ≠ []’ by (strip_tac >> Cases_on ‘D’ >> fs[bytes_def]) >>
  ‘is_conn (gstate (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  (* it is handed out at some round N0 *)
  ‘∃N0. MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (EI lfdn) s0 N0))’
    by (irule m_conn_accepted >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘n1 = n + N0’ >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (EI lfdn) s0 n1))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[Abbr ‘n1’]) >>
  ‘bytes D ≼ sent_upto c n1 s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[Abbr ‘n1’, sent_upto_prefix]) >>
  (* its handler's view, B D rounds past n1 *)
  qspecl_then [‘n1’, ‘n1 + B D’] mp_tac
    (Q.GENL [‘n’, ‘N’] view_wrap |> Q.INST [‘ifds’ |-> ‘EI lfdn’]) >>
  impl_tac >- simp[] >> strip_tac >>
  (* the socket world gives the handler its environment *)
  ‘interest_covers (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by simp[interest_covers_EI] >>
  ‘henv_t (w2n c) (λq. sproj V (trans (hf (w2n c)) q)) g (n1 − a) D ∧
   ∀j. j ≤ LENGTH g ⇒
     bytes (FLAT (written (w2n c) ((λq. sproj V (trans (hf (w2n c)) q)) (TAKE j g)))) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0)
                        (SUC (a + j))))’
    by (irule m_view_henv >> simp[] >> qexists_tac ‘lfdn’ >> fs[]) >>
  (* so it writes out D *)
  qpat_x_assum ‘handler_live_va _ _ _ _’ (mp_tac o REWRITE_RULE [handler_live_va_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘n1 − a’, ‘D’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl [‘SUC (a + j)’, ‘kanswers V (trans (hf (w2n c)) (TAKE j g))’] >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ bytes _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  REWRITE_TAC[bytes_prefix_sw] >>
  qpat_x_assum ‘out D _ ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* server_v_live's statement, re-derived through server_v_live_a *)
Theorem server_v_live_via_a:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_live_v V hf out B ∧ FLAT (out "") = "" ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0) N))
Proof
  rw[handler_live_v_va] >>
  mp_tac (Q.GEN ‘out’ server_v_live_a) >>
  disch_then (qspec_then ‘λD ans. out D’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> qexists_tac ‘N’ >> fs[]
QED
