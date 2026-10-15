(*
  asyncServerVLiveA: the library liveness theorem for STATEFUL servers
  (design/34, KV; additive over asyncServerVLive).

  handler_live_va generalises handler_live_v: the output owed for data D
  may also depend on the answers the handler received to its queries (for
  KV: the store's answers), in order, read off its transcript (kanswers).
  server_v_live_a is server_v_live for it; and handler_live_v is the
  instance whose output ignores the answers (handler_live_v_va), so
  server_v_live's statement is a corollary (server_v_live_via_a).
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

(* MAIN: server_v_live, for outputs that depend on the answers *)
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
