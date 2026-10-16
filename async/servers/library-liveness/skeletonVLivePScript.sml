(*
  skeletonVLiveP: the library liveness theorem with a general
  per-handler goal, for handlers whose queries must be answered by the
  store (design/34, KV; additive over skeletonVLive, skeletonVLiveAns).

   - kans_ok V tr: every answered query in tr was answered with a store
     answer (V.kans x ≠ NONE).  wrap_kans V Wr inner: the wrapper answers
     every query of the inner computation that way (with_store does).
   - handler_live_vp V hf Q B: in every environment henv_t whose query
     answers are store answers, the handler reaches, within B D rounds, a
     point where Q holds of D, its answers so far, and its writes so far.
     handler_live_va (out D ks ≼ writes) is the instance
     Q D ks ws ⇔ out D ks ≼ ws (handler_live_va_vp).
   - server_v_live_p (MAIN): then on every connection c, for every prefix D
     of what was sent, Q holds of D, some answers and some writes whose
     bytes are what the loop has written to c by some round.

  The KV handler stops if a query is not answered by the store, so it is
  live only in environments where kans_ok holds; and kv_live asks for a
  number of whole responses, which Q can say directly.
*)
Theory skeletonVLiveP
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  echoProgress socketWorld socketFair EchoSpec HttpGetSpec
  loopPollWorld loopRounds relabel relabelDist
  echoSockModel loopSockInv loopRoundsTrans loopPollDyn echoRunOk
  echoLiveSched echoLiveAccount echoLiveProg echoLiveWorld echoLiveReadSoon
  echoLiveQueue echoLiveAcceptSoon echoLiveDrain skeletonRunOk skeleton
  echoServerUses skeletonUses skeletonProgress skeletonSock
  skeletonLive skeletonV skeletonVProgress skeletonVLive
  skeletonVLiveAns
Libs
  preamble

(* Every answered query in tr has a store answer *)
Definition kans_ok_def:
  kans_ok (V : ('act, 'k, 'q, 'res) vocab) (tr : ('act # 'res option) list) ⇔
    ∀a x. MEM (a, SOME x) tr ∧ V.sact a = NONE ⇒ V.kans x ≠ NONE
End

(* The wrapper answers every query of the inner computation with a store
   answer *)
Definition wrap_kans_def:
  wrap_kans (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, 'x) vmach -> 'y smach) inner ⇔
    ∀m h. asyncLevel1$wf m ⇒ kans_ok V (trans m (inner m h))
End

Theorem kans_ok_FILTER:
  kans_ok V tr ⇒ kans_ok V (FILTER P tr)
Proof
  simp[kans_ok_def, MEM_FILTER] >> metis_tac[]
QED

(* The per-handler obligation, with a general goal Q, in environments whose
   queries are answered by the store *)
Definition handler_live_vp_def:
  handler_live_vp (V : ('act, 'k, 'q, 'res) vocab) (hf : num -> ('act, 'res, 'z) vmach)
                  (Q : string -> 'k option list -> string list -> bool) B ⇔
    ∀fd g j0 D.
      prompt (hf fd) g ∧ henv_t fd (λq. sproj V (trans (hf fd) q)) g j0 D ∧
      (∀j. j ≤ LENGTH g ⇒ kans_ok V (trans (hf fd) (TAKE j g))) ∧
      j0 + B D ≤ LENGTH g ⇒
      ∃j. j ≤ LENGTH g ∧
          Q D (kanswers V (trans (hf fd) (TAKE j g)))
              (written fd (sproj V (trans (hf fd) (TAKE j g))))
End

(* handler_live_va is the goal "what is owed is a prefix of the writes" *)
Theorem handler_live_va_vp:
  handler_live_va V hf out B ⇒ handler_live_vp V hf (λD ks ws. out D ks ≼ ws) B
Proof
  rw[handler_live_va_def, handler_live_vp_def] >> metis_tac[]
QED

(* MAIN: the library liveness theorem for a general goal Q: on every
   connection c, for every prefix D of what its client sent, Q holds of D,
   the handler's answers, and writes whose bytes the loop has written to c *)
Theorem server_v_live_p:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  wrap_kans V Wr inner ∧ vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_live_vp V hf Q B ∧ Q "" [] [] ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N ks ws. Q D ks ws ∧
    bytes (FLAT ws) =
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
  >- (qexistsl [‘0’, ‘[]’, ‘[]’] >> gvs[bytes_def, bytes_written_to_def]) >>
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
  (* the wrapper answered the handler's queries with store answers *)
  ‘∀j. j ≤ LENGTH g ⇒ kans_ok V (trans (hf (w2n c)) (TAKE j g))’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd_v _ _) _ = _’
          (qspec_then ‘j’ mp_tac) >>
        simp[] >> disch_then (SUBST1_TAC o SYM) >>
        irule kans_ok_FILTER >> fs[wrap_kans_def]) >>
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
