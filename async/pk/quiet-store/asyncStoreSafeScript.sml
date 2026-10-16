(*
  Write safety for the skeleton in a wrapper (design/37 §5, step C2):
  asyncStableGen's wsafe, from the handlers.

  hsafe V hf: on any prompt history, each handler has written no more
  often than bytes it has read.  If every handler has it, so has the
  skeleton in any wrapper, in the polling run (wsafe_wrap): what the run
  shows of an accepted connection c is c's handler's transcript
  (asyncServerVLive's view_wrap), and a connection never accepted is never
  touched (uses_ok).

  The query handler has hsafe (proto_v_hsafe: asyncProtoDrainV's Wq_resps,
  at most one response per complete request), and owns its actions if its
  queries are tagged with its fd (proto_v_hokv).  So the store server,
  with_store over the skeleton with query handlers, meets wsafe
  (store_wsafe).

  With asyncWrapActs' per-action cause, the store server meets all of
  asyncStableGen's conditions, so its actions stop after the last arrival
  (store_acts_stop).

  MAIN: wsafe_wrap, proto_v_hsafe, proto_v_hokv, store_wsafe,
  store_acts_stop.
*)
Theory asyncStoreSafe
Ancestors
  pair list rich_list arithmetic option pred_set words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncM4ServerUses asyncM4GRounds asyncRunOkGen asyncSWSock
  asyncWithStore asyncServerV asyncServerVProgress asyncServerVLive
  asyncServerVKv asyncProto asyncProtoV asyncProtoMachineV asyncProtoDrainV
  asyncProtoMeasure asyncStableGen asyncProtoVActs asyncSVActs asyncWrapActs
Libs
  preamble

(* Each handler writes no more often than bytes it has read *)
Definition hsafe_def:
  hsafe V hf ⇔
    ∀fd g. prompt (hf fd) g ⇒
           LENGTH (written fd (sproj V (trans (hf fd) g))) ≤
           LENGTH (CONCAT (read fd (sproj V (trans (hf fd) g))))
End

(* ------------------------------------------------------------------------
   From the handlers to the skeleton
   ------------------------------------------------------------------------ *)

(* A connection never handed out is never read or written *)
Theorem unaccepted_untouched:
  ∀tr. acc_first fd tr ∧ ¬MEM fd (accepted tr) ⇒ FILTER (on_fd fd) tr = []
Proof
  Induct >> simp[acc_first_def] >> PairCases >> simp[] >>
  Cases_on ‘h0’ >> Cases_on ‘h1’ >> TRY (rename1 ‘SOME x’ >> Cases_on ‘x’) >>
  rw[accepts_def, on_fd_def] >> gvs[]
QED

(* MAIN: if every handler is safe, so is the skeleton in any wrapper, in
   the polling run *)
Theorem wsafe_wrap:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧ hsafe V hf ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  wsafe (Wr (server_v V hf lfdn)) ifds s0
Proof
  rw[wsafe_def] >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  Cases_on ‘MEM fd (accepted (TSg (Wr (server_v V hf lfdn)) ifds s0 n))’
  >- (‘∃c. fd = w2n c ∧ MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 n))’
        by (drule_all TSg_accepted >> disch_then (qspecl_then [‘n’, ‘ifds’] mp_tac) >>
            strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
      gvs[] >>
      ‘∃a g. a ≤ n ∧ LENGTH g + a = n ∧ prompt (hf (w2n c)) g ∧
         (∀i. i < LENGTH g ⇒
              (EL i g).ready =
              (EL (a + i) (MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 n))).ready) ∧
         ∀j. j ≤ LENGTH g ⇒
           FILTER (on_fd (w2n c)) (TSg (Wr (server_v V hf lfdn)) ifds s0 (a + j)) =
           sproj V (trans (hf (w2n c)) (TAKE j g))’
        by (irule view_wrap >> simp[] >> qexists_tac ‘inner’ >> simp[]) >>
      ‘FILTER (on_fd (w2n c)) (TSg (Wr (server_v V hf lfdn)) ifds s0 n) =
       sproj V (trans (hf (w2n c)) g)’
        by (first_x_assum (qspec_then ‘LENGTH g’ mp_tac) >>
            ‘a + LENGTH g = n’ by simp[] >> simp[]) >>
      ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER] >>
      pop_assum SUBST1_TAC >>
      fs[hsafe_def])
  >> ‘FILTER (on_fd fd) (TSg (Wr (server_v V hf lfdn)) ifds s0 n) = []’
       by (irule unaccepted_untouched >> fs[uses_ok_def]) >>
  ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER] >> simp[]
QED

(* ------------------------------------------------------------------------
   The query handler
   ------------------------------------------------------------------------ *)

(* MAIN: the query handler writes at most one response per complete
   request, hence no more often than bytes it has read *)
Theorem proto_v_hsafe:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ⇒
  hsafe V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, ""))
Proof
  rw[hsafe_def] >>
  ‘proto_handler_v V P (ansq fd) (fin fd) (fd, "") = qcomp V P (ansq fd) (fin fd) fd (QA "")’
    by simp[qcomp_def] >>
  fs[] >>
  ‘LENGTH g ≤ LENGTH g’ by simp[] >>
  qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
  qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
  qpat_assum ‘LENGTH g ≤ LENGTH g’ (fn t5 =>
    mp_tac (MATCH_MP Wq_resps (CONJ (LIST_CONJ [t1, t2, t3, t4]) t5))))))) >>
  simp[TAKE_LENGTH_ID] >> strip_tac >>
  drule IS_PREFIX_LENGTH >>
  qmatch_goalsub_abbrev_tac ‘LENGTH (CONCAT RR)’ >>
  ‘LENGTH (proto_all P (CONCAT RR)) ≤ LENGTH (CONCAT RR)’ by simp[proto_all_LENGTH] >>
  qmatch_goalsub_abbrev_tac ‘resps _ _ _ KK’ >>
  ‘LENGTH (resps (ansq fd) (fin fd) (proto_all P (CONCAT RR)) KK) ≤
   LENGTH (proto_all P (CONCAT RR))’ by simp[resps_LENGTH] >>
  decide_tac
QED

(* An emit of an action of fd, then a continuation that acts on fd only
   (on shorter histories) *)
Theorem every_emit[local]:
  V.owner a = SOME fd ∧
  (∀r h'. LENGTH h' < LENGTH h ⇒ EVERY (on_fd_v V fd) (trans (f r) h')) ⇒
  EVERY (on_fd_v V fd) (trans (bind (emit a) f) h)
Proof
  strip_tac >> qspecl_then [‘a’, ‘f’, ‘h’] strip_assume_tac emit_split >>
  gvs[trans_emit, on_fd_v_def] >> rw[on_fd_v_def] >>
  first_x_assum irule >> simp[]
QED

(* The handler of fd acts on fd only, if its queries are fd's *)
Theorem proto_v_own:
  vocab_ok (V : ('act, 'k, 'q, 'res) vocab) ∧
  (∀req q. ansq req = SOME q ⇒ (V : ('act, 'k, 'q, 'res) vocab).owner (V.qry q) = SOME fd) ⇒
  ∀h buf. EVERY (on_fd_v V fd) (trans (proto_handler_v V P ansq fin (fd, buf)) h)
Proof
  strip_tac >>
  ‘(∀fd. V.owner (V.rd fd) = SOME fd) ∧ ∀fd d. V.owner (V.wr fd d) = SOME fd’
    by fs[vocab_ok_def] >>
  gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[proto_handler_v_unfold]
  >> Cases_on ‘P.parse buf’ >> simp[return_def]
  (* a complete request: (the query,) the write, then the rest *)
  >- (rename1 ‘PComplete req rest’ >> Cases_on ‘ansq req’ >> simp[]
      >- (irule every_emit >> simp[])
      >> irule every_emit >> rpt strip_tac >>
      TRY (qpat_x_assum ‘∀req q. _’ drule >> simp[] >> NO_TAC) >>
      simp[] >> irule every_emit >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> simp[])
  (* incomplete: wait, read, continue *)
  >> qmatch_goalsub_abbrev_tac ‘bind (readable fd) K0’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac trans_bind_cases_all
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- gvs[readable_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> gvs[readable_def] >> simp[Abbr ‘K0’]
  >> irule every_emit >> simp[] >> rpt strip_tac
  >> ‘LENGTH h' < LENGTH h1 + LENGTH h2’ by (Cases_on ‘h1’ >> gvs[])
  >> rpt CASE_TAC >> simp[return_def]
QED

(* MAIN: the query handlers meet hokv, if each tags its queries with its
   fd *)
Theorem proto_v_hokv:
  vocab_ok (V : ('act, 'k, 'q, 'res) vocab) ∧
  (∀fd req q. ansq fd req = SOME q ⇒ (V : ('act, 'k, 'q, 'res) vocab).owner (V.qry q) = SOME fd) ⇒
  hokv V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, ""))
Proof
  rw[hokv_def, wf_proto_handler_v, settled_proto_handler_v] >>
  irule proto_v_own >> simp[] >> rpt strip_tac >> res_tac
QED

(* ------------------------------------------------------------------------
   The store server
   ------------------------------------------------------------------------ *)

(* MAIN: the store server, with query handlers that tag their queries with
   their fd, is write-safe in the polling run *)
Theorem store_wsafe:
  proto_ok P ∧ (∀fd req q. ansq fd req = SOME q ⇒ FST q = fd) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  wsafe (with_store δ st
           (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfdn))
        ifds s0
Proof
  strip_tac >> irule wsafe_wrap >>
  simp[vocab_ok_sockV, wrap_ok_with_store] >> rpt conj_tac
  (* the handlers are safe *)
  >> TRY (irule proto_v_hsafe >> simp[vocab_ok_sockV, vocab_qok_sockV] >> NO_TAC)
  (* the wrapper *)
  >> TRY (qexists_tac ‘inner_hist δ st’ >> simp[wrap_ok_with_store] >> NO_TAC)
  (* and own their actions *)
  >> rw[hokv_def, wf_proto_handler_v, settled_proto_handler_v] >>
  irule proto_v_own >> simp[vocab_ok_sockV] >>
  rw[sockV_def] >> PairCases_on ‘q’ >> simp[sock_owner_def] >> res_tac >> fs[]
QED

(* MAIN (C, first half): in a world where only finitely many things arrive,
   the polling run of the store server reaches a round after which it
   performs no actions *)
Theorem store_acts_stop:
  proto_ok P ∧ (∀fd req q. ansq fd req = SOME q ⇒ FST q = fd) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃N n1. N ≤ n1 ∧
    static_g (EI lfdn)
      (srelabel (with_store δ st
         (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfdn)))
      s0 N ∧
    ∀n. n1 ≤ n ⇒
        gacts (EI lfdn)
          (srelabel (with_store δ st
             (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfdn)))
          s0 n = []
Proof
  strip_tac >> irule acts_stop_gen >> simp[] >> rpt conj_tac
  (* write safety *)
  >> TRY (irule store_wsafe >> simp[] >> metis_tac[] >> NO_TAC)
  (* the socket API *)
  >> TRY (irule uses_ok_wrap >> simp[vocab_ok_sockV] >>
          rpt conj_tac >>
          TRY (qexists_tac ‘inner_hist δ st’ >> simp[wrap_ok_with_store] >> NO_TAC) >>
          rw[hokv_def, wf_proto_handler_v, settled_proto_handler_v] >>
          irule proto_v_own >> simp[vocab_ok_sockV] >>
          rw[sockV_def] >> PairCases_on ‘q’ >> simp[sock_owner_def] >> res_tac >> fs[] >>
          NO_TAC)
  (* the per-action cause *)
  >> rw[acts_cause_def]
  >- simp[with_store_def, sv_NIL_actions, socks_def]
  >> drule store_proto_new_actions >> simp[]
QED
