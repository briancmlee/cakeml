(*
  HttpSpecBodies2 bites: the statement rules out plausible bugs, and its
  assumptions are satisfiable with fds actually reused.  Everything here
  is proved.

  - NEW, fd reuse: a server that answers a previous connection's request
    on the new connection that reuses its fd violates http_safe_b2
    (broken_answers_across_reuse).  HttpSpecBodies' per-fd http_safe_b
    does NOT catch this bug (v1_misses_answer_leak), which is why
    HttpSpecBodies2 projects per episode.
  - NEW, closing: a server that answers, reads the client's EOF and never
    closes (version 1's behaviour) is safe and live, but violates
    http_closes_b2 (broken_never_closes_b).
  - Non-vacuity: a fair version-2 world in which two clients each send
    rp (HttpSpecBodiesBite's POST /echo whose body looks like a request)
    and close (two_clients_world2), and an ideal trace for it, with two
    episodes on the same fd, that is safe, live and closes
    (ideal_b2_trace_spec).
  HttpSpecBodies' own bites (framing, answering before the body, never
  answering) carry over per episode: each is about a single connection.
*)
Theory HttpSpecBodies2Bite
Ancestors
  HttpSpecBodies2 HttpSpecBodiesBite HttpSpecBodies HttpSpecHeaders HttpSpec
  EchoSpec2Bite EchoSpec2 EchoSpecBite EchoSpec ffiSpikeSocketFFI
  socketV2FFI socketV2Fair llist Marshalling
Libs
  preamble

Overload R = “brequests [rp]”
Overload P = “bresponses site [rp]”

(* ------------------------------------------------------------------------
   Requests (as in HttpSpecBodiesBite, where these are local)
   ------------------------------------------------------------------------ *)

Theorem bytes_split[local]:
  ∀s p rest. bytes p ++ rest = bytes s ⇒ ∃s'. s = p ++ s' ∧ rest = bytes s'
Proof
  simp[bytes_def] >> Induct_on ‘p’ >> rw[] >>
  Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem brequests_CONS[local]:
  brequests [] = [] ∧
  brequests (r :: rs) = bytes (print_brequest r) ++ brequests rs
Proof
  simp[brequests_def, bytes_def]
QED

Theorem print_brequest_NIL[local]:
  print_brequest r ≠ []
Proof
  Cases_on ‘r’ >> simp[print_brequest_def]
QED

Theorem brequests_NIL[local]:
  brequests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[brequests_CONS, bytes_def, print_brequest_NIL]
QED

Theorem brequests_of_one[local]:
  valid_brequest r ∧ EVERY valid_brequest rs ∧
  brequests rs ++ rest = brequests [r] ⇒
  rs = [] ∨ (rs = [r] ∧ rest = [])
Proof
  Cases_on ‘rs’ >> rw[] >> fs[brequests_CONS] >>
  ‘bytes (print_brequest h) ++ (brequests t ++ rest) = bytes (print_brequest r)’
    by fs[] >>
  drule bytes_split >> strip_tac >>
  ‘h = r ∧ s' = []’
    by (irule print_brequest_unique >> fs[]) >>
  qpat_x_assum ‘print_brequest r = _’ kall_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[bytes_def, APPEND_eq_NIL, brequests_NIL]
QED

Theorem valid_rp[local]:
  valid_brequest rp
Proof
  EVAL_TAC
QED

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

Theorem prefix_take[local]:
  evs ≼ l ⇔ ∃n. n ≤ LENGTH l ∧ evs = TAKE n l
Proof
  eq_tac >> rw[]
  >- (qexists_tac ‘LENGTH evs’ >> gvs[IS_PREFIX_APPEND] >> simp[TAKE_APPEND1])
  >> simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP n l’ >> simp[]
QED

(* Safety on one connection that is sent rp: having read nothing, nothing
   is written; having read rp, a prefix of its response is *)
Theorem safe_rp[local]:
  EVERY valid_brequest rs ∧ X = brequests rs ++ rest ∧ no_full_brequest rest ∧
  (X = [] ∧ W = [] ∨ X = R ∧ (W = [] ∨ W = P)) ⇒
  W ≼ bresponses site rs
Proof
  rw[] >> simp[] >>
  qspecl_then [‘rp’, ‘rs’, ‘rest’] mp_tac (GEN_ALL brequests_of_one) >>
  simp[valid_rp] >> rw[] >> gvs[] >>
  fs[no_full_brequest_def] >> metis_tac[valid_rp, IS_PREFIX_REFL]
QED

(* ------------------------------------------------------------------------
   fd reuse: a new connection never receives the previous one's answer
   ------------------------------------------------------------------------ *)

(* Read rp on fd c1, close c1 without answering, accept a new connection
   that reuses c1, and answer rp on it *)
Overload answer_leak = “[acc L c1; rd c1 R 100; cls c1; acc L c1; wr c1 P]”

(* NEW: such a server violates HttpSpecBodies2's safety *)
Theorem broken_answers_across_reuse:
  starts_with answer_leak io ⇒ ¬http_safe_b2 site io
Proof
  rw[http_safe_b2_def] >> qexistsl [‘answer_leak’, ‘1’, ‘[]’, ‘[]’] >>
  simp[no_full_brequest_def, brequests_NIL] >> EVAL_TAC
QED

(* ... but HttpSpecBodies' per-fd safety does not catch it: on fd c1, rp
   was read and its response written *)
Theorem v1_misses_answer_leak:
  http_safe_b site (fromList answer_leak) ∧ ¬http_safe_b2 site (fromList answer_leak)
Proof
  conj_tac
  >- (rw[http_safe_b_def, LPREFIX_fromList_fromList, prefix_take] >>
      irule safe_rp >> qexistsl [‘bytes_read_from c (TAKE n answer_leak)’, ‘rest’] >>
      simp[] >>
      ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5’ by gvs[] >> gvs[] >>
      EVAL_TAC >> rw[] >> EVAL_TAC)
  >> irule broken_answers_across_reuse >> simp[]
QED

(* ------------------------------------------------------------------------
   A fair world with reuse: two clients, each sends rp and closes
   ------------------------------------------------------------------------ *)

Definition two_clients_world2_def:
  two_clients_world2 =
    <| listening := [(3w, [])]; clients := []; open_fds := [];
       reserved := [0w; 1w; 2w]; alloc := (λj. lowest_free);
       future := [| [Connect2 3w; Data2 0 R; Eof2 0];
                    [Connect2 3w; Data2 1 R; Eof2 1] |] |>
End

Theorem ticks2_quiet[local]:
  ∀n s. s.future = [||] ⇒ ticks2 n s = s
Proof
  Induct >> rw[ticks2_def, tick2_def]
QED

Theorem two_clients_world2_sched_wf[local]:
  sched_wf2 two_clients_world2
Proof
  rw[sched_wf2_def] >> Cases_on ‘n’ >- EVAL_TAC
  >> Cases_on ‘n'’ >- EVAL_TAC
  >> simp[ticks2_def]
  >> ‘(tick2 (tick2 two_clients_world2)).future = [||]’ by EVAL_TAC
  >> simp[ticks2_quiet, next_step2_def, step_ok2_def]
QED

(* NON-VACUITY: the assumption holds *)
Theorem server_world2_two_clients:
  server_world2 3w two_clients_world2
Proof
  simp[server_world2_def, two_clients_world2_sched_wf] >> conj_tac >- EVAL_TAC >>
  simp[two_clients_world2_def, lowest_free_alloc_ok]
QED

Theorem arrivals2_upto_nil[local]:
  arrivals2_upto n [||] = []
Proof
  Cases_on ‘n’ >> simp[arrivals2_upto_def]
QED

Theorem sent2_upto_two_clients[local]:
  sent2_upto j n two_clients_world2 =
    if j = 0 ∧ 1 ≤ n then R else if j = 1 ∧ 2 ≤ n then R else []
Proof
  Cases_on ‘n’ >> simp[sent2_upto_def, arrivals2_upto_def, two_clients_world2_def]
  >> Cases_on ‘n'’ >> simp[arrivals2_upto_def, arrivals2_upto_nil] >> rw[]
QED

(* What a client of this world has sent is no request, or rp *)
Theorem sent_rp[local]:
  EVERY valid_brequest rs ∧ brequests rs ≼ sent2_upto j n two_clients_world2 ⇒
  rs = [] ∨ (rs = [rp] ∧ (j = 0 ∧ 1 ≤ n ∨ j = 1 ∧ 2 ≤ n))
Proof
  rw[sent2_upto_two_clients] >> gvs[brequests_NIL] >>
  fs[IS_PREFIX_APPEND] >> drule_all brequests_of_one >> simp[valid_rp]
QED

(* ------------------------------------------------------------------------
   An ideal trace, with two episodes on the same fd
   ------------------------------------------------------------------------ *)

(* Accept client 0 on fd 4, read rp, answer it, read EOF, close fd 4;
   accept client 1, again on fd 4, the same *)
Overload ideal_b2 =
  “[acc L 4w; rd 4w R 100; wr 4w P; rdeof 4w 100; cls 4w;
    acc L 4w; rd 4w R 100; wr 4w P; rdeof 4w 100; cls 4w]”

Theorem ideal_b2_safe[local]:
  http_safe_b2 site (fromList ideal_b2)
Proof
  rw[http_safe_b2_def, LPREFIX_fromList_fromList, prefix_take] >>
  irule safe_rp >> qexistsl [‘ep_read j (TAKE n ideal_b2)’, ‘rest’] >> simp[] >>
  ‘n ≤ 10’ by gvs[] >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
   n = 8 ∨ n = 9 ∨ n = 10’ by simp[] >>
  ‘j = 0 ∨ j = 1 ∨ 2 ≤ j’ by simp[] >> gvs[] >> EVAL_TAC >> simp[]
QED

Theorem ideal_b2_live[local]:
  http_live_b2 site two_clients_world2 (fromList ideal_b2)
Proof
  rw[http_live_b2_def] >> drule_all sent_rp >> rw[]
  >- (qexists_tac ‘[]’ >> simp[] >> EVAL_TAC)
  >> qexists_tac ‘ideal_b2’ >> simp[LPREFIX_fromList_fromList] >> EVAL_TAC
QED

Theorem ideal_b2_closes[local]:
  http_closes_b2 (fromList ideal_b2)
Proof
  rw[http_closes_b2_def, echo_closes2_def, LPREFIX_fromList_fromList] >>
  qexists_tac ‘ideal_b2’ >> simp[] >>
  ‘j < LENGTH (accepted_fds evs)’ by gvs[ep_eof_read_def] >>
  ‘accepted_fds evs ≼ accepted_fds ideal_b2’
    by (qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
        ASM_REWRITE_TAC [accepted_fds_def, MAP_APPEND, FLAT_APPEND] >>
        REWRITE_TAC [IS_PREFIX_APPEND] >> metis_tac[]) >>
  ‘LENGTH (accepted_fds ideal_b2) = 2’ by EVAL_TAC >>
  imp_res_tac IS_PREFIX_LENGTH >>
  ‘j = 0 ∨ j = 1’ by simp[] >> gvs[] >> EVAL_TAC
QED

(* NON-VACUITY: in a fair world with reuse, the three clauses are jointly
   satisfiable *)
Theorem ideal_b2_trace_spec:
  server_world2 3w two_clients_world2 ∧
  http_safe_b2 site (fromList ideal_b2) ∧
  http_live_b2 site two_clients_world2 (fromList ideal_b2) ∧
  http_closes_b2 (fromList ideal_b2)
Proof
  simp[server_world2_two_clients, ideal_b2_safe, ideal_b2_live, ideal_b2_closes]
QED

(* ------------------------------------------------------------------------
   A server that never closes
   ------------------------------------------------------------------------ *)

(* Version 1's behaviour: answer each client, read its EOF, never close;
   the second client gets a fresh fd (5), as fd 4 is still in use *)
Overload noclose_b2 =
  “[acc L 4w; rd 4w R 100; wr 4w P; rdeof 4w 100;
    acc L 5w; rd 5w R 100; wr 5w P; rdeof 5w 100]”

(* NEW: it is safe and live, but violates http_closes_b2 *)
Theorem broken_never_closes_b:
  http_safe_b2 site (fromList noclose_b2) ∧
  http_live_b2 site two_clients_world2 (fromList noclose_b2) ∧
  ¬http_closes_b2 (fromList noclose_b2)
Proof
  rpt conj_tac
  >- (rw[http_safe_b2_def, LPREFIX_fromList_fromList, prefix_take] >>
      irule safe_rp >> qexistsl [‘ep_read j (TAKE n noclose_b2)’, ‘rest’] >>
      simp[] >> ‘n ≤ 8’ by gvs[] >>
      ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
       n = 8’ by simp[] >>
      ‘j = 0 ∨ j = 1 ∨ 2 ≤ j’ by simp[] >> gvs[] >> EVAL_TAC >> simp[])
  >- (rw[http_live_b2_def] >> drule_all sent_rp >> rw[]
      >- (qexists_tac ‘[]’ >> simp[] >> EVAL_TAC)
      >> qexists_tac ‘noclose_b2’ >> simp[LPREFIX_fromList_fromList] >> EVAL_TAC)
  >> rw[http_closes_b2_def, echo_closes2_def, LPREFIX_fromList_fromList] >>
  qexistsl [‘noclose_b2’, ‘0’] >> simp[] >> conj_tac >- EVAL_TAC >>
  rw[] >> Cases_on ‘evs' ≼ noclose_b2’ >> simp[] >> gvs[prefix_take] >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
   n = 8’ by simp[] >> gvs[] >> EVAL_TAC
QED
