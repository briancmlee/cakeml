(*
  Liveness of the HTTP server in the closed loop (asyncWorld): on an
  accepted connection, every complete request that has arrived is
  eventually answered.

  closed_loop_http_accepted: if by round n the connection c has been
  accepted and the data D has arrived on it, then by round
  n + 2K + 3, where K is the number of complete requests at the front of D,
  the responses to those K requests have been written to c.

  The proof puts together
   - the handler's view of the server's history (asyncSWProgress's
     sw_handler_view): the handler of c runs on its own history g, from
     the round a in which c was accepted;
   - the machine-level liveness theorem (asyncHttpDrain's hmachine_live),
     whose four environment facts are discharged here from the world
     model: readiness is reported truthfully, a read takes everything that
     has arrived, and end-of-file comes after all the data.
*)
Theory asyncHttpLiveness
Ancestors
  pair list rich_list arithmetic option pred_set string alist
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncWorld asyncClosedLoop asyncLiveness asyncServerWith
  asyncSWProgress asyncSWClosedLoop HttpSpec asyncHttpParse asyncHttpServer
  asyncHttpMachine asyncHttpDrain
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The machine: reading and end-of-file in its transcript
   ------------------------------------------------------------------------ *)

(* In state HB the handler has a read of fd outstanding *)
Theorem hmachine_reading:
  prompt (hcomp files fd (HA "")) g ∧ j ≤ LENGTH g ∧ Sj files fd g j = HB b ⇒
  MEM (Read fd, NONE) (trans (hcomp files fd (HA "")) (TAKE j g))
Proof
  strip_tac >> drule_all hmachine_trans_TAKE >> disch_then SUBST1_TAC >>
  simp[MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> qexists_tac ‘j’ >>
  simp[hacts_def, zipr_def]
QED

(* The handler stops on a buffer that is not invalid only after reading
   end-of-file *)
Theorem hmachine_stopped_eof:
  ∀j b. j ≤ LENGTH g ∧ Sj files fd g j = HD b ∧ parse_request b ≠ Invalid ⇒
        ∃i b'. i < j ∧ Sj files fd g i = HB b' ∧ oHD (EL i g).results = SOME Eof
Proof
  Induct >- simp[hrun_def] >>
  rpt strip_tac >>
  ‘j < LENGTH g’ by simp[] >>
  qpat_x_assum ‘Sj _ _ _ (SUC j) = _’ mp_tac >>
  drule_then (qspecl_then [‘files’, ‘fd’] SUBST1_TAC) Sj_SUC >>
  Cases_on ‘Sj files fd g j’ >> simp[hstep_def]
  >- (every_case_tac >> simp[] >> strip_tac >> gvs[])
  >- (every_case_tac >> simp[] >> strip_tac >> gvs[] >>
      qexists_tac ‘j’ >> simp[])
  >> strip_tac >> gvs[] >>
  metis_tac[DECIDE “i < j ⇒ i < SUC j”]
QED

(* So its transcript has the read that returned end-of-file *)
Theorem hmachine_eof:
  prompt (hcomp files fd (HA "")) g ∧ j ≤ LENGTH g ∧
  Sj files fd g j = HD b ∧ parse_request b ≠ Invalid ⇒
  MEM (Read fd, SOME Eof) (trans (hcomp files fd (HA "")) (TAKE j g))
Proof
  strip_tac >> drule_all hmachine_stopped_eof >> strip_tac >>
  drule_all hmachine_trans_TAKE >> disch_then SUBST1_TAC >>
  simp[MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> qexists_tac ‘i’ >>
  simp[hacts_def, zipr_def]
QED

(* ------------------------------------------------------------------------
   The server's transcript in the closed loop, against the world's log
   ------------------------------------------------------------------------ *)

Theorem read_MAP_NONE[local]:
  ∀l. read c (MAP (λa. (a, NONE : asyncServer$response option)) l) = []
Proof
  Induct >> simp[] >> Cases >> simp[]
QED

(* What the server has read is what the world performed *)
Theorem sw_trans_read:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) k = (h, w, p) ⇒
  read c (trans (server_with hf lfd) h) = read c (sperf p)
Proof
  strip_tac >> drule_all sw_fresh >> strip_tac >> simp[read_MAP_NONE]
QED

(* What the server has written by round k is what the world holds after
   round k *)
Theorem sw_trans_written:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) k = (h, w, p) ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) (k + 1) = (h', w', p') ⇒
  written c (trans (server_with hf lfd) h) = written c (sperf p')
Proof
  strip_tac >>
  ‘trans (server_with hf lfd) h =
     sperf p ++ MAP (λa. (a, NONE)) (new_actions (log_of (server_with hf lfd)) h)’
    by metis_tac[sw_fresh] >>
  drule_all closed_loop_step >> strip_tac >> drule perform_all_length >>
  strip_tac >> simp[written_ZIP]
QED

(* An unanswered action in the transcript is one of the round's new ones *)
Theorem sw_trans_none:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) k = (h, w, p) ∧
  MEM (x, NONE) (trans (server_with hf lfd) h) ⇒
  MEM x (new_actions (log_of (server_with hf lfd)) h)
Proof
  strip_tac >> drule_all sw_fresh >> strip_tac >> gvs[] >>
  gvs[sperf_def, MEM_MAP, pairTheory.EXISTS_PROD]
QED

(* An answered action in the transcript was performed by the world *)
Theorem sw_trans_some:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) k = (h, w, p) ∧
  MEM (x, SOME r) (trans (server_with hf lfd) h) ⇒
  MEM (x, r) p
Proof
  strip_tac >> drule_all sw_fresh >> strip_tac >> gvs[] >>
  gvs[sperf_def, MEM_MAP, pairTheory.EXISTS_PROD]
QED

Theorem accepted_prefix[local]:
  p ≼ p' ∧ MEM c (accepted (sperf p)) ⇒ MEM c (accepted (sperf p'))
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* Earlier rounds' histories and logs are prefixes of later ones *)
Theorem sw_prefix[local]:
  closed_loop (server_with hf lfd) (start_world lfd sch) k = (h, w, p) ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) N = (h', w', p') ∧ k ≤ N ⇒
  h = TAKE k h' ∧ p ≼ p'
Proof
  strip_tac >> ‘N = k + (N − k)’ by simp[] >> pop_assum SUBST_ALL_TAC >>
  metis_tac[closed_loop_prefix]
QED

(* What has been written to a connection only grows *)
Theorem sw_outgoing_later:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) k = (h, w, p) ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) N = (h', w', p') ∧ k ≤ N ∧
  ALOOKUP w.conns c = SOME cn ∧ ALOOKUP w'.conns c = SOME cn' ⇒
  cn.outgoing ≼ cn'.outgoing
Proof
  strip_tac >>
  ‘consistent lfd w p ∧ consistent lfd w' p'’ by metis_tac[sw_consistent] >>
  drule_all sw_prefix >> strip_tac >>
  ‘cn.outgoing = CONCAT (written c (sperf p)) ∧
   cn'.outgoing = CONCAT (written c (sperf p'))’ by metis_tac[consistent_def] >>
  gvs[IS_PREFIX_APPEND]
QED

(* ------------------------------------------------------------------------
   The handler's view, in the closed loop
   ------------------------------------------------------------------------ *)

(* MAIN: in the closed loop, a connection c accepted by round n is served by
   its own handler, on a history g that starts at the round a ≤ n in which
   c was accepted.  At every round a + j, the handler's transcript after j
   snapshots is the server's transcript restricted to c. *)
Theorem sw_closed_loop_view:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
  MEM c (accepted (sperf perf)) ∧ n ≤ M ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) M = (hM, wM, pM) ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = M ∧ prompt (hf c) g ∧
        (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) hM).ready) ∧
        ∀j hj wj pj.
          j ≤ LENGTH g ∧
          closed_loop (server_with hf lfd) (start_world lfd sch) (a + j) = (hj, wj, pj) ⇒
          FILTER (on_fd c) (trans (server_with hf lfd) hj) = trans (hf c) (TAKE j g)
Proof
  strip_tac >>
  ‘LENGTH hM = M ∧ LENGTH h = n’ by metis_tac[closed_loop_length] >>
  ‘perf ≼ pM’ by metis_tac[sw_prefix] >>
  ‘trans (server_with hf lfd) h =
     sperf perf ++ MAP (λa. (a,NONE)) (new_actions (log_of (server_with hf lfd)) h) ∧
   trans (server_with hf lfd) hM =
     sperf pM ++ MAP (λa. (a,NONE)) (new_actions (log_of (server_with hf lfd)) hM) ∧
   fresh (trans (server_with hf lfd) hM)’ by metis_tac[sw_fresh] >>
  ‘MEM c (accepted (trans (server_with hf lfd) h)) ∧
   MEM c (accepted (trans (server_with hf lfd) hM))’
    by (asm_rewrite_tac[accepted_APPEND, MEM_APPEND] >> metis_tac[accepted_prefix]) >>
  ‘h = TAKE n hM’ by metis_tac[sw_prefix] >>
  qspec_then ‘hM’ mp_tac (Q.INST [‘fd’ |-> ‘c’] sw_handler_view) >>
  impl_tac
  >- (simp[] >> metis_tac[closed_loop_prompt]) >>
  strip_tac >> qexists_tac ‘a’ >> qexists_tac ‘g’ >> simp[] >>
  conj_tac
  >- (first_x_assum irule >> simp[] >> gvs[]) >>
  rpt strip_tac >>
  ‘hj = TAKE (a + j) hM’ by metis_tac[sw_prefix, DECIDE “j ≤ LENGTH g ∧ LENGTH g + a = M ⇒ a + j ≤ M”] >>
  gvs[]
QED

(* ------------------------------------------------------------------------
   The HTTP server in the closed loop
   ------------------------------------------------------------------------ *)

Theorem hok_http:
  hok (λfd. http_handler files (fd, ""))
Proof
  simp[hok_def, wf_http_handler, settled_http_handler, http_handler_serves]
QED

(* The closed-loop facts used below, for the HTTP server *)
Theorem http_consistent[local]:
  closed_loop (http_server files lfd) (start_world lfd sch) k = (h, w, p) ∧
  ALOOKUP w.conns c = SOME cn ⇒
  cn.received = FLAT (read c (sperf p)) ++ cn.incoming ∧
  cn.outgoing = FLAT (written c (sperf p))
Proof
  rw[http_server_def] >> drule_at (Pos last) sw_consistent >>
  simp[hok_http, consistent_def] >> metis_tac[]
QED

Theorem http_prefix[local]:
  closed_loop (http_server files lfd) (start_world lfd sch) k = (h, w, p) ∧
  closed_loop (http_server files lfd) (start_world lfd sch) N = (h', w', p') ∧ k ≤ N ⇒
  p ≼ p'
Proof
  rw[http_server_def] >> metis_tac[sw_prefix]
QED

Theorem http_received_later[local]:
  closed_loop (http_server files lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ n ≤ k ∧
  closed_loop (http_server files lfd) (start_world lfd sch) k = (h', w', p') ⇒
  ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧ cn.received ≼ cn'.received
Proof
  rw[http_server_def] >> ‘k = n + (k − n)’ by simp[] >> pop_assum SUBST_ALL_TAC >>
  metis_tac[sw_received_later, hok_http]
QED

Theorem http_outgoing_later[local]:
  closed_loop (http_server files lfd) (start_world lfd sch) k = (h, w, p) ∧
  closed_loop (http_server files lfd) (start_world lfd sch) N = (h', w', p') ∧ k ≤ N ∧
  ALOOKUP w.conns c = SOME cn ∧ ALOOKUP w'.conns c = SOME cn' ⇒
  cn.outgoing ≼ cn'.outgoing
Proof
  rw[http_server_def] >> metis_tac[sw_outgoing_later, hok_http]
QED

Theorem http_round_read[local]:
  closed_loop (http_server files lfd) (start_world lfd sch) k = (h, w, p) ∧
  closed_loop (http_server files lfd) (start_world lfd sch) (k + 1) = (h', w', p') ∧
  ALOOKUP w.conns c = SOME cn ∧
  MEM (Read c) (new_actions (log_of (http_server files lfd)) h) ⇒
  cn.received = FLAT (read c (sperf p'))
Proof
  rw[http_server_def] >> metis_tac[sw_round_conn, hok_http]
QED

Theorem http_eof[local]:
  closed_loop (http_server files lfd) (start_world lfd sch) k = (h, w, p) ∧
  MEM (Read c, Eof) p ⇒
  ∃cn. ALOOKUP w.conns c = SOME cn ∧ cn.incoming = ""
Proof
  rw[http_server_def] >> metis_tac[sw_eof, hok_http]
QED

(* A closed-loop lemma about round k, instantiated to the HTTP handler and
   round a + j *)
fun AT_j th =
  Q.GENL [‘hf’, ‘k’, ‘h’, ‘w’, ‘p’] th
  |> Q.ISPEC ‘λfd. http_handler files (fd, "")’
  |> Q.SPECL [‘a + j’, ‘hj’, ‘wj’, ‘pj’];

(* The handler of an accepted connection c, in the closed loop: it runs on
   g from round a; after j snapshots (round a + j), what it has read is
   what the world performed; an action of its still unanswered is one of
   the server's new actions; an answered one was performed; and what it
   has written is what the world holds after round a + j. *)
Theorem http_view:
  closed_loop (http_server files lfd) (start_world lfd sch) n = (h, w, perf) ∧
  MEM c (accepted (sperf perf)) ∧ n ≤ M ∧
  closed_loop (http_server files lfd) (start_world lfd sch) M = (hM, wM, pM) ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = M ∧ prompt (hcomp files c (HA "")) g ∧
    (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) hM).ready) ∧
    ∀j hj wj pj.
      j ≤ LENGTH g ∧
      closed_loop (http_server files lfd) (start_world lfd sch) (a + j) = (hj, wj, pj) ⇒
      Rj files c g j = FLAT (read c (sperf pj)) ∧
      (∀x. MEM (x, NONE) (trans (hcomp files c (HA "")) (TAKE j g)) ⇒
           MEM x (new_actions (log_of (http_server files lfd)) hj)) ∧
      (∀x r. MEM (x, SOME r) (trans (hcomp files c (HA "")) (TAKE j g)) ⇒
             MEM (x, r) pj) ∧
      ∀hj' wj' pj'.
        closed_loop (http_server files lfd) (start_world lfd sch) (a + j + 1) =
          (hj', wj', pj') ⇒
        Wj files c g j = written c (sperf pj')
Proof
  simp[http_server_def] >> strip_tac >>
  assume_tac (Q.GEN ‘files’ hok_http) >>
  pop_assum (qspec_then ‘files’ assume_tac) >>
  drule_all sw_closed_loop_view >> strip_tac >>
  qexists_tac ‘a’ >> qexists_tac ‘g’ >> gvs[hcomp_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (drule_all_then (assume_tac o SYM)) >>
  rpt conj_tac
  >- (asm_rewrite_tac[read_FILTER] >> AP_TERM_TAC >> mp_tac (AT_j sw_trans_read) >> gs[])
  >- (asm_rewrite_tac[MEM_FILTER] >> rpt strip_tac >>
      mp_tac (AT_j sw_trans_none) >> gs[])
  >- (asm_rewrite_tac[MEM_FILTER] >> rpt strip_tac >>
      mp_tac (AT_j sw_trans_some) >> gs[])
  >> rpt strip_tac >> asm_rewrite_tac[written_FILTER] >>
  mp_tac (Q.GENL [‘hf’, ‘k’, ‘h’, ‘w’, ‘p’, ‘h'’, ‘w'’, ‘p'’] sw_trans_written
         |> Q.ISPEC ‘λfd. http_handler files (fd, "")’
         |> Q.SPECL [‘a + j’, ‘hj’, ‘wj’, ‘pj’, ‘hj'’, ‘wj'’, ‘pj'’]) >>
  gs[]
QED

Theorem FLAT_prefix[local]:
  l1 ≼ l2 ⇒ FLAT l1 ≼ FLAT l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* closed_loop_snapshot, for the HTTP server *)
Theorem http_snapshot[local]:
  closed_loop (http_server files lfd) (start_world lfd sch) M = (hM, wM, pM) ∧ k < M ∧
  closed_loop (http_server files lfd) (start_world lfd sch) (k + 1) = (h1, w1, p1) ⇒
  (EL k hM).ready = set (MAP Readable (ready_fds w1))
Proof
  strip_tac >>
  irule (Q.GENL [‘m’, ‘w0’] closed_loop_snapshot
         |> Q.ISPECL [‘http_server files lfd’, ‘start_world lfd sch’]) >>
  metis_tac[]
QED

(* MAIN: liveness of the HTTP server on an accepted connection.  If by round
   n the connection c has been accepted and the data D = cn.received has
   arrived on it, then by every round N ≥ n + 2K + 3, where K is the number
   of complete requests at the front of D, the responses to those requests
   have been written to c. *)
Theorem closed_loop_http_accepted:
  closed_loop (http_server files lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ MEM c (accepted (sperf perf)) ∧
  n + 2 * LENGTH (parse_all cn.received) + 3 ≤ N ∧
  closed_loop (http_server files lfd) (start_world lfd sch) N = (hN, wN, pN) ⇒
  ∃cnN. ALOOKUP wN.conns c = SOME cnN ∧
        FLAT (responses_to files cn.received) ≼ cnN.outgoing
Proof
  strip_tac >>
  qabbrev_tac ‘NK = LENGTH (parse_all cn.received)’ >>
  ‘∃hM wM pM. closed_loop (http_server files lfd) (start_world lfd sch)
                (n + 2 * NK + 2) = (hM, wM, pM)’ by metis_tac[pair_CASES] >>
  (* c's handler runs on g, from round a ≤ n *)
  mp_tac (Q.INST [‘M’ |-> ‘n + 2 * NK + 2 : num’] http_view) >>
  impl_tac >- simp[] >> strip_tac >>
  (* from round n on, c has received D, and what it has received is what
     the handler has read, then the unread data *)
  ‘∀j hj wj pj.
     n ≤ a + j ∧ j ≤ LENGTH g ∧
     closed_loop (http_server files lfd) (start_world lfd sch) (a + j) = (hj, wj, pj) ⇒
     ∃cnj. ALOOKUP wj.conns c = SOME cnj ∧ cn.received ≼ cnj.received ∧
           cnj.received = Rj files c g j ++ cnj.incoming’
    by (rpt strip_tac >>
        mp_tac (Q.INST [‘k’ |-> ‘a + j : num’, ‘h'’ |-> ‘hj’, ‘w'’ |-> ‘wj’, ‘p'’ |-> ‘pj’]
                  http_received_later) >>
        impl_tac >- simp[] >> strip_tac >>
        mp_tac (Q.INST [‘k’ |-> ‘a + j : num’, ‘h’ |-> ‘hj’, ‘w’ |-> ‘wj’, ‘p’ |-> ‘pj’,
                        ‘cn’ |-> ‘cn'’] http_consistent) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_assum ‘∀j hj wj pj. _ ⇒ Rj _ _ _ _ = _ ∧ _’
          (qspecl_then [‘j’, ‘hj’, ‘wj’, ‘pj’] mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qexists_tac ‘cn'’ >> gvs[]) >>
  qabbrev_tac ‘j0 = n − a’ >>
  mp_tac (Q.INST [‘fd’ |-> ‘c’, ‘D’ |-> ‘cn.received’] hmachine_live) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- fs[Abbr ‘j0’, Abbr ‘NK’]
      (* what has been read by round n is a prefix of D *)
      >- (qpat_assum ‘∀j hj wj pj. _ ⇒ ∃cnj. _’
            (qspecl_then [‘j0’, ‘h’, ‘w’, ‘perf’] mp_tac) >>
          impl_tac >- fs[Abbr ‘j0’] >> strip_tac >> gvs[] >>
          simp[IS_PREFIX_APPEND] >> metis_tac[])
      (* waiting while c is not readable: everything has been read *)
      >- (rpt strip_tac >>
          ‘∃h1 w1 p1. closed_loop (http_server files lfd) (start_world lfd sch)
                        (a + j + 1) = (h1, w1, p1)’ by metis_tac[pair_CASES] >>
          qpat_assum ‘∀j hj wj pj. _ ⇒ ∃cnj. _’
            (qspecl_then [‘j + 1’, ‘h1’, ‘w1’, ‘p1’] mp_tac) >>
          impl_tac >- fs[Abbr ‘j0’] >> strip_tac >>
          ‘(EL j g).ready = set (MAP Readable (ready_fds w1))’
            by (‘(EL j g).ready = (EL (a + j) hM).ready’ by gs[] >>
                pop_assum SUBST1_TAC >>
                mp_tac (Q.INST [‘M’ |-> ‘n + 2 * NK + 2 : num’, ‘k’ |-> ‘a + j : num’]
                          http_snapshot) >>
                gs[]) >>
          ‘cnj.incoming = ""’
            by (CCONTR_TAC >>
                mp_tac (Q.INST [‘w’ |-> ‘w1’, ‘cn’ |-> ‘cnj’] incoming_ready) >>
                gs[]) >>
          ‘Rj files c g (j + 1) = Rj files c g j’
            by (drule_all Rj_Wj_SUC >> gs[ADD1]) >>
          gs[])
      (* after a read: everything has been read *)
      >- (rpt strip_tac >>
          ‘∃hj wj pj. closed_loop (http_server files lfd) (start_world lfd sch)
                        (a + j) = (hj, wj, pj)’ by metis_tac[pair_CASES] >>
          ‘∃h1 w1 p1. closed_loop (http_server files lfd) (start_world lfd sch)
                        (a + j + 1) = (h1, w1, p1)’ by metis_tac[pair_CASES] >>
          qpat_assum ‘∀j hj wj pj. _ ⇒ ∃cnj. _’
            (qspecl_then [‘j’, ‘hj’, ‘wj’, ‘pj’] mp_tac) >>
          impl_tac >- fs[Abbr ‘j0’] >> strip_tac >>
          ‘j ≤ LENGTH g’ by simp[] >>
          drule_all hmachine_reading >> strip_tac >>
          qpat_assum ‘∀j hj wj pj. _ ⇒ Rj _ _ _ _ = _ ∧ _’
            (qspecl_then [‘j’, ‘hj’, ‘wj’, ‘pj’] mp_tac) >>
          impl_tac >- gs[] >> strip_tac >>
          qpat_assum ‘∀j hj wj pj. _ ⇒ Rj _ _ _ _ = _ ∧ _’
            (qspecl_then [‘j + 1’, ‘h1’, ‘w1’, ‘p1’] mp_tac) >>
          impl_tac >- gs[] >> strip_tac >>
          ‘MEM (Read c) (new_actions (log_of (http_server files lfd)) hj)’
            by metis_tac[] >>
          mp_tac (Q.INST [‘k’ |-> ‘a + j : num’, ‘h’ |-> ‘hj’, ‘w’ |-> ‘wj’, ‘p’ |-> ‘pj’,
                          ‘h'’ |-> ‘h1’, ‘w'’ |-> ‘w1’, ‘p'’ |-> ‘p1’, ‘cn’ |-> ‘cnj’]
                    http_round_read) >>
          impl_tac >- gs[] >> strip_tac >>
          qpat_x_assum ‘Rj _ _ _ (j + 1) = _’ (fn th => REWRITE_TAC [ADD1, th]) >>
          metis_tac[])
      (* stopped at end-of-file: everything has been read *)
      >> rpt strip_tac >>
      ‘∃hj wj pj. closed_loop (http_server files lfd) (start_world lfd sch)
                    (a + j) = (hj, wj, pj)’ by metis_tac[pair_CASES] >>
      qpat_assum ‘∀j hj wj pj. _ ⇒ ∃cnj. _’
        (qspecl_then [‘j’, ‘hj’, ‘wj’, ‘pj’] mp_tac) >>
      impl_tac >- fs[Abbr ‘j0’] >> strip_tac >>
      ‘parse_request b ≠ Invalid’ by gs[] >>
      drule_all hmachine_eof >> strip_tac >>
      qpat_assum ‘∀j hj wj pj. _ ⇒ Rj _ _ _ _ = _ ∧ _’
        (qspecl_then [‘j’, ‘hj’, ‘wj’, ‘pj’] mp_tac) >>
      impl_tac >- gs[] >> strip_tac >>
      ‘MEM (Read c, Eof) pj’ by metis_tac[] >>
      mp_tac (Q.INST [‘k’ |-> ‘a + j : num’, ‘h’ |-> ‘hj’, ‘w’ |-> ‘wj’, ‘p’ |-> ‘pj’] http_eof) >>
      impl_tac >- gs[] >> strip_tac >>
      ‘cnj = cn'’ by gs[] >> pop_assum SUBST_ALL_TAC >>
      qpat_x_assum ‘cn'.received = _’ mp_tac >>
      qpat_x_assum ‘cn'.incoming = _’ (fn th => REWRITE_TAC [th, APPEND_NIL]) >>
      strip_tac >> metis_tac[]) >>
  (* the responses are written by round a + j + 1 ≤ N, and stay written *)
  strip_tac >>
  ‘j ≤ LENGTH g ∧ a + j + 1 ≤ N’ by fs[Abbr ‘j0’, Abbr ‘NK’] >>
  ‘∃hj wj pj. closed_loop (http_server files lfd) (start_world lfd sch)
                (a + j) = (hj, wj, pj)’ by metis_tac[pair_CASES] >>
  ‘∃h1 w1 p1. closed_loop (http_server files lfd) (start_world lfd sch)
                (a + j + 1) = (h1, w1, p1)’ by metis_tac[pair_CASES] >>
  qpat_assum ‘∀j hj wj pj. _ ⇒ Rj _ _ _ _ = _ ∧ _’
    (qspecl_then [‘j’, ‘hj’, ‘wj’, ‘pj’] mp_tac) >>
  impl_tac >- gs[] >> strip_tac >>
  ‘Wj files c g j = written c (sperf p1)’ by metis_tac[] >>
  (* c at round N holds what the server has written to it *)
  mp_tac (Q.INST [‘k’ |-> ‘N’, ‘h'’ |-> ‘hN’, ‘w'’ |-> ‘wN’, ‘p'’ |-> ‘pN’]
            http_received_later) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘n + 2 * NK + 3 ≤ N’ mp_tac >> simp[]) >>
  strip_tac >> qexists_tac ‘cn'’ >> simp[] >>
  mp_tac (Q.INST [‘k’ |-> ‘N’, ‘h’ |-> ‘hN’, ‘w’ |-> ‘wN’, ‘p’ |-> ‘pN’, ‘cn’ |-> ‘cn'’]
            http_consistent) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  ‘p1 ≼ pN’ by metis_tac[http_prefix] >>
  qpat_x_assum ‘cn'.outgoing = _’ SUBST1_TAC >> irule IS_PREFIX_TRANS >>
  qexists_tac ‘FLAT (written c (sperf p1))’ >> conj_tac
  >- (irule FLAT_prefix >> qpat_x_assum ‘p1 ≼ pN’ mp_tac >>
      rw[IS_PREFIX_APPEND] >> simp[]) >>
  irule FLAT_prefix >>
  qpat_x_assum ‘Wj _ _ _ _ = written _ _’ (fn th =>
    qpat_x_assum ‘_ ≼ Wj _ _ _ _’ (ACCEPT_TAC o REWRITE_RULE [th]))
QED

(* MAIN: the same, in terms of requests (as in HttpSpec): if the data that
   has arrived on c by round n is the requests rs (valid, complete) followed
   by anything, then by round n + 2K + 3 the responses to rs have been
   written to c. *)
Theorem closed_loop_http_requests:
  closed_loop (http_server files lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ MEM c (accepted (sperf perf)) ∧
  cn.received = FLAT (MAP print_request rs) ++ rest ∧ EVERY valid_request rs ∧
  n + 2 * LENGTH (parse_all cn.received) + 3 ≤ N ∧
  closed_loop (http_server files lfd) (start_world lfd sch) N = (hN, wN, pN) ⇒
  ∃cnN. ALOOKUP wN.conns c = SOME cnN ∧
        FLAT (MAP (print_response o handle files) rs) ≼ cnN.outgoing
Proof
  strip_tac >> drule_all closed_loop_http_accepted >> strip_tac >>
  qexists_tac ‘cnN’ >> simp[] >>
  ‘parse_all cn.received = rs ++ parse_all rest’
    by (qpat_x_assum ‘cn.received = _’ SUBST1_TAC >> simp[parse_all_print]) >>
  irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
  asm_rewrite_tac[MAP_APPEND, FLAT_APPEND] >> simp[]
QED
