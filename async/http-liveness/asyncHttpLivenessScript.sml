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
