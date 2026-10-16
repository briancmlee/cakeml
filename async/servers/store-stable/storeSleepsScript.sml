(*
  The store server goes to sleep (design/37, step D, model side): R1's
  loop (loopInterestBusy) running the Level 2 store server with query handlers
  blocks forever in select, in a world where finitely many things arrive.

  - rd2: a Level 2 computation waits only for Readable events; the
    skeleton with query handlers does (rd2_server_v2), so the store
    server waits for Always only while a query is pending;
  - quiet_nb_with_store2: with_store2 Always is quiet while not busy
    (withStore2's quiet_with_store2_np);
  - store_sleeps: qsel_sleepsB under store_stable's three facts.

  MAIN: store_sleeps.
*)
Theory storeSleeps
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncLevel2 asyncLoop2 asyncTranscript echoServer
  echoServerSafety asyncSched2 socketWorld socketFair
  loopPollWorld loopRounds loopRoundsTrans loopPollDyn loopSelectWorld
  loopSelectSet relabel relabelDist echoSockModel
  quietRounds skeletonV protoV proto2 relabel2
  loopInterestFinite loopInterestSel withStore withStore2 skeletonVKv
  stableGen storeSafe storeStable loopInterestBusy QuietSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   Waiting only for Readable events
   ------------------------------------------------------------------------ *)

Definition rd2_def:
  rd2 c ⇔ ∀h e. e ∈ c.interest h ⇒ ∃x. e = Readable x
End

Theorem rd2_return2:
  rd2 (return2 x)
Proof
  simp[rd2_def, return2_def]
QED

Theorem rd2_emit2:
  rd2 (emit2 a)
Proof
  simp[rd2_def, emit2_def]
QED

Theorem rd2_wait_on:
  rd2 (wait_on (Readable n) p)
Proof
  simp[rd2_def, wait_on_def]
QED

Theorem rd2_map2:
  rd2 c ⇒ rd2 (map2 f c)
Proof
  simp[rd2_def, map2_def]
QED

Theorem rd2_bind2:
  rd2 c ∧ (∀x. rd2 (f x)) ⇒ rd2 (bind2 c f)
Proof
  rw[rd2_def, bind2_def, bind_interest_def] >> every_case_tac >> gvs[] >>
  metis_tac[]
QED

Theorem rd2_both2:
  rd2 c1 ∧ rd2 c2 ⇒ rd2 (both2 c1 c2)
Proof
  rw[rd2_def, both2_def, waiting_on_def] >> every_case_tac >> gvs[] >>
  metis_tac[]
QED

Theorem rd2_fix2:
  contractive2 body2 ∧ (∀R. (∀p. rd2 (R p)) ⇒ ∀p. rd2 (body2 R p)) ⇒
  ∀p. rd2 (fix2 body2 p)
Proof
  rw[contractive2_lift, fix2_def]
  >> ‘∀p. (λF. rd2 (unpack F)) (fix (lift_body body2) p)’ suffices_by simp[]
  >> irule fix_preserves >> simp[]
  >> rpt conj_tac
  >> TRY (rw[closed_def, rd2_def, unpack_def] >>
          first_x_assum (qspec_then ‘LENGTH h + 1’ strip_assume_tac) >>
          gvs[agree_below_def, rd2_def, unpack_def] >> metis_tac[])
  >- (qexists_tac ‘pack never2’ >> simp[rd2_def, never2_def])
  >> simp[lift_body_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem rd2_proto_handler_v2:
  ∀p. rd2 (proto_handler_v2 V P ansq fin p)
Proof
  simp[proto_handler_v2_def] >> irule rd2_fix2 >>
  simp[proto_body_v2_contractive] >> rw[] >>
  PairCases_on ‘p’ >> simp[proto_body_v2_def] >> CASE_TAC >>
  simp[rd2_return2]
  >- (CASE_TAC >> irule rd2_bind2 >> simp[rd2_emit2] >> rw[] >>
      irule rd2_bind2 >> simp[rd2_emit2])
  >> irule rd2_bind2 >> simp[rd2_wait_on] >> rw[] >>
  irule rd2_bind2 >> simp[rd2_emit2] >> rw[] >>
  rpt CASE_TAC >> simp[rd2_return2]
QED

Theorem rd2_server_v2:
  (∀fd. rd2 (h2 fd)) ⇒ rd2 (server_v2 V h2 lfd)
Proof
  strip_tac >> simp[server_v2_def] >> qid_spec_tac ‘lfd’ >> irule rd2_fix2 >>
  simp[server_v_body2_contractive] >> rw[server_v_body2_def] >>
  irule rd2_bind2 >> simp[rd2_wait_on] >> rw[] >>
  irule rd2_bind2 >> simp[rd2_emit2] >> rw[] >> CASE_TAC >> simp[] >>
  irule rd2_map2 >> irule rd2_both2 >> simp[]
QED

(* ------------------------------------------------------------------------
   The store server, at Level 2
   ------------------------------------------------------------------------ *)

(* Busy exactly while a query is pending *)
Theorem with_store2_busy:
  rd2 c ⇒
  (busy (with_store2 Always δ st c) h ⇔
   ((with_store2 Always δ st c).run h).result = NONE ∧ kv_pending δ st c.run h)
Proof
  rw[rd2_def, waiting_on_def, with_store2_def] >> rw[] >>
  strip_tac >> res_tac >> fs[]
QED

(* MAIN: with_store2 Always is quiet while not busy *)
Theorem quiet_nb_with_store2:
  wf c.run ∧ quiet c ∧ rd2 c ⇒ quiet_nb (with_store2 Always δ st c)
Proof
  strip_tac >> REWRITE_TAC[quiet_nb_def] >> rpt gen_tac >> strip_tac >>
  irule quiet_with_store2_np >> simp[] >>
  qpat_x_assum ‘¬busy _ _’ mp_tac >> simp[with_store2_busy]
QED

(* ------------------------------------------------------------------------
   Going to sleep
   ------------------------------------------------------------------------ *)

Theorem server_v2_run[local]:
  (∀fd. (h2 fd).run = hf fd) ⇒ (server_v2 V h2 lfd).run = server_v V hf lfd
Proof
  strip_tac >>
  ‘∀fd. erase (h2 fd) = hf fd’ by simp[erase_def] >>
  drule erase_server_v2 >> simp[erase_def]
QED

(* The Level 2 store server's run is the store server *)
Theorem SM2_run:
  (SM2 δ st P ansq fin lfdn).run = SM δ st P ansq fin lfdn
Proof
  simp[with_store2_def] >> AP_TERM_TAC >> irule server_v2_run >>
  simp[GSYM erase_def, erase_proto_handler_v2]
QED

(* MAIN (Q2 for stateful servers): R1's loop running the Level 2 store
   server with query handlers, in a world where finitely many things
   arrive, blocks forever in select: nothing to do, no query pending,
   nothing it waits for ever ready *)
Theorem store_sleeps:
  proto_ok P ∧ (∀fd req q. ansq fd req = SOME q ⇒ FST q = fd) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃n kept N s.
    lbgroundsB (SM2 δ st P ansq fin lfdn) [n2w lfdn] s0 n = SOME (kept, N, s) ∧
    new_actions (log_of (srelabel (SM2 δ st P ansq fin lfdn).run)) kept = [] ∧
    ¬busy (SM2 δ st P ansq fin lfdn) (MAP sfs kept) ∧
    sock_wait (qsel (srelabel2 (SM2 δ st P ansq fin lfdn)) kept) s = NONE
Proof
  strip_tac >>
  qabbrev_tac ‘C2 = server_v2 sockV (λfd. proto_handler_v2 sockV P (ansq fd) (fin fd) (fd, "")) lfdn’ >>
  ‘C2.run = server_v sockV (HQ P ansq fin) lfdn’
    by (simp[Abbr ‘C2’] >> irule server_v2_run >>
        simp[GSYM erase_def, erase_proto_handler_v2]) >>
  ‘wf2 C2’ by (simp[Abbr ‘C2’] >> irule wf2_server_v2 >> simp[wf2_proto_handler_v2]) >>
  ‘rd2 C2’ by (simp[Abbr ‘C2’] >> irule rd2_server_v2 >> simp[rd2_proto_handler_v2]) >>
  ‘finite2 C2’
    by (simp[Abbr ‘C2’] >> irule finite2_server_v2 >> simp[finite2_proto_handler_v2]) >>
  ‘(SM2 δ st P ansq fin lfdn) = with_store2 Always δ st C2’ by simp[Abbr ‘C2’] >>
  pop_assum SUBST1_TAC >>
  irule qsel_sleepsB >> rpt conj_tac
  (* wf, quiet while not busy, finitely many events *)
  >> TRY (‘wf C2.run’ by fs[wf2_def] >>
          ‘(with_store2 Always δ st C2).run = with_store δ st C2.run’
            by simp[with_store2_def] >>
          pop_assum SUBST1_TAC >> match_mp_tac wf_with_store >>
          first_assum ACCEPT_TAC)
  >> TRY (irule quiet_nb_with_store2 >> fs[wf2_def] >> NO_TAC)
  >> TRY (fs[finite2_def] >> irule finite_with_store2 >> simp[] >> NO_TAC)
  (* the world is static after some round *)
  >> TRY (qspecl_then [‘s0’, ‘EI lfdn’, ‘srelabel (SM δ st P ansq fin lfdn)’]
            mp_tac (Q.GENL [‘s0’, ‘ifds’, ‘m’] static_after) >>
          simp[with_store2_def, Abbr ‘C2’] >> NO_TAC)
  (* store_stable's three facts *)
  >> drule_all_then (Q.ISPECL_THEN [‘δ’, ‘st’, ‘fin’] strip_assume_tac) store_stable >>
  qexists_tac ‘n1’ >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  ‘(with_store2 Always δ st C2).run = SM δ st P ansq fin lfdn’
    by simp[with_store2_def] >>
  simp[] >> strip_tac >> rpt conj_tac
  >- (simp[with_store2_busy] >> strip_tac >> fs[])
  >> rpt strip_tac >>
  gvs[waiting_on_srelabel2, sie_def] >>
  first_x_assum drule >> simp[]
QED
