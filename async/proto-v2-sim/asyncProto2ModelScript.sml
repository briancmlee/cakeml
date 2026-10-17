(*
  The generic protocol server, run by the handle-layer loop in a fair
  version-2 server world, meets the generic version-2 spec, for every
  protocol with proto_ok (proto2_model):

     its trace is safe and live per episode, and closes every episode
     whose client's EOF it has read.

  As asyncHLEchoSpec2 for echo.  First, for any server m that uses only
  handed-out connections and ends each connection's transcript at its EOF:
  episode j's bytes at the end of each round are the version-1 loop's
  bytes on handle j in the renamed world (ep_rounds_gen), and every
  episode whose EOF was read is closed (gen_closes2).  Then, for the
  protocol server: safety from the version-1 loop's round-level safety
  (proto_rounds_safe), liveness from proto_live_rounds.
*)
Theory asyncProto2Model
Ancestors
  llist alist words ffi ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4Loop asyncM4SockInv asyncM4SockModel
  asyncRunOkGen EchoSpec EchoSpec2 HttpSpec socketV2FFI socketV2Fair
  asyncHLFair asyncHLModel asyncHLSimWorld asyncHLSimTick asyncHLSimOps
  asyncHLSimRun asyncHLEpisodes asyncHLSimEvents asyncHLSimTrace
  asyncHLEchoSpec2 asyncProto asyncProtoServer asyncProtoSafe asyncProtoLive
  asyncProtoEof asyncHLEofGen asyncHLSimRunGen asyncHLSimTraceGen asyncProto2
Libs
  preamble

Overload Rg2[local] = “λm lfdn s2. hround_events (n2w lfdn) (interest [n2w lfdn : word64])
                                   (srelabel m) s2”
Overload Rg1[local] = “λm lfdn s2. grounds_events (interest [n2w lfdn : word64])
                                   (srelabel m) (v1of (n2w lfdn) s2)”
Overload gtrace2 = “λm lfdn s2. LFLATTEN (LGENLIST
                      (λi. fromList (hround_events (n2w lfdn)
                                       (interest [n2w lfdn : word64]) (srelabel m) s2 i))
                      NONE)”

(* ------------------------------------------------------------------------
   Any server that uses handed-out connections and stops at EOF
   ------------------------------------------------------------------------ *)

Theorem accepted_bound_gen:
  uses_ok lfdn m ∧ srv_eof_last m ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. LENGTH (accepted_fds (FLAT (GENLIST (Rg2 m lfdn s2) n))) < dimword (:64) − 1
Proof
  rpt strip_tac >>
  drule_all hrun_events_gen >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_all hrun_sim_gen >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qspecl_then [‘FLAT (GENLIST (Rg2 m lfdn s2) n)’, ‘0’, ‘[]’] mp_tac ep_st_count >>
  qpat_x_assum ‘ep_st _ _ _ = _’ (fn th => REWRITE_TAC[th]) >> simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  Cases_on ‘hst (n2w lfdn) (interest [n2w lfdn]) (srelabel m) s2 n’ >>
  rename1 ‘_ = (sk, hk)’ >> fs[hsim_def] >>
  ‘hk.nxt ≤ LENGTH sk.clients’ by fs[hsim0_def] >>
  Cases_on ‘sk.clients = []’ >> fs[] >>
  drule_all hsim0_bound >> simp[]
QED

(* MAIN: at the end of every round, what episode j read and wrote is what
   the version-1 loop read from and wrote to handle j *)
Theorem ep_rounds_gen:
  uses_ok lfdn m ∧ srv_eof_last m ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ j < dimword (:64) − 1 ⇒
  ep_read j (FLAT (GENLIST (Rg2 m lfdn s2) n)) =
    bytes_read_from (hdl (n2w lfdn) j) (FLAT (GENLIST (Rg1 m lfdn s2) n)) ∧
  ep_written j (FLAT (GENLIST (Rg2 m lfdn s2) n)) =
    bytes_written_to (hdl (n2w lfdn) j) (FLAT (GENLIST (Rg1 m lfdn s2) n))
Proof
  strip_tac >>
  drule_all accepted_bound_gen >> disch_then (qspec_then ‘n’ assume_tac) >>
  drule_all hrun_events_gen >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  conj_tac
  >- (qspecl_then [‘dimword (:64) − 1’, ‘n2w lfdn’, ‘FLAT (GENLIST (Rg2 m lfdn s2) n)’, ‘j’]
        mp_tac (Q.GENL [‘N’, ‘lfd’, ‘evs’, ‘j’] ep_read_rn) >>
      simp[hdl_inj] >> impl_tac >- fs[] >> fs[])
  >> qspecl_then [‘dimword (:64) − 1’, ‘n2w lfdn’, ‘FLAT (GENLIST (Rg2 m lfdn s2) n)’, ‘j’]
       mp_tac (Q.GENL [‘N’, ‘lfd’, ‘evs’, ‘j’] ep_written_rn) >>
  simp[hdl_inj] >> impl_tac >- fs[] >> fs[]
QED

Theorem Rg2_nonempty[local]:
  Rg2 m lfdn s2 i ≠ []
Proof
  simp[hround_events_alt] >> rpt (pairarg_tac >> simp[])
QED

(* MAIN: every episode whose client's EOF was read is closed (for any m:
   the handle layer closes on EOF) *)
Theorem gen_closes2:
  echo_closes2 (gtrace2 m lfdn s2)
Proof
  rw[echo_closes2_def] >>
  ‘∀i. Rg2 m lfdn s2 i ≠ []’ by simp[Rg2_nonempty] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  qexists_tac ‘FLAT (GENLIST (Rg2 m lfdn s2) (SUC n))’ >> simp[rounds_LPREFIX] >>
  qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
  gvs[ep_eof_read_def, ep_closed_def, accepted_fds_APPEND, EL_APPEND1] >>
  qmatch_goalsub_abbrev_tac ‘EL j A’ >>
  ‘eof_then_close (evs ++ l)’
    by (qpat_x_assum ‘_ = evs ++ l’ (SUBST1_TAC o SYM) >>
        simp[hround_events_eof_then_close]) >>
  irule ep_eof_closes >> simp[ep_events_APPEND] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   Strings and bytes (as in asyncProtoSafe, where these are local)
   ------------------------------------------------------------------------ *)

Theorem chars_of_bytes[local]:
  MAP ((n2w : num -> word8) o ORD) (MAP (CHR o w2n) (bs : word8 list)) = bs
Proof
  simp[bytes_round_trip]
QED

Theorem bytes_split[local]:
  ∀p s rest. MAP ((n2w : num -> word8) o ORD) s = MAP (n2w o ORD) p ++ rest ⇒
             ∃s'. s = p ++ s' ∧ MAP (n2w o ORD) s' = rest
Proof
  Induct >> simp[] >> rpt strip_tac >> Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem bytes_prefix[local]:
  ∀s t. MAP ((n2w : num -> word8) o ORD) s ≼ MAP (n2w o ORD) t ⇔ s ≼ t
Proof
  Induct >> Cases_on ‘t’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >>
  simp[] >> metis_tac[ORD_11]
QED

Theorem prefix_FLAT[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ FLAT l1 ≼ FLAT l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem prefix_MAP[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ MAP f l1 ≼ MAP f l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem read_requests_parse[local]:
  proto_ok P ∧
  MAP ((n2w : num -> word8) o ORD) s = preqs P rs ++ rest ∧
  EVERY P.valid rs ∧ no_full P rest ⇒
  proto_all P s = rs
Proof
  rw[preqs_def, bytes_def] >> drule bytes_split >> strip_tac >> gvs[] >>
  irule proto_all_requests >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[no_full_def] >> first_x_assum drule >>
  simp[preqs_def, bytes_def, IS_PREFIX_APPEND]
QED

Theorem presps_prefix[local]:
  l1 ≼ l2 ⇒ presps resp l1 ≼ presps resp l2
Proof
  rw[presps_def, bytes_def] >> irule prefix_MAP >> irule prefix_FLAT >>
  irule prefix_MAP >> simp[]
QED

(* ------------------------------------------------------------------------
   The protocol server
   ------------------------------------------------------------------------ *)

(* MAIN (version 1, per round): what the protocol server has written on c
   by the end of round n + 1 is a prefix of the responses to the complete
   requests it had read on c by the end of round n *)
Theorem proto_rounds_safe:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  bytes_written_to c
    (FLAT (GENLIST (grounds_events ifds (srelabel (proto_server P resp lfdn)) s0) (SUC n))) ≼
  presps resp (proto_all P (MAP (CHR o w2n)
    (bytes_read_from c
       (FLAT (GENLIST (grounds_events ifds (srelabel (proto_server P resp lfdn)) s0) n)))))
Proof
  strip_tac >>
  ‘uses_ok lfdn (proto_server P resp lfdn)’
    by simp[uses_ok_def, proto_server_uses_accepted] >>
  drule_all gen_rounds_bytes >>
  disch_then (qspecl_then [‘n’, ‘ifds’, ‘c’] strip_assume_tac) >>
  ‘fresh (trans (proto_server P resp lfdn)
           (MAP sfs (ghist ifds (srelabel (proto_server P resp lfdn)) s0 n)))’
    by metis_tac[gen_fresh] >>
  drule_all proto_server_safety >> disch_then (qspec_then ‘w2n c’ assume_tac) >>
  qabbrev_tac ‘TT = trans (proto_server P resp lfdn)
                      (MAP sfs (ghist ifds (srelabel (proto_server P resp lfdn)) s0 n))’ >>
  simp[] >>
  simp[presps_def, bytes_def, bytes_prefix] >>
  irule prefix_FLAT >>
  ‘MAP (CHR o w2n) (MAP ((n2w : num -> word8) o ORD) (FLAT (read (w2n c) TT))) =
   FLAT (read (w2n c) TT)’
    by simp[MAP_MAP_o, combinTheory.o_DEF, ORD_BOUND, CHR_ORD, MAP_ID] >>
  pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC
QED

(* MAIN: safety, per episode *)
Theorem proto2_safe:
  proto_ok P ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  proto_safe2 P resp (gtrace2 (proto_server P resp lfdn) lfdn s2)
Proof
  rw[proto_safe2_def] >>
  ‘uses_ok lfdn (proto_server P resp lfdn) ∧ srv_eof_last (proto_server P resp lfdn)’
    by simp[uses_ok_def, proto_server_uses_accepted, proto_server_eof_last] >>
  ‘∀i. Rg2 (proto_server P resp lfdn) lfdn s2 i ≠ []’ by simp[Rg2_nonempty] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  reverse (Cases_on ‘j < LENGTH (accepted_fds evs)’) >- simp[ep_written_def] >>
  ‘LENGTH (accepted_fds evs) ≤
   LENGTH (accepted_fds (FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) (SUC n))))’
    by (qpat_x_assum ‘evs ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >>
        simp[accepted_fds_APPEND]) >>
  ‘LENGTH (accepted_fds (FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) (SUC n)))) <
   dimword (:64) − 1’ by metis_tac[accepted_bound_gen] >>
  ‘j < dimword (:64) − 1’ by fs[] >>
  ‘∀k. ep_read j (FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) k)) =
         bytes_read_from (hdl (n2w lfdn) j)
           (FLAT (GENLIST (Rg1 (proto_server P resp lfdn) lfdn s2) k)) ∧
       ep_written j (FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) k)) =
         bytes_written_to (hdl (n2w lfdn) j)
           (FLAT (GENLIST (Rg1 (proto_server P resp lfdn) lfdn s2) k))’
    by metis_tac[ep_rounds_gen] >>
  ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
    by simp[v1of_def] >>
  qspecl_then [‘P’, ‘v1of (n2w lfdn) s2’, ‘lfdn’, ‘resp’, ‘hdl (n2w lfdn) j’, ‘n’,
               ‘interest [n2w lfdn]’] mp_tac
    (Q.GENL [‘P’, ‘s0’, ‘lfdn’, ‘resp’, ‘c’, ‘n’, ‘ifds’] proto_rounds_safe) >>
  impl_tac >- simp[] >> strip_tac >>
  (* the chain *)
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘ep_written j (FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) (SUC n)))’ >>
  reverse conj_tac >- metis_tac[ep_written_mono] >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘presps resp (proto_all P (MAP (CHR o w2n)
                 (ep_read j (FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) n)))))’ >>
  reverse conj_tac >- metis_tac[] >>
  irule presps_prefix >>
  ‘proto_all P (MAP (CHR o w2n) (ep_read j evs)) = rs’
    by (irule read_requests_parse >> simp[chars_of_bytes]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule proto_all_prefix >> simp[] >>
  qpat_x_assum ‘ep_read j evs = _’ (fn th => REWRITE_TAC[GSYM MAP_APPEND, GSYM th]) >>
  qpat_x_assum ‘∀k. _’ (qspec_then ‘n’ (fn th => REWRITE_TAC[GSYM (CONJUNCT1 th)])) >>
  irule prefix_MAP >> irule ep_read_mono >> first_assum ACCEPT_TAC
QED

(* MAIN: liveness, per client *)
Theorem proto2_live:
  proto_ok P ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  proto_live2 P resp s2 (gtrace2 (proto_server P resp lfdn) lfdn s2)
Proof
  rw[proto_live2_def] >>
  ‘uses_ok lfdn (proto_server P resp lfdn) ∧ srv_eof_last (proto_server P resp lfdn)’
    by simp[uses_ok_def, proto_server_uses_accepted, proto_server_eof_last] >>
  Cases_on ‘rs = []’
  >- (qexists_tac ‘[]’ >> simp[LPREFIX_def, from_toList, presps_def, bytes_def] >>
      CASE_TAC) >>
  ‘preqs P rs ≠ []’
    by (Cases_on ‘rs’ >> fs[preqs_def, bytes_def] >> metis_tac[proto_nonempty]) >>
  ‘sent2_upto j n s2 ≠ []’ by (strip_tac >> fs[]) >>
  ‘j < dimword (:64) − 1’
    by (drule_all hsim_init >> strip_tac >>
        mp_tac (Q.SPECL [‘n’, ‘v1of (n2w lfdn) s2’, ‘s2’, ‘hinit’]
                 (Q.INST [‘lfd’ |-> ‘n2w lfdn’] data_bound)) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
        gvs[sent2_upto_def, FLAT_EQ_NIL, EVERY_MEM, MEM_MAP] >>
        rename1 ‘MEM y (arrivals2_upto _ _)’ >> Cases_on ‘y’ >> gvs[] >>
        Cases_on ‘n' = j’ >> gvs[] >> res_tac) >>
  ‘sent2_upto j n s2 = sent_upto (hdl (n2w lfdn) j) n (v1of (n2w lfdn) s2)’
    by metis_tac[sent2_rn] >>
  ‘sched_wf (v1of (n2w lfdn) s2)’ by metis_tac[v1of_sched_wf] >>
  ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
    by simp[v1of_def] >>
  ‘proto_live P resp (v1of (n2w lfdn) s2)
     (LFLATTEN (LGENLIST (λi. fromList (Rg1 (proto_server P resp lfdn) lfdn s2 i)) NONE))’
    by (irule proto_live_rounds >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
  pop_assum (qspecl_then [‘hdl (n2w lfdn) j’, ‘n’, ‘rs’] mp_tac o REWRITE_RULE [proto_live_def]) >>
  impl_tac >- fs[] >> strip_tac >>
  ‘∀i. Rg1 (proto_server P resp lfdn) lfdn s2 i ≠ []’ by simp[grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  qexists_tac ‘FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) (SUC n'))’ >>
  simp[rounds_LPREFIX] >>
  ‘ep_written j (FLAT (GENLIST (Rg2 (proto_server P resp lfdn) lfdn s2) (SUC n'))) =
   bytes_written_to (hdl (n2w lfdn) j)
     (FLAT (GENLIST (Rg1 (proto_server P resp lfdn) lfdn s2) (SUC n')))’
    by metis_tac[ep_rounds_gen] >>
  pop_assum SUBST1_TAC >>
  irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
  irule bytes_written_to_mono >> first_assum ACCEPT_TAC
QED

(* MAIN: the model result, for every protocol *)
Theorem proto2_model:
  proto_ok P ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  proto_safe2 P resp (gtrace2 (proto_server P resp lfdn) lfdn s2) ∧
  proto_live2 P resp s2 (gtrace2 (proto_server P resp lfdn) lfdn s2) ∧
  echo_closes2 (gtrace2 (proto_server P resp lfdn) lfdn s2)
Proof
  simp[proto2_safe, proto2_live, gen_closes2]
QED
