(*
  The converse for request/response servers (HTTP, the key-value server):
  their liveness is "for every valid request list rs the client has sent,
  Rel rs of what was written".  From that in the version-1 worlds of the
  bounded version-2 worlds (req_acc_live):
   - each client that sends a valid request is answered, so is accepted,
     so each client that connects is accepted (peerV2Accept);
   - what a client has sent is a longest list of valid requests and a rest
     with no full request (max_parse), and every valid request list sent is
     a prefix of it (parse_le), so one point of the run answers them all;
  which is peerV1ConvRun's acc_live for P x y = ∀rs. … ⇒ Rel rs y.
*)
Theory peerV1ReqConv
Ancestors
  llist ffi semantics socketWorld socketFair EchoSpec lifetimeWorld
  lifetimeFair EchoEpisodesSpec HttpGetSpec HttpSpec peerSpecForms peerServers
  peerEchoEpisodes peerEchoEpisodesConv peerV1Sim peerV1Run peerV1Inst
  peerV1Proj peerV1Conv peerV2Hide peerV2Accept peerV1ConvRun
  peerBufferKv peerBufferHttp
Libs
  preamble

(* ------------------------------------------------------------------------
   Parsing what a client sent
   ------------------------------------------------------------------------ *)

Theorem brequests_CONS[local]:
  brequests (h :: t) = brequests [h] ++ brequests t
Proof
  simp[brequests_def, bytes_def]
QED

Theorem brequests_one_nonempty[local]:
  brequests [r] ≠ []
Proof
  simp[brequests_nil]
QED

(* MAIN: a longest list of valid requests, and a rest with no full request *)
Theorem max_parse:
  ∀x:word8 list.
    ∃rs rest. EVERY valid_brequest rs ∧ x = brequests rs ++ rest ∧ no_full_brequest rest
Proof
  completeInduct_on ‘LENGTH (x:word8 list)’ >> rw[] >>
  Cases_on ‘no_full_brequest x’
  >- (qexistsl_tac [‘[]’, ‘x’] >> simp[brequests_def, bytes_def]) >>
  fs[no_full_brequest_def] >> fs[IS_PREFIX_APPEND] >> rename1 ‘x = brequests [r] ++ x'’ >>
  ‘LENGTH x' < LENGTH x’
    by (‘brequests [r] ≠ []’ by simp[brequests_one_nonempty] >>
        Cases_on ‘brequests [r]’ >> fs[]) >>
  first_x_assum drule >> disch_then (qspec_then ‘x'’ mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [‘r :: rs’, ‘rest’] >> simp[] >>
  simp[brequests_def, bytes_def]
QED

(* The parse is unique *)
Theorem parse_uniq[local]:
  ∀z rs rest. EVERY valid_brequest z ∧ EVERY valid_brequest rs ∧ no_full_brequest rest ∧
              brequests z = brequests rs ++ rest ⇒ z = rs ∧ rest = []
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      ‘brequests rs ++ rest = []’ by (pop_assum (SUBST1_TAC o SYM) >> simp[brequests_def, bytes_def]) >>
      fs[brequests_nil]) >>
  rpt gen_tac >> strip_tac >> Cases_on ‘rs’
  >- (fs[no_full_brequest_def] >>
      first_x_assum (qspec_then ‘h’ mp_tac) >> simp[] >>
      fs[brequests_def, bytes_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  rename1 ‘brequests (h :: z) = brequests (h' :: t) ++ rest’ >>
  qpat_x_assum ‘brequests _ = _’ mp_tac >>
  ONCE_REWRITE_TAC[brequests_CONS] >> REWRITE_TAC[GSYM APPEND_ASSOC] >> strip_tac >>
  ‘h = h'’
    by (‘brequests [h] ≼ brequests [h'] ∨ brequests [h'] ≼ brequests [h]’
          by (irule prefixes_is_prefix_total >> qexists_tac ‘brequests [h] ++ brequests z’ >>
              simp[] >> qpat_x_assum ‘_ ++ _ = _ ++ _’ (fn th => REWRITE_TAC[th]) >>
              REWRITE_TAC[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]) >>
        fs[brequests_def, bytes_prefix_iff] >> metis_tac[print_prefix_free]) >>
  qpat_x_assum ‘h = h'’ SUBST_ALL_TAC >> fs[] >>
  last_x_assum (qspecl_then [‘t’, ‘rest’] mp_tac) >> simp[]
QED

(* MAIN: every valid request list sent is a prefix of the longest *)
Theorem parse_le:
  EVERY valid_brequest rs ∧ no_full_brequest rest ∧ EVERY valid_brequest z ∧
  brequests z ≼ brequests rs ++ rest ⇒ z ≼ rs
Proof
  strip_tac >> drule_all parse_mono >> strip_tac >>
  ‘z = rs'’ by metis_tac[parse_uniq] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The converse
   ------------------------------------------------------------------------ *)

Theorem bytes_written_prefix_mono[local]:
  evs1 ≼ evs2 ⇒ bytes_written_to c evs1 ≼ bytes_written_to c evs2
Proof
  rw[IS_PREFIX_APPEND, bytes_written_to_def] >>
  qexists_tac ‘FLAT (MAP (event_written c) l)’ >> simp[]
QED

Theorem accepted_fds_prefix_mono[local]:
  evs1 ≼ evs2 ⇒ LENGTH (accepted_fds evs1) ≤ LENGTH (accepted_fds evs2)
Proof
  rw[IS_PREFIX_APPEND] >> simp[accepted_fds_def]
QED

(* Per-request liveness in the version-1 world of a version-2 world is
   per-request liveness of the episodes *)
Theorem req_live2[local]:
  (∀rs y y'. Rel rs y ∧ y ≼ y' ⇒ Rel rs y') ∧
  v1_disciplined lfd prog ∧ lifetime_world lfd sk ∧ (∀n. nconn sk n ≤ N) ∧
  LENGTH sk.reserved + N + 3 < dimword (:64) ∧
  semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog (Diverge io) ∧
  (∀c n rs. EVERY valid_brequest rs ∧ brequests rs ≼ sent_upto c n (v1of2 lfd sk) ⇒
            ∃evs. LPREFIX (fromList evs) io ∧ Rel rs (bytes_written_to c evs)) ∧
  j < nconn sk n ∧ EVERY valid_brequest rs ∧ brequests rs ≼ sent2_upto j n sk ⇒
  ∃evs. LPREFIX (fromList evs) io ∧ Rel rs (ep_written j evs) ∧
        ∀evs'. LPREFIX (fromList evs') io ∧ evs ≼ evs' ⇒ Rel rs (ep_written j evs')
Proof
  strip_tac >>
  ‘sent2_upto j n sk = sent_upto (F2 lfd sk j) n (v1of2 lfd sk)’
    by (irule v1of2_sent >> metis_tac[]) >>
  first_x_assum (qspecl_then [‘F2 lfd sk j’, ‘n’, ‘rs’] mp_tac) >> impl_tac >- fs[] >>
  strip_tac >> qexists_tac ‘evs’ >>
  ‘∀evs'. LPREFIX (fromList evs') io ⇒ ep_written j evs' = bytes_written_to (F2 lfd sk j) evs'’
    by (rpt strip_tac >> irule v1of2_written >> metis_tac[]) >>
  simp[] >> metis_tac[bytes_written_prefix_mono]
QED

(* MAIN: per-request liveness, monotone in the requests and in what is
   written, in the version-1 worlds of the bounded version-2 worlds, with a
   valid request r0 that must be answered, gives acc_live *)
Theorem req_acc_live:
  (∀rs rs' y. rs' ≼ rs ∧ Rel rs y ⇒ Rel rs' y) ∧
  (∀rs y y'. Rel rs y ∧ y ≼ y' ⇒ Rel rs y') ∧
  valid_brequest r0 ∧ (∀y. Rel [r0] y ⇒ y ≠ []) ∧ v1_disciplined lfd prog ∧
  (∀sk N. lifetime_world lfd sk ∧ (∀n. nconn sk n ≤ N) ∧
          LENGTH sk.reserved + N + 3 < dimword (:64) ⇒
          ∃io. semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog
                 (Diverge io) ∧ Sf io ∧
               ∀c n rs. EVERY valid_brequest rs ∧ brequests rs ≼ sent_upto c n (v1of2 lfd sk) ⇒
                        ∃evs. LPREFIX (fromList evs) io ∧ Rel rs (bytes_written_to c evs)) ⇒
  ∀sk N. lifetime_world lfd sk ∧ (∀n. nconn sk n ≤ N) ∧
         LENGTH sk.reserved + N + 3 < dimword (:64) ⇒
         ∃io. semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog
                (Diverge io) ∧ Sf io ∧
              acc_live (λx y. ∀rs. EVERY valid_brequest rs ∧ brequests rs ≼ x ⇒ Rel rs y) sk io
Proof
  strip_tac >>
  (* every client that sends r0 is accepted *)
  ‘∀N sk io j n.
     lifetime_world lfd sk ∧ (∀m. nconn sk m ≤ N) ∧ LENGTH sk.reserved + N + 3 < dimword (:64) ∧
     semantics_prog (init_state (lifetime_ffi sk)) init_env prog (Diverge io) ∧
     brequests [r0] ≼ sent2_upto j n sk ⇒
     ∃evs. LPREFIX (fromList evs) io ∧ j < LENGTH (accepted_fds evs)’
    by (rpt strip_tac >>
        last_x_assum (qspecl_then [‘sk’, ‘N’] mp_tac) >> impl_tac >- fs[] >> strip_tac >>
        rename1 ‘semantics_prog (init_state (socket_ffi _)) _ _ (Diverge io1)’ >>
        drule_all v1of2_run >> strip_tac >>
        ‘io1 = io’ by metis_tac[diverge_unique] >> pop_assum SUBST_ALL_TAC >>
        ‘j < nconn sk n’
          by (CCONTR_TAC >>
              ‘sent2_upto j n sk = []’
                by (irule sent2_unconn >> fs[] >> qexists_tac ‘lfd’ >> fs[]) >>
              fs[brequests_one_nonempty]) >>
        ‘EVERY valid_brequest [r0]’ by simp[] >>
        drule_all req_live2 >> strip_tac >>
        qexists_tac ‘evs’ >> simp[] >>
        ‘ep_written j evs ≠ []’
          by (qpat_x_assum ‘∀y. Rel [r0] y ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
        CCONTR_TAC >> fs[ep_written_def]) >>
  rpt strip_tac >>
  last_x_assum (qspecl_then [‘sk’, ‘N’] mp_tac) >> impl_tac >- fs[] >> strip_tac >>
  qexists_tac ‘io’ >> simp[acc_live_def] >> rpt strip_tac >>
  drule_all v1of2_run >> strip_tac >>
  ‘j < nconn sk n’
    by (CCONTR_TAC >>
        ‘sent2_upto j n sk = []’ by (irule sent2_unconn >> fs[] >> qexists_tac ‘lfd’ >> fs[]) >>
        fs[]) >>
  (* the client is accepted *)
  ‘∃evs2. LPREFIX (fromList evs2) io ∧ j < LENGTH (accepted_fds evs2)’
    by (mp_tac (Q.INST [‘bs’ |-> ‘brequests [r0]’] accept_all) >>
        impl_tac
        >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            first_x_assum (qspec_then ‘N’ ACCEPT_TAC)) >>
        simp[]) >>
  (* its longest request list is answered *)
  qspec_then ‘sent2_upto j n sk’ strip_assume_tac max_parse >>
  ‘brequests rs ≼ sent2_upto j n sk’
    by (qpat_x_assum ‘sent2_upto _ _ _ = _’ (fn th => REWRITE_TAC[th]) >> simp[]) >>
  drule_all req_live2 >> strip_tac >>
  rename1 ‘Rel rs (ep_written j evs1)’ >>
  ‘∃evs. LPREFIX (fromList evs) io ∧ evs1 ≼ evs ∧ evs2 ≼ evs’
    by (‘evs1 ≼ evs2 ∨ evs2 ≼ evs1’ by metis_tac[io_prefixes_total] >>
        TRY (qexists_tac ‘evs1’ >> fs[] >> NO_TAC) >> qexists_tac ‘evs2’ >> fs[]) >>
  qexists_tac ‘evs’ >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      ‘rs' ≼ rs’
        by (irule parse_le >> fs[] >> qexists_tac ‘rest’ >> fs[]) >>
      ‘Rel rs (ep_written j evs)’ by (first_x_assum irule >> simp[]) >>
      qpat_x_assum ‘∀rs rs' y. rs' ≼ rs ∧ _ ⇒ _’ irule >> qexists_tac ‘rs’ >> simp[]) >>
  ‘LENGTH (accepted_fds evs2) ≤ LENGTH (accepted_fds evs)’ by simp[accepted_fds_prefix_mono] >>
  decide_tac
QED
