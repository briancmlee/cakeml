(*
  The key-value server in the async model:

     kv_server lfd = with_store kv_delta (λk. NONE)
                       (server_with_k (λfd. kv_handler (fd, "")) lfd)

  The connections' handlers (asyncKvHandler) share one store through
  with_store (asyncWithStore); the store's step is HttpKvSpec's kv_step.

  MAIN:
   - kv_server_uses_ok: outside the store, the server uses the socket API
     correctly (so asyncRunOkGen's trace bridge applies);
   - kv_server_serves: on any history, on every connection fd,
       * fd's queries, in the global order of all queries, are a prefix of
         the requests in what the server has read from fd, and
       * what the server has written to fd is a prefix of the printed
         answers that running the store over ALL queries so far gives to
         fd's queries.
     This is linearizability in the model: the global query order is the
     order in which with_store answered them.
*)
Theory asyncKvModel
Ancestors
  pair list rich_list arithmetic option string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncRunOkGen asyncWithStore
  asyncServerWithK asyncKvHandler
  HttpSpec HttpSpecHeaders HttpSpecBodies HttpKvSpec asyncHttpParse
  asyncHttpParseH asyncHttpParseB
Libs
  BasicProvers

Definition kv_delta_def:
  kv_delta (st : store) (q : num # brequest) = kv_step st (SND q)
End

Definition kv_inner_def:
  kv_inner lfd = server_with_k (λfd. kv_handler (fd, "")) lfd
End

Definition kv_server_def:
  kv_server lfd = with_store kv_delta (λk. NONE) (kv_inner lfd)
End

(* All the queries of the handlers so far, in the order the store answered
   them *)
Definition kv_queries_def:
  kv_queries lfd hh =
    queries ((kv_inner lfd) (inner_hist kv_delta (λk. NONE) (kv_inner lfd) hh)).actions
End

(* The answers that running the store over the queries G gives to fd's *)
Definition fd_answers_def:
  fd_answers fd G =
    MAP SND (FILTER (λp. FST (FST p) = fd)
                    (ZIP (G, FST (run_store kv_delta (λk. NONE) G))))
End

Theorem wf_kv_inner:
  wf (kv_inner lfd)
Proof
  simp[kv_inner_def] >> irule wf_server_with_k >> simp[wf_kv_handler]
QED

Theorem wf_kv_server:
  wf (kv_server lfd)
Proof
  simp[kv_server_def] >> irule wf_with_store >> simp[wf_kv_inner]
QED

Theorem kv_handler_on_fdk[local]:
  ∀fd hh. EVERY (on_fdk fd) (trans ((λfd. kv_handler (fd, "")) fd) hh)
Proof
  simp[kv_handler_serves]
QED

(* MAIN: outside the store, the server uses the socket API correctly *)
Theorem kv_server_uses_ok:
  uses_ok lfd (kv_server lfd)
Proof
  simp[uses_ok_def, kv_server_def, trans_with_store, wf_kv_inner] >>
  simp[kv_inner_def] >> gen_tac >>
  irule server_with_k_uses_accepted >> simp[kv_handler_serves]
QED

(* The queries of a shorter history are a prefix *)
Theorem kv_queries_TAKE:
  kv_queries lfd (TAKE n hh) ≼ kv_queries lfd hh
Proof
  simp[kv_queries_def, inner_hist_TAKE] >>
  ‘((kv_inner lfd) (TAKE n (inner_hist kv_delta (λk. NONE) (kv_inner lfd) hh))).actions ≼
   ((kv_inner lfd) (inner_hist kv_delta (λk. NONE) (kv_inner lfd) hh)).actions’
    by (irule wf_actions_grow >> simp[wf_kv_inner, IS_PREFIX_APPEND] >>
        metis_tac[TAKE_DROP]) >>
  gvs[IS_PREFIX_APPEND]
QED

(* ------------------------------------------------------------------------
   Filtering by connection
   ------------------------------------------------------------------------ *)

Theorem kvs_FILTER_on_fdk[local]:
  ∀tr. kvs (FILTER (on_fdk fd) tr) = FILTER (λe. FST (FST e) = fd) (kvs tr)
Proof
  Induct >> simp[kvs_def] >> PairCases >> Cases_on ‘h0’ >>
  rw[on_fdk_def] >> gvs[GSYM kvs_def] >> simp[kvs_def]
QED

Theorem untag_FILTER_on_fdk[local]:
  ∀tr. untag (FILTER (on_fdk fd) tr) = FILTER (on_fd fd) (untag tr)
Proof
  Induct >> simp[untag_def] >> PairCases >> Cases_on ‘h0’ >>
  rw[on_fdk_def] >> gvs[GSYM untag_def, on_fd_def] >> simp[untag_def] >>
  gvs[on_fd_def]
QED

Theorem readk_FILTER_on_fdk[local]:
  readk fd (FILTER (on_fdk fd) tr) = read fd (untag tr)
Proof
  simp[readk_def, untag_FILTER_on_fdk, read_FILTER]
QED

Theorem writtenk_FILTER_on_fdk[local]:
  writtenk fd (FILTER (on_fdk fd) tr) = written fd (untag tr)
Proof
  simp[writtenk_def, untag_FILTER_on_fdk, written_FILTER]
QED

(* The answers got by a connection are those of the store at their
   positions *)
Theorem got_FILTER_fits[local]:
  ∀E A. fits A E ∧ LENGTH E = LENGTH A ⇒
        got (FILTER (λe. P (FST e)) E) ≼
        MAP SND (FILTER (λp. P (FST p)) (ZIP (MAP FST E, A)))
Proof
  Induct >> simp[got_def] >> rpt gen_tac >> Cases_on ‘A’ >> simp[] >>
  strip_tac >> gvs[fits_CONS] >> PairCases_on ‘h’ >> gvs[] >>
  rw[got_def] >> first_x_assum drule >> simp[]
QED

Theorem prefix_MAP[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ MAP f l1 ≼ MAP f l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

(* MAIN: the server, on any history whose connections are distinct *)
Theorem kv_server_serves:
  fresh (trans (kv_server lfd) hh) ⇒
  ∀fd. MAP SND (FILTER (λq. FST q = fd) (kv_queries lfd hh)) ≼
         parse_all_b (FLAT (read fd (trans (kv_server lfd) hh))) ∧
       written fd (trans (kv_server lfd) hh) ≼
         MAP print_response (fd_answers fd (kv_queries lfd hh))
Proof
  simp[kv_server_def, trans_with_store, wf_kv_inner] >>
  qabbrev_tac ‘ih = inner_hist kv_delta (λk. NONE) (kv_inner lfd) hh’ >>
  qabbrev_tac ‘T0 = trans (kv_inner lfd) ih’ >>
  strip_tac >> gen_tac >>
  ‘freshk T0’ by simp[freshk_untag] >>
  qspecl_then [‘kv_delta’, ‘λk. NONE’, ‘kv_inner lfd’, ‘hh’] mp_tac
    (Q.GENL [‘δ’, ‘s0’, ‘m’, ‘h’] kv_answers) >>
  simp[wf_kv_inner] >> strip_tac >>
  ‘MAP FST (kvs T0) = kv_queries lfd hh’ by simp[kv_queries_def, Abbr ‘T0’] >>
  ‘fits (FST (run_store kv_delta (λk. NONE) (kv_queries lfd hh))) (kvs T0) ∧
   LENGTH (kvs T0) = LENGTH (FST (run_store kv_delta (λk. NONE) (kv_queries lfd hh)))’
    by (simp[fits_def] >> conj_tac >- metis_tac[LENGTH_MAP] >>
        gvs[] >> metis_tac[LENGTH_MAP]) >>
  ‘FILTER (λq. FST q = fd) (kv_queries lfd hh) =
   MAP FST (kvs (FILTER (on_fdk fd) T0))’
    by (qpat_x_assum ‘MAP FST (kvs T0) = _’ (SUBST1_TAC o SYM) >>
        simp[kvs_FILTER_on_fdk, MAP_FILTER_FST] >>
        simp[FILTER_MAP, combinTheory.o_DEF]) >>
  qspecl_then [‘λfd. kv_handler (fd, "")’, ‘lfd’] mp_tac
    (Q.GENL [‘h’, ‘lfd’] server_with_k_isolates) >>
  impl_tac >- simp[kv_handler_serves] >>
  disch_then (qspec_then ‘ih’ mp_tac) >>
  simp[GSYM kv_inner_def] >> strip_tac >>
  first_x_assum (qspec_then ‘fd’ strip_assume_tac) >>
  qpat_x_assum ‘∀fd. EXISTS _ _ ⇒ _’ kall_tac
  >- (‘written fd (untag T0) = []’
        by metis_tac[writtenk_FILTER_on_fdk, readk_writtenk_simps] >>
      gvs[]) >>
  qspecl_then [‘fd’, ‘L’, ‘""’] mp_tac
    (Q.GENL [‘fd’, ‘hh’, ‘buf’] kv_handler_serves) >>
  qpat_x_assum ‘FILTER (on_fdk fd) T0 = _’ (assume_tac o SYM) >>
  simp[] >> strip_tac >>
  ‘queries (MAP FST (FILTER (on_fdk fd) T0)) = MAP FST (kvs (FILTER (on_fdk fd) T0))’
    by simp[MAP_FST_kvs] >>
  gvs[readk_FILTER_on_fdk, writtenk_FILTER_on_fdk] >>
  irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
  simp[fd_answers_def] >> irule prefix_MAP >>
  simp[kvs_FILTER_on_fdk] >>
  qspecl_then [‘kvs T0’, ‘FST (run_store kv_delta (λk. NONE) (kv_queries lfd hh))’]
    mp_tac (Q.GENL [‘E’, ‘A’] (INST [“P : num # brequest -> bool” |-> “λq : num # brequest. FST q = fd”] got_FILTER_fits)) >>
  simp[]
QED
