(*
  Generic CF specs of with_store (kvProg's with_store, ws_run, ws_merge,
  ws_socks, ws_res), for any store representation and any step function:

  - the vocabulary Sock a | Kv q, and SockR r | KvR b (KACT, KRES);
  - DELTA p δ STORE QRY ANS deltav: the CakeML function deltav implements the
    store step δ;
  - with_store_spec: with_store implements the model's with_store δ s0 m, if
    its argument implements m.  Proved by the depth-indexed technique
    (libApprox): the residual ws_res carries the store in its closure,
    and with_store_suspended (withStoreStep) is the model's account of
    one poll;
  - ksreadable_spec: sreadable in this vocabulary.

  Independent of the store's implementation (kvSockSpec instantiates it).
*)
Theory withStoreSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose echoServer libModel
  libProg libApprox loopPollWorld loopPollProg loopPoll
  relabel relabelDist echoSockModel libSockApprox
  echoSockServer HttpGetSpec HttpHeadersSpec HttpSpec KvSpec
  httpGetParse httpHeadersParse httpParse protoInterface protoProg
  withStore withStoreStep skeletonK kvHandler
  kvModel kvSockModel kvProg ml_translator mlstring
  std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "kvProg"

val eq_string_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCTS |> el 6);

(* ------------------------------------------------------------------------
   The vocabulary: Sock a | Kv q, and SockR r | KvR b
   ------------------------------------------------------------------------ *)

local
  val env = get_env (get_ml_prog_state ())
  fun stamp_of c =
    EVAL “nsLookup (^env).c (Short ^c)” |> concl |> rhs
    |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
in
  val sock_stamp = stamp_of “«Sock»”
  val kv_stamp = stamp_of “«Kv»”
  val sockr_stamp = stamp_of “«Sockr»”
  val kvr_stamp = stamp_of “«Kvr»”
end

Definition KACT_def:
  KACT ACT QRY (Sock a) v = (∃av. v = Conv (SOME ^sock_stamp) [av] ∧ ACT a av) ∧
  KACT ACT QRY (Kv q) v = (∃qv. v = Conv (SOME ^kv_stamp) [qv] ∧ QRY q qv)
End

Definition KRES_def:
  KRES RES ANS (SockR r) v = (∃rv. v = Conv (SOME ^sockr_stamp) [rv] ∧ RES r rv) ∧
  KRES RES ANS (KvR b) v = (∃bv. v = Conv (SOME ^kvr_stamp) [bv] ∧ ANS b bv)
End

(* The server's vocabulary *)
Overload KQRY = “PAIR_TYPE NUM HTTPSPEC_BREQUEST_TYPE”
Overload KANS = “HTTPGETSPEC_RESPONSE_TYPE”
Overload KSACT = “KACT SACT KQRY”
Overload KSRESP = “KRES SRESP KANS”
Overload KSSNAP = “SNAPSHOT SREADY KSRESP”

(* DELTA p δ STORE QRY ANS deltav: the CakeML function deltav implements the
   store step δ, for stores represented by STORE *)
Definition DELTA_def:
  DELTA (p:'ffi ffi_proj) δ STORE QRY ANS deltav ⇔
    ∀s sv q qv. STORE s sv ∧ QRY q qv ⇒
      app p deltav [sv; qv] emp
        (POSTv v. &(∃bv sv'. v = Conv NONE [bv; sv'] ∧ ANS (FST (δ s q)) bv ∧
                             STORE (SND (δ s q)) sv'))
End

(* ------------------------------------------------------------------------
   with_store
   ------------------------------------------------------------------------ *)

Theorem ws_run_spec:
  ∀acts actsv st stv.
    DELTA p δ STORE QRY ANS deltav ∧
    LIST_TYPE (KACT ACT QRY) acts actsv ∧ STORE st stv ⇒
    app (p:'ffi ffi_proj) ws_run_v [deltav; stv; actsv] emp
      (POSTv v. &(∃bsv st2v. v = Conv NONE [bsv; st2v] ∧
                   LIST_TYPE ANS (FST (run_store δ st (queries acts))) bsv ∧
                   STORE (SND (run_store δ st (queries acts))) st2v))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "kvProg" "ws_run_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xlet_auto >- (xcon >> xsimpl) >> xcon >> xsimpl >>
      simp[run_store_def, LIST_TYPE_def]) >>
  Cases_on ‘h’ >> gvs[KACT_def] >> xmatch
  >- (xapp >> simp[] >> metis_tac[]) >>
  rename1 ‘QRY q qv’ >>
  xlet ‘POSTv v. &(∃bv sv'. v = Conv NONE [bv; sv'] ∧ ANS (FST (δ st q)) bv ∧
                            STORE (SND (δ st q)) sv')’
  >- (gvs[DELTA_def] >> xapp >> simp[]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &(∃bsv st2v. v = Conv NONE [bsv; st2v] ∧
                   LIST_TYPE ANS (FST (run_store δ (SND (δ st q)) (queries acts))) bsv ∧
                   STORE (SND (run_store δ (SND (δ st q)) (queries acts))) st2v)’
  >- (xapp >> simp[] >> metis_tac[]) >>
  gvs[] >> xmatch >> xlet_auto >- (xcon >> xsimpl) >> xcon >> xsimpl >>
  simp[run_store_def] >> rpt (pairarg_tac >> gvs[]) >> simp[LIST_TYPE_def]
QED

Theorem ws_merge_spec:
  ∀acts actsv rs rsv ans ansv.
    LIST_TYPE (KACT ACT QRY) acts actsv ∧ LIST_TYPE RES rs rsv ∧
    LIST_TYPE ANS ans ansv ⇒
    app (p:'ffi ffi_proj) ws_merge_v [actsv; rsv; ansv] emp
      (POSTv v. &LIST_TYPE (KRES RES ANS) (merge acts rs ans) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "kvProg" "ws_merge_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
  Cases_on ‘h’ >> gvs[KACT_def] >> xmatch
  >- (Cases_on ‘rs’ >> gvs[LIST_TYPE_def] >> xmatch
      >- (xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
      xlet ‘POSTv v. &LIST_TYPE (KRES RES ANS) (merge acts t ans) v’
      >- (xapp >> simp[] >> metis_tac[]) >>
      xlet ‘POSTv v. &KRES RES ANS (SockR h) v’
      >- (xcon >> xsimpl >> simp[KRES_def]) >>
      xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
  Cases_on ‘ans’ >> gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
  xlet ‘POSTv v. &LIST_TYPE (KRES RES ANS) (merge acts rs t) v’
  >- (xapp >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv v. &KRES RES ANS (KvR h) v’
  >- (xcon >> xsimpl >> simp[KRES_def]) >>
  xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]
QED

Theorem ws_socks_spec:
  ∀acts actsv.
    LIST_TYPE (KACT ACT QRY) acts actsv ⇒
    app (p:'ffi ffi_proj) ws_socks_v [actsv] emp
      (POSTv v. &LIST_TYPE ACT (socks acts) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "kvProg" "ws_socks_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  Cases_on ‘h’ >> gvs[KACT_def] >> xmatch
  >- (xlet ‘POSTv v. &LIST_TYPE ACT (socks acts) v’ >- (xapp >> simp[]) >>
      xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp >> simp[]
QED

(* MAIN (helper): the residual, up to depth n *)
(* Rename a theorem's type variables apart, so that specialising it to the
   goal's terms (qspecl_then) does not identify them with the goal's *)
fun fresh_tys th =
  INST_TYPE (map (fn v => v |-> mk_vartype ("'z" ^ String.extract (dest_vartype v, 1, NONE)))
                 (filter (fn v => v <> “:'ffi”) (type_vars_in_term (concl th)))) th;

Theorem ws_res_spec_d:
  ∀n m sv st stv actsv.
    DELTA p δ STORE QRY ANS deltav ∧ wf m ∧
    STEPA p (KACT ACT QRY) A (SNAPSHOT READY (KRES RES ANS)) m sv ∧
    STORE st stv ∧ LIST_TYPE (KACT ACT QRY) (m []).actions actsv ⇒
    app (p:'ffi ffi_proj) ws_res_v [deltav; stv; actsv; sv] emp
      (POSTv v. &STEPAd p ACT A (SNAPSHOT READY RES) n (with_store δ st m) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def (fetch "kvProg" "ws_res_v_def") >>
  qpat_x_assum ‘STEPA _ _ _ _ m sv’ (strip_assume_tac o ONCE_REWRITE_RULE [STEPA_cases]) >>
  gvs[]
  >- ((* finished *)
      xmatch >> xcon >> xsimpl >>
      simp[with_store_finished, STEPAd_finished]) >>
  (* pending: the closure *)
  xmatch >> xfun ‘f’ >> xcon >> xsimpl >>
  Cases_on ‘n’ >- simp[STEPAd_def, with_store_first] >>
  simp[Once STEPAd_def, with_store_first] >>
  rpt strip_tac >> simp[returns_def] >>
  rename1 ‘STEPAd _ _ _ _ n’ >>
  qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def] >> xmatch >>
  qabbrev_tac ‘bs = FST (run_store δ st (queries (m []).actions))’ >>
  qabbrev_tac ‘st2 = SND (run_store δ st (queries (m []).actions))’ >>
  xlet ‘POSTv v. &(∃bsv st2v. v = Conv NONE [bsv; st2v] ∧ LIST_TYPE ANS bs bsv ∧
                              STORE st2 st2v)’
  >- (qspecl_then [‘δ’, ‘STORE’, ‘QRY’, ‘ANS’, ‘deltav’, ‘ACT’, ‘(m []).actions’, ‘actsv’, ‘st’, ‘stv’]
        mp_tac (fresh_tys (Q.GENL [‘δ’, ‘STORE’, ‘QRY’, ‘ANS’, ‘deltav’, ‘ACT’] ws_run_spec)) >>
      simp[] >> strip_tac >> xapp >> simp[Abbr ‘bs’, Abbr ‘st2’, first_answers_def]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &LIST_TYPE (KRES RES ANS) (merge (m []).actions w.results bs) v’
  >- (qspecl_then [‘ACT’, ‘QRY’, ‘RES’, ‘ANS’, ‘(m []).actions’, ‘actsv’, ‘w.results’, ‘resv’, ‘bs’, ‘bsv’]
        mp_tac (fresh_tys (Q.GENL [‘ACT’, ‘QRY’, ‘RES’, ‘ANS’] ws_merge_spec)) >> simp[] >> strip_tac >> xapp) >>
  qabbrev_tac ‘w' = merged (m []).actions bs w’ >>
  xlet ‘POSTv v. &SNAPSHOT READY (KRES RES ANS) w' v’
  >- (xcon >> xsimpl >> simp[SNAPSHOT_def, Abbr ‘w'’, merged_def]) >>
  qpat_x_assum ‘∀w wv. _ ⇒ returns _ _ _ _’ (qspecl_then [‘w'’, ‘v'’] mp_tac) >>
  simp[] >> strip_tac >>
  xlet ‘POSTv v. &POLL_RESULT (KACT ACT QRY) (STEPA p (KACT ACT QRY) A
                    (SNAPSHOT READY (KRES RES ANS))) (suspended m [w']) v’
  >- (gvs[returns_def] >> xapp >> fs[SNAPSHOT_def]) >>
  gvs[POLL_RESULT_def] >> xmatch >>
  xlet ‘POSTv v. &STEPAd p ACT A (SNAPSHOT READY RES) n
                    (with_store δ st2 (suspended m [w'])) v’
  >- (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
      xapp >> simp[wf_suspended] >> metis_tac[]) >>
  xlet ‘POSTv v. &LIST_TYPE ACT (socks (suspended m [w'] []).actions) v’
  >- (qspecl_then [‘ACT’, ‘QRY’] mp_tac (fresh_tys (Q.GENL [‘ACT’, ‘QRY’] ws_socks_spec)) >>
      simp[] >> strip_tac >> xapp >> metis_tac[]) >>
  xcon >> xsimpl >>
  simp[POLL_RESULT_def, with_store_suspended, Abbr ‘w'’, Abbr ‘bs’, Abbr ‘st2’,
       with_store_first, first_answers_def]
QED

(* MAIN: with_store implements the model's with_store *)
Theorem with_store_spec:
  DELTA p δ STORE QRY ANS deltav ∧ wf m ∧ STORE s0 stv ∧
  COMP p (KACT ACT QRY) A (SNAPSHOT READY (KRES RES ANS)) m cv ⇒
  app (p:'ffi ffi_proj) with_store_v [deltav; stv; cv] emp
    (POSTv v. &COMP p ACT A (SNAPSHOT READY RES) (with_store δ s0 m) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "kvProg" "with_store_v_def") >>
  gvs[COMP_def, POLL_RESULT_def] >> xmatch >>
  (* constructor arguments are evaluated right to left *)
  xlet ‘POSTv v. &STEPAd p ACT A (SNAPSHOT READY RES) n (with_store δ s0 m) v’
  >- (qspecl_then [‘δ’, ‘STORE’, ‘QRY’, ‘ANS’, ‘deltav’, ‘ACT’, ‘A’, ‘READY’, ‘RES’] mp_tac
        (fresh_tys (Q.GENL [‘δ’, ‘STORE’, ‘QRY’, ‘ANS’, ‘deltav’, ‘ACT’, ‘A’, ‘READY’, ‘RES’]
                     ws_res_spec_d)) >>
      strip_tac >> xapp >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv v. &LIST_TYPE ACT (socks (m []).actions) v’
  >- (qspecl_then [‘ACT’, ‘QRY’] mp_tac (fresh_tys (Q.GENL [‘ACT’, ‘QRY’] ws_socks_spec)) >>
      simp[] >> strip_tac >> xapp >> metis_tac[]) >>
  xcon >> xsimpl >> simp[COMPd_def, POLL_RESULT_def, with_store_first]
QED

(* ------------------------------------------------------------------------
   sreadable, in the vocabulary of with_store
   ------------------------------------------------------------------------ *)

Theorem MEM_MAP_w2n[local]:
  MEM fd (MAP w2n (fds:word64 list)) ⇔ ∃c. MEM c fds ∧ w2n c = fd
Proof
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem ksreadable_spec:
  NUM fd fdv ⇒
  app (p:'ffi ffi_proj) sreadable_v [fdv] emp
    (POSTv v. &COMP p ACT UNIT_TYPE (SNAPSHOT SREADY R) (sreadable fd) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "echoSockServer" "sreadable_v_def") >>
  xfun ‘f’ >> simp[sreadable_def] >>
  ‘∀w wv. SNAPSHOT SREADY R w wv ⇒
     returns p f [wv]
       (OPTION_TYPE UNIT_TYPE
          (if ∃c. c ∈ w.ready ∧ w2n c = fd then SOME () else NONE))’
    by (rpt strip_tac >> simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        gvs[SNAPSHOT_def, SREADY_def] >> xmatch >>
        xlet ‘POSTv bv. &BOOL (MEM fd (MAP w2n fds)) bv’
        >- (xapp >> metis_tac[]) >>
        xif >> rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
        gvs[MEM_MAP_w2n] >> rw[OPTION_TYPE_def] >> fs[UNIT_TYPE_def] >>
        metis_tac[]) >>
  ‘app p Async_wait_v [f] emp
     (POSTv v. &COMP p ACT UNIT_TYPE (SNAPSHOT SREADY R)
        (wait (λs. if ∃c. c ∈ s.ready ∧ w2n c = fd then SOME () else NONE)) v)’
    by (irule Async_wait_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_wait_v _ _ _’ xapp_spec >> xsimpl
QED

