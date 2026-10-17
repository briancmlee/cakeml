(*
  The moonshot's LIVENESS headline from its obligations, one per owner
  (the liveness analogue of close-v2's moonshot_safe_client).

  MAIN: moonshot_live_of_run_obs: moonshot_live kb cprog pprog kprog from
    - client_run_ob kb cprog       (close-v2)
    - proxy_run_ob kb pprog        (honest-ffi / m4-server)
    - kv_run_ob kb kprog           (KV owner / e1-driver)
    - topology_run_ob cprog pprog kprog   (each program listens only on its own port)
    - closes_run_ob kb cprog pprog kprog   ([R3], joint, r3-close)
    - exits_run_ob kb cprog pprog kprog    ([R3], the client exits once served)
  Each is stated over the run, for every run of moonshot_live_hyps, with
  X = sys_excuse.  At the concrete programs each becomes a discharge from
  the program's L0 claim through a lift (the lifts are moonshot-live's;
  the list is in README §6, "Final instantiation"):

  client_run_ob  ⇐ client_live_claim (C-asks, C-sends, C-reads, one connect
                   episode per logical connection to a) + "the client calls
                   infinitely often" + l0sys_proj_inf / l0sys_proj_drains;
  proxy_run_ob   ⇐ proxy_live_l0 (P-fwd) + proxy_asks_l0 (P-asks) +
                   conn_live_l0 (a backend per front) with accepts_lt
                   (accepts_lt_irun: the proxy accepts only on a; close-v2's
                   fact 1 and no_close_stdio) + "the proxy calls infinitely
                   often" (CALLS-IO hypothesis below, from proxySem's
                   infinite-trace Diverge: non-blocking polls every round);
  kv_run_ob      ⇐ kv_live_claim (K-asks, K-answers; F1_io, F2) + "KV calls
                   infinitely often" (CALLS-IO, from KV's Sem theorem).
*)
Theory moonshotLiveFinal
Ancestors
  moonshotLiveCompose moonshotLiveObs moonshotLiveStmts l0sysFair
Libs
  preamble

(* The run hypotheses and the excuse of the headline, at given programs *)
Definition mhyps_def:
  mhyps cprog pprog kprog a b c N rqs ss rs ⇔
    moonshot_live_hyps a b c N rqs (moonshot_sys cprog pprog kprog a b c N rqs) ss rs
End

Definition mX_def:
  mX kb cprog pprog kprog a b c N rqs ss rs ⇔
    sys_excuse kb (moonshot_sys cprog pprog kprog a b c N rqs) ss rs
End

(* The client (close-v2): one episode per logical connection, a connect to
   a, and on each the client's clauses *)
Definition client_run_ob_def:
  client_run_ob kb cprog ⇔
    ∀pprog kprog a b c N rqs ss rs.
      mhyps cprog pprog kprog a b c N rqs ss rs ⇒
      let X = mX kb cprog pprog kprog a b c N rqs ss rs in
        ∃ep. client_open X a N rs ep ∧ ∀i. i < N ⇒ client_conn_ob X ss rs (ep i) (rqs i)
End

(* The proxy (honest-ffi): a backend per front, and the forwarding and
   asking clauses per pair *)
Definition proxy_run_ob_def:
  proxy_run_ob kb pprog ⇔
    ∀cprog kprog a b c N rqs ss rs.
      mhyps cprog pprog kprog a b c N rqs ss rs ⇒
      ∃bk. proxy_ob (mX kb cprog pprog kprog a b c N rqs ss rs) a b ss rs bk
End

(* KV: asks and answers on each end paired with a connect to b *)
Definition kv_run_ob_def:
  kv_run_ob kb kprog ⇔
    ∀cprog pprog a b c N rqs ss rs.
      mhyps cprog pprog kprog a b c N rqs ss rs ⇒
      kv_ob (mX kb cprog pprog kprog a b c N rqs ss rs) b ss rs
End

(* Only the proxy listens on a, only KV on b *)
Definition topology_run_ob_def:
  topology_run_ob cprog pprog kprog ⇔
    ∀a b c N rqs ss rs. mhyps cprog pprog kprog a b c N rqs ss rs ⇒ topology_ob a b ss
End

(* [R3], joint: no chain end is lost before its episode is done, for the
   client's episodes and the proxy's backends *)
Definition closes_run_ob_def:
  closes_run_ob kb cprog pprog kprog ⇔
    ∀a b c N rqs ss rs ep bk.
      mhyps cprog pprog kprog a b c N rqs ss rs ∧
      client_open (mX kb cprog pprog kprog a b c N rqs ss rs) a N rs ep ∧
      proxy_ob (mX kb cprog pprog kprog a b c N rqs ss rs) a b ss rs bk ⇒
      ∀i. i < N ⇒ closes_ob (mX kb cprog pprog kprog a b c N rqs ss rs) ss rs bk (ep i) (rqs i)
End

(* [R3]: the client exits *)
Definition exits_run_ob_def:
  exits_run_ob kb cprog pprog kprog ⇔
    ∀a b c N rqs ss rs.
      mhyps cprog pprog kprog a b c N rqs ss rs ⇒
      mX kb cprog pprog kprog a b c N rqs ss rs ∨
      client_exits (moonshot_sys cprog pprog kprog a b c N rqs) rs 0
End

(* CALLS-IO, per program k (1 = proxy, 2 = KV): the premise of the drains
   and accepts lifts (l0sys_proj_drains, accepts_lt_irun).  Owed per
   program, from its binary's infinite-trace Diverge (e1-driver's proxySem /
   KV Sem) and the projection; used by the lifts, not by the theorem below *)
Definition calls_io_def:
  calls_io k cprog pprog kprog ⇔
    ∀a b c N rqs ss rs. mhyps cprog pprog kprog a b c N rqs ss rs ⇒
                        ∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')
End

Theorem moonshot_live_of_run_obs:
  client_run_ob kb cprog ∧ proxy_run_ob kb pprog ∧ kv_run_ob kb kprog ∧
  topology_run_ob cprog pprog kprog ∧ closes_run_ob kb cprog pprog kprog ∧
  exits_run_ob kb cprog pprog kprog ⇒
  moonshot_live kb cprog pprog kprog
Proof
  strip_tac >>
  irule (REWRITE_RULE [moonshot_live_of_obs_claim_def] moonshot_live_of_obs) >>
  rpt gen_tac >> strip_tac >>
  ‘mhyps cprog pprog kprog a b c N rqs ss rs’ by simp[mhyps_def] >>
  conj_tac
  >- (simp[moonshot_obs_def] >> disj2_tac >>
      qpat_x_assum ‘client_run_ob _ _’ mp_tac >> rewrite_tac[client_run_ob_def] >>
      disch_then drule >> simp[LET_THM, mX_def] >> strip_tac >>
      qpat_x_assum ‘proxy_run_ob _ _’ mp_tac >> rewrite_tac[proxy_run_ob_def] >>
      disch_then drule >> simp[mX_def] >> strip_tac >>
      qexistsl_tac [‘ep’, ‘bk’] >> simp[] >>
      ‘topology_ob a b ss’ by metis_tac[topology_run_ob_def] >>
      ‘kv_ob (sys_excuse kb (moonshot_sys cprog pprog kprog a b c N rqs) ss rs) b ss rs’
        by metis_tac[kv_run_ob_def, mX_def] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum ‘closes_run_ob _ _ _ _’ mp_tac >> rewrite_tac[closes_run_ob_def] >>
      disch_then (qspecl_then [‘a’, ‘b’, ‘c’, ‘N’, ‘rqs’, ‘ss’, ‘rs’, ‘ep’, ‘bk’] mp_tac) >>
      simp[mX_def]) >>
  metis_tac[exits_run_ob_def, mX_def]
QED
