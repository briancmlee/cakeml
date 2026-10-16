(*
  The protocol server's run becomes stable after the last arrival (option
  C, design/33 §2.5 (c); Q1), for every protocol P with proto_ok P.

  - From some round on, the polling run performs no actions: every action
    after the last arrival shrinks the measure (asyncProtoMeasure's
    proto_acts_stop).
  - Then nothing the Level 2 server waits for is ready: if it waited for
    Readable x with x ready, x would be polled (the listener, or a
    connection the server accepted, asyncOCAcc's proto_acc), stay ready
    (no actions, no arrivals), and make the server act in the next round
    (asyncProtoReact's proto_reacts).

  This is the hypothesis asyncOCSleeps' qsel_sleeps asks of a program, for
  the generic protocol server.

  MAIN: proto_stable.
*)
Theory asyncProtoStable
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety ffiSpikeSocketFFI ffiSpikeSocketFair asyncM3World
  asyncM4GRounds asyncM4GTrans asyncM4SockInv asyncM4Relabel
  asyncM4RelabelDist asyncM4SockModel asyncM4EchoRunOk asyncM4Loop
  asyncM4Sched asyncM4LiveProg asyncM4LiveServer asyncRunOkGen
  asyncStaticRounds asyncEchoStable asyncServerV asyncProto asyncProtoServer
  asyncProtoV2 asyncOCProtoModel asyncOCAcc asyncSWActs asyncProtoActs
  asyncProtoReact asyncProtoMeasure QuietSpec
Libs
  preamble

Theorem gres_idle[local]:
  gacts ifds m s0 n = [] ⇒ gres ifds m s0 n = []
Proof
  simp[gres_def, sock_acts_tot_def, sock_acts_def]
QED

Theorem gstate_idle[local]:
  gacts ifds m s0 n = [] ⇒ gstate ifds m s0 (SUC n) = tick (gstate ifds m s0 n)
Proof
  simp[gstate_SUC, gmid_def, sock_acts_tot_def, sock_acts_def]
QED

Theorem is_ready_tick[local]:
  next_step s = [] ⇒ (is_ready (tick s) w ⇔ is_ready s w)
Proof
  strip_tac >> drule tick_static >> simp[is_ready_def]
QED

(* What the Level 2 server waits for is polled *)
Theorem waiting_polled:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  Readable x ∈ waiting_on (proto_server_v2 idVu P (K NONE) (λr k. resp r) lfdn)
                 (MAP sfs (ghist (EI lfdn) (PM P resp lfdn) s0 n)) ⇒
  x < dimword (:64) ∧ MEM (n2w x) (EI lfdn (ghist (EI lfdn) (PM P resp lfdn) s0 n))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (PM P resp lfdn) s0’ by metis_tac[proto_grun_ok] >>
  ‘uses_ok lfdn (proto_server P resp lfdn)’ by metis_tac[proto_uses_ok] >>
  drule proto_acc >> disch_then drule >> strip_tac
  >- (gvs[] >> metis_tac[interest_accepted, MEM])
  >> qabbrev_tac ‘TT = TSg (proto_server P resp lfdn) (EI lfdn) s0 n’ >>
  ‘MEM x (accepted TT)’
    by (CCONTR_TAC >>
        ‘FILTER ($= x) (accepted TT) = []’
          by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
        gvs[accs_accepted]) >>
  ‘MEM x (MAP w2n (wacc (gperf (EI lfdn) (PM P resp lfdn) s0 n)))’
    by (drule_all gen_sinv >>
        disch_then (qspecl_then [‘EI lfdn’, ‘n’] strip_assume_tac) >>
        drule gen_trans_split >> strip_tac >>
        drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
        gvs[Abbr ‘TT’, accepted_NONE]) >>
  gvs[MEM_MAP] >> conj_tac >- (qspec_then ‘y’ mp_tac w2n_lt >> simp[]) >>
  metis_tac[interest_accepted]
QED

(* MAIN (Q1): in a world where only finitely many things arrive, the
   polling run of the protocol server reaches a round after which it
   performs no actions, and nothing the Level 2 server waits for is ready *)
Theorem proto_stable:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  lfdn < dimword (:64) ∧ arrivals_finite s0 ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
    gacts (EI lfdn) (srelabel (proto_server P resp lfdn)) s0 n = [] ∧
    ∀x. Readable x ∈ waiting_on (proto_server_v2 idVu P (K NONE) (λr k. resp r) lfdn)
                       (MAP sfs (ghist (EI lfdn) (srelabel (proto_server P resp lfdn)) s0 n)) ⇒
        ¬is_ready (gstate (EI lfdn) (srelabel (proto_server P resp lfdn)) s0 n) (n2w x)
Proof
  strip_tac >> drule_all proto_acts_stop >>
  disch_then (qspec_then ‘resp’ strip_assume_tac) >>
  qexists_tac ‘n1’ >> rpt gen_tac >> strip_tac >> simp[] >>
  rpt strip_tac >>
  drule_all waiting_polled >> strip_tac >>
  (* round n + 1 sees x ready, with no responses *)
  ‘gacts (EI lfdn) (PM P resp lfdn) s0 n = [] ∧
   gacts (EI lfdn) (PM P resp lfdn) s0 (SUC n) = []’ by simp[] >>
  ‘next_step (gstate (EI lfdn) (PM P resp lfdn) s0 n) = []’ by simp[] >>
  ‘is_ready (gstate (EI lfdn) (PM P resp lfdn) s0 (SUC n)) (n2w x)’
    by (‘gstate (EI lfdn) (PM P resp lfdn) s0 (SUC n) =
         tick (gstate (EI lfdn) (PM P resp lfdn) s0 n)’ by (irule gstate_idle >> fs[]) >>
        simp[is_ready_tick]) >>
  ‘gres (EI lfdn) (PM P resp lfdn) s0 n = []’ by (irule gres_idle >> fs[]) >>
  ‘NA (proto_server P resp lfdn)
      (MAP sfs (ghist (EI lfdn) (PM P resp lfdn) s0 n) ++
       [sfs (ssnap (FILTER (is_ready (gstate (EI lfdn) (PM P resp lfdn) s0 (SUC n)))
                           (EI lfdn (ghist (EI lfdn) (PM P resp lfdn) s0 n))) [])]) ≠ []’
    by (irule proto_reacts >> qexists_tac ‘x’ >> simp[] >>
        simp[snap_map_def, ssnap_def, sfe_def, MEM_FILTER] >>
        qexists_tac ‘n2w x’ >> simp[]) >>
  ‘gacts (EI lfdn) (PM P resp lfdn) s0 (SUC n) ≠ []’
    by (REWRITE_TAC[proto_gacts_SUC] >>
        qpat_x_assum ‘gres _ _ _ n = []’ (fn th => REWRITE_TAC[th]) >>
        simp[]) >>
  qpat_x_assum ‘∀n. n1 ≤ n ⇒ _’ (qspec_then ‘SUC n’ mp_tac) >> simp[]
QED
