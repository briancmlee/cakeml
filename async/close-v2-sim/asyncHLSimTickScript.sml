(*
  The simulation across time: a step of the version-2 schedule is the
  renamed step of the version-1 one (deliver_step_sim), a tick keeps the
  relation (tick_sim), and so the version-1 world of a fair version-2
  world is fair (v1of_sched_wf): the version-1 theorems apply to it.
*)
Theory asyncHLSimTick
Ancestors
  llist alist words ffiSpikeSocketFFI ffiSpikeSocketFair socketV2FFI
  socketV2Fair asyncHLFair asyncHLModel asyncHLSimWorld
Libs
  preamble

Theorem hsim0_with_sched[simp]:
  hsim0 lfd (s1 with sched := x) (s2 with future := y, hs) ⇔ hsim0 lfd s1 (s2, hs)
Proof
  simp[hsim0_def]
QED

Theorem deliver1_sched_eq[local]:
  (deliver1 s a).sched = s.sched
Proof
  Cases_on ‘a’ >> rw[deliver1_def]
QED

Theorem FOLDL_deliver1_sched[local]:
  ∀as s. (FOLDL deliver1 s as).sched = s.sched
Proof
  Induct >> simp[deliver1_sched_eq]
QED

Theorem deliver1_with_sched[local]:
  deliver1 (s with sched := x) a = (deliver1 s a) with sched := x
Proof
  Cases_on ‘a’ >> rw[deliver1_def, is_listener_def, is_conn_def]
QED

Theorem step_ok_sched[local]:
  ∀as s. step_ok (s with sched := x) as ⇔ step_ok s as
Proof
  Induct >> simp[step_ok_def, deliver1_with_sched]
  >> Cases >> simp[arrival_ok_def, is_listener_def, is_conn_def]
QED

Theorem deliver2_with_future[local]:
  deliver2 (s with future := x) a = (deliver2 s a) with future := x
Proof
  Cases_on ‘a’ >> rw[deliver2_def, update_client_def]
QED

Theorem step_ok2_future[local]:
  ∀as s. step_ok2 (s with future := x) as ⇔ step_ok2 s as
Proof
  Induct >> simp[step_ok2_def, deliver2_with_future]
  >> Cases >> simp[arrival_ok2_def]
QED

(* MAIN: an effective version-2 step is the renamed version-1 step, and
   delivering both keeps the relation *)
Theorem deliver_step_sim:
  ∀as s1 s2.
    hsim0 lfd s1 (s2, hs) ∧ step_ok2 s2 as ⇒
    step_ok s1 (SND (rn_step lfd (LENGTH s2.clients) as)) ∧
    hsim0 lfd (FOLDL deliver1 s1 (SND (rn_step lfd (LENGTH s2.clients) as)))
              (FOLDL deliver2 s2 as, hs) ∧
    LENGTH (FOLDL deliver2 s2 as).clients = FST (rn_step lfd (LENGTH s2.clients) as) ∧
    (FOLDL deliver2 s2 as).future = s2.future
Proof
  Induct >> simp[rn_step_def, step_ok_def, step_ok2_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on ‘rn_arr lfd (LENGTH s2.clients) h’ >> rename1 ‘_ = (k1, b)’ >>
  drule_all deliver_sim >> strip_tac >>
  first_x_assum (qspecl_then [‘deliver1 s1 b’, ‘deliver2 s2 h’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[step_ok_def]
QED

(* MAIN: a tick keeps the relation; the version-1 world's next step is
   effective when the version-2 one is *)
Theorem tick_sim:
  hsim lfd s1 (s2, hs) ∧ step_ok2 s2 (next_step2 s2) ⇒
  step_ok s1 (next_step s1) ∧ hsim lfd (tick s1) (tick2 s2, hs)
Proof
  simp[hsim_def] >> strip_tac >> Cases_on ‘LHD s2.future’
  >- gvs[next_step_def, next_step2_def, rn_sched_LHD, tick_def, tick2_def, step_ok_def]
  >> rename1 ‘LHD s2.future = SOME st’
  >> ‘LHD s1.sched = SOME (SND (rn_step lfd (LENGTH s2.clients) st))’
       by gvs[rn_sched_LHD]
  >> ‘LTL s1.sched =
        SOME (rn_sched lfd (FST (rn_step lfd (LENGTH s2.clients) st)) (THE (LTL s2.future)))’
       by (gvs[] >> irule rn_sched_LTL >> simp[])
  >> ‘hsim0 lfd (s1 with sched := THE (LTL s1.sched))
                (s2 with future := THE (LTL s2.future), hs)’ by simp[]
  >> ‘step_ok2 (s2 with future := THE (LTL s2.future)) st’
       by gvs[step_ok2_future, next_step2_def]
  >> drule_all deliver_step_sim >> strip_tac
  >> gvs[next_step_def, next_step2_def, tick_def, tick2_def, deliver_def, FOLDL_deliver1_sched,
         step_ok_sched]
QED

(* The worlds left alone stay related *)
Theorem ticks_sim:
  ∀n s1 s2. hsim lfd s1 (s2, hs) ∧ sched_wf2 s2 ⇒
            hsim lfd (ticks n s1) (ticks2 n s2, hs) ∧ sched_wf2 (ticks2 n s2)
Proof
  Induct >> simp[ticks_def, ticks2_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> drule sched_wf2_tick >> strip_tac >> simp[] >>
  metis_tac[tick_sim]
QED

(* MAIN: the version-1 world of a fair version-2 server world is fair *)
Theorem v1of_sched_wf:
  s2.listening = [(lfd, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  sched_wf (v1of lfd s2)
Proof
  strip_tac >> drule_all hsim_init >> strip_tac >> rw[sched_wf_def] >>
  drule_all ticks_sim >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule sched_wf2_tick >> strip_tac >> metis_tac[tick_sim]
QED
