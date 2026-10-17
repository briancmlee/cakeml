(*
  The bridges below sys_run (design/45 §3.2, steps 3-4).

  B1 l0sys_proj: each process of an l0sys run sees an L0 world.  The world
  is built after the fact: its environment at k's n-th call delivers the
  arrivals the kernel delivered to k since its previous call, and a
  blocking poll, which l0sys answers once it may return, then waits no
  steps.  So every per-process theorem, stated for all L0 worlds with the
  rely, applies to each process of every system run (l0sys_proj_safe).

  B2 l0sys_causal: the kernel's prefix relations between the two ends of
  each connection inside the system, over the episodes of the processes'
  own traces (l0sysEpisodes): what one end's recvs returned is, at every
  instant, a prefix of what the other end's sends accepted.  conn pairs
  the episodes: a connect to port p with an accept on a listener of p.
  No fairness and no start order: a refused, dropped or reset connection
  only gives conn fewer pairs, or shorter streams.
*)
Theory l0sysBridges
Ancestors
  semantics alt_semantics honestL0World honestL0Rely l0sys l0sysEpisodes l0sysInv l0sysRun
  l0sysReplay l0sysProj
Libs
  preamble

(* The state sys_init gives each process *)
Definition l0_fresh_def:
  l0_fresh (w : l0world) ⇔
    w.listeners = [] ∧ w.chans = [] ∧ w.open_fds = [] ∧ w.clock = 0 ∧ w.hist = []
End

(* The I/O of a behaviour *)
Definition beh_io_def:
  beh_io (Terminate _ io) = fromList io ∧
  beh_io (Diverge io) = io ∧
  beh_io Fail = [||]
End

(* B1 (with design/45 §9 (d): the world's fds are below its limit) *)
Theorem l0sys_proj:
  l0sys_run ps rs ∧ k < LENGTH ps ⇒
  ∃w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ∧
       ∀b. semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) b ∧ b ≠ Fail ⇒
           LPREFIX (fromList (proc_events k rs)) (beh_io b)
Proof
  rw[l0sys_run_def] >> drule_all l0sys_world >> strip_tac >>
  qexists_tac ‘EL k s0.procs with env := E’ >>
  ‘l0_rely (EL k s0.procs) ∧ l0_fresh (EL k s0.procs) ∧ fds_lt (EL k s0.procs)’
    by fs[sys_init_def, LET_THM, l0_fresh_def, fds_lt_def] >>
  rpt conj_tac
  >- (irule l0_rely_ch >> qexists_tac ‘EL k s0.procs’ >> simp[])
  >- fs[l0_fresh_def]
  >- (qpat_x_assum ‘fds_lt _’ mp_tac >> simp[fds_lt_def, l0_used_def]) >>
  rpt strip_tac >>
  ‘prog_makes (EL k ps) (proc_events k rs)’ by simp[] >>
  qspecl_then [‘EL k ps’, ‘proc_events k rs’, ‘l0_ffi (EL k s0.procs with env := E)’, ‘b’]
    mp_tac (Q.GENL [‘prog’, ‘evs’, ‘f’, ‘b’] replay_prefix) >>
  impl_tac >- simp[l0_ffi_def] >>
  Cases_on ‘b’ >> fs[beh_io_def, LPREFIX_fromList, from_toList]
QED

Theorem proc_events_TAKE:
  proc_events k (TAKE t rs) ≼ proc_events k rs
Proof
  ‘rs = TAKE t rs ++ DROP t rs’ by simp[] >>
  qabbrev_tac ‘a = TAKE t rs’ >> qabbrev_tac ‘b = DROP t rs’ >>
  pop_assum kall_tac >> pop_assum kall_tac >> rveq >>
  simp[proc_events_APPEND]
QED

(* B1, as it is used: a per-process safety property holds of each process's
   events in a system run, at every instant *)
Theorem l0sys_proj_safe:
  l0sys_run ps rs ∧ k < LENGTH ps ∧
  (∀w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
        ∃b. semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) b ∧ b ≠ Fail ∧
            ∀evs. LPREFIX (fromList evs) (beh_io b) ⇒ P evs) ⇒
  ∀t. P (proc_events k (TAKE t rs))
Proof
  rpt strip_tac >> drule_all l0sys_proj >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum irule >> irule LPREFIX_TRANS >>
  qexists_tac ‘fromList (proc_events k rs)’ >>
  simp[LPREFIX_fromList, from_toList, proc_events_TAKE] >> metis_tac[]
QED

(* B2 *)
Theorem l0sys_causal:
  l0sys_run ps rs ⇒
  ∃conn. (∀e e'. conn e = SOME e' ⇔ conn e' = SOME e) ∧
    ∀k j k' j'. conn (k, j) = SOME (k', j') ⇒
      k < LENGTH ps ∧ k' < LENGTH ps ∧
      (∃p. l0_ep_role j (proc_events k rs) = SOME (Connected p) ∧
           l0_ep_role j' (proc_events k' rs) = SOME (Accepted p) ∨
           l0_ep_role j (proc_events k rs) = SOME (Accepted p) ∧
           l0_ep_role j' (proc_events k' rs) = SOME (Connected p)) ∧
      ∀t. l0_ep_recvd j' (proc_events k' (TAKE t rs)) ≼ l0_ep_sent j (proc_events k (TAKE t rs))
Proof
  rw[l0sys_run_def] >> drule_all sys_causal >> simp[]
QED
