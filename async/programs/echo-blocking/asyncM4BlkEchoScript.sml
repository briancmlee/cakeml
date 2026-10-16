(*
  The echo server ignores idle snapshots: idle_quiet for the computation
  the loop runs, srelabel (server lfd), discharged from the model.

  The model proves the Level 2 echo server quiet (asyncServer2:
  wf2_server2), and that it erases to the Level 1 server the loop runs
  (erase_server2).  `quiet` is about snapshots with none of the declared
  events ready; an idle snapshot has nothing ready at all, so it is
  ignored whatever the interest.  Relabelling into the socket vocabulary
  (sfs = snap_map sfe sfr) maps idle snapshots to idle snapshots.

  MAIN: idle_quiet_echo; and blocking_echo_server, asyncM4BlkTrace's
  two-outcome theorem for the echo server, with no hypothesis left.
*)
Theory asyncM4BlkEcho
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncServer asyncServer2
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4BlkWorld
  asyncM4BlkTrace EchoSpec
Libs
  preamble

(* A quiet computation ignores idle snapshots, whatever its interest *)
Theorem quiet_idle_quiet:
  quiet c ⇒ idle_quiet c.run
Proof
  rw[idle_quiet_def] >> fs[quiet_def] >> rw[] >>
  first_x_assum (qspecl_then [‘h’, ‘s’, ‘h'’] mp_tac) >> gvs[DISJOINT_DEF]
QED

(* Relabelling keeps idle_quiet, if idle snapshots stay idle *)
Theorem idle_quiet_relabel:
  idle_quiet m ∧
  (∀s. s.ready = ∅ ∧ s.results = [] ⇒ (fs s).ready = ∅ ∧ (fs s).results = []) ⇒
  idle_quiet (relabel fa fs m)
Proof
  rw[idle_quiet_def, quiet_def, icomp_def, new_actions_relabel] >>
  gvs[relabel_def, DISJOINT_DEF] >>
  ‘(fs s).ready = ∅ ∧ (fs s).results = []’ by simp[] >>
  first_x_assum (qspecl_then [‘MAP fs h’, ‘fs s’, ‘MAP fs h'’] mp_tac) >>
  simp[]
QED

Theorem sfs_idle:
  s.ready = ∅ ∧ s.results = [] ⇒ (sfs s).ready = ∅ ∧ (sfs s).results = []
Proof
  simp[snap_map_def, sfe_def]
QED

(* MAIN: the echo server, in the socket vocabulary, ignores idle
   snapshots while it has nothing to do *)
Theorem idle_quiet_echo:
  idle_quiet (srelabel (server lfd))
Proof
  irule idle_quiet_relabel >> simp[sfs_idle] >>
  ‘server lfd = (server2 lfd).run’ by simp[GSYM erase_server2, erase_def] >>
  pop_assum SUBST1_TAC >> irule quiet_idle_quiet >>
  metis_tac[wf2_server2, wf2_def]
QED

Theorem wf_echo:
  wf (srelabel (server lfd))
Proof
  irule wf_relabel >>
  ‘server lfd = (server2 lfd).run’ by simp[GSYM erase_server2, erase_def] >>
  pop_assum SUBST1_TAC >> metis_tac[wf2_server2, wf2_def]
QED

(* MAIN: the blocking echo loop (round-by-round model of the trace), for
   the echo server: either it runs forever, safe and live whenever the
   polling loop is; or it blocks forever in select after n rounds, and the
   finite trace of those rounds is safe and live whenever the polling
   loop's is. *)
Theorem blocking_echo_server =
  MATCH_MP blocking_echo (CONJ wf_echo idle_quiet_echo)
