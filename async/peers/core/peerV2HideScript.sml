(*
  In a version-2 world, what a client the program never accepts sends is
  unobservable: a world that differs from it only in that client's data
  and EOF (hrel j) gives the same answers along any run that accepts at
  most j clients, so a diverging run is a run there too (hide_diverge).

  The program can see a client only through an accepted fd (client_of
  looks in open_fds), and accepts are first in, first out from the one
  listener (qinv lfd k: the queue holds clients k, k + 1, ...; open fds
  are clients below k).  So, with at most j accepts, client j is never
  seen.  No discipline is needed: in version 2 the program cannot touch
  a client before accepting it.
*)
Theory peerV2Hide
Ancestors
  llist ffi semantics socketWorld lifetimeWorld lifetimeFair EchoEpisodesSpec
  ffiAgreeUpto peerV1Run
Libs
  preamble

(* ------------------------------------------------------------------------
   The relation and the queue invariant
   ------------------------------------------------------------------------ *)

Definition touches_def:
  touches j (Connect2 l) = F ∧
  touches j (Data2 i bs) = (i = j) ∧
  touches j (Eof2 i) = (i = j)
End

Overload hfut = “λj (f : arrival2 list llist). LMAP (FILTER (λa. ¬touches j a)) f”

(* s' is s, but for client j's stream and arrivals *)
Definition hrel_def:
  hrel j (s:sockets2) (s':sockets2) ⇔
    s'.listening = s.listening ∧ s'.open_fds = s.open_fds ∧ s'.reserved = s.reserved ∧
    s'.alloc = s.alloc ∧ LENGTH s'.clients = LENGTH s.clients ∧
    (∀i. i ≠ j ⇒ EL i s'.clients = EL i s.clients) ∧ hfut j s'.future = hfut j s.future
End

(* The queue holds the clients from k on; the open fds are clients below k *)
Definition qinv_def:
  qinv lfd k (s:sockets2) ⇔
    s.listening = [(lfd, GENLIST (λi. i + k) (LENGTH s.clients − k))] ∧
    k ≤ LENGTH s.clients ∧ ∀f i. MEM (f, i) s.open_fds ⇒ i < k
End

Theorem lifetime_world_qinv:
  lifetime_world lfd s ⇒ qinv lfd 0 s
Proof
  rw[lifetime_world_def, qinv_def]
QED

Theorem hrel_refl[simp]:
  hrel j s s
Proof
  simp[hrel_def]
QED

Theorem hrel_sym:
  hrel j s s' ⇒ hrel j s' s
Proof
  rw[hrel_def] >> metis_tac[]
QED

Theorem hrel_trans:
  hrel j s1 s2 ∧ hrel j s2 s3 ⇒ hrel j s1 s3
Proof
  rw[hrel_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Time passes
   ------------------------------------------------------------------------ *)

Theorem deliver2_hrel[local]:
  hrel j s s' ⇒ hrel j (deliver2 s a) (deliver2 s' a)
Proof
  Cases_on ‘a’ >> rw[hrel_def, deliver2_def, update_client_def] >> gvs[] >>
  gvs[EL_APPEND_EQN, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem deliver2_touch[local]:
  touches j a ∧ hrel j s s' ⇒ hrel j s (deliver2 s' a)
Proof
  Cases_on ‘a’ >> rw[hrel_def, deliver2_def, update_client_def, touches_def] >>
  gvs[EL_LUPDATE]
QED

Theorem FOLDL_hrel[local]:
  ∀st s s'. hrel j s s' ⇒
            hrel j (FOLDL deliver2 s (FILTER (λa. ¬touches j a) st)) (FOLDL deliver2 s' st)
Proof
  Induct >> simp[] >> rw[] >> first_x_assum irule
  >- simp[deliver2_hrel] >>
  irule deliver2_touch >> simp[]
QED

Theorem FOLDL_hrel_eq[local]:
  hrel j s s' ∧ FILTER (λa. ¬touches j a) st = FILTER (λa. ¬touches j a) st' ⇒
  hrel j (FOLDL deliver2 s st) (FOLDL deliver2 s' st')
Proof
  strip_tac >>
  ‘hrel j (FOLDL deliver2 s (FILTER (λa. ¬touches j a) st)) (FOLDL deliver2 s st)’
    by simp[FOLDL_hrel] >>
  ‘hrel j (FOLDL deliver2 s (FILTER (λa. ¬touches j a) st')) (FOLDL deliver2 s' st')’
    by simp[FOLDL_hrel] >>
  metis_tac[hrel_sym, hrel_trans]
QED

Theorem tick2_hrel:
  hrel j s s' ⇒ hrel j (tick2 s) (tick2 s')
Proof
  strip_tac >> simp[tick2_def] >>
  ‘hfut j s'.future = hfut j s.future’ by fs[hrel_def] >>
  qspec_then ‘s.future’ strip_assume_tac llist_CASES >>
  qspec_then ‘s'.future’ strip_assume_tac llist_CASES >> gvs[] >>
  irule FOLDL_hrel_eq >> fs[hrel_def]
QED

Theorem deliver2_qinv[local]:
  qinv lfd k s ⇒ qinv lfd k (deliver2 s a)
Proof
  Cases_on ‘a’ >> rw[qinv_def, deliver2_def, update_client_def] >> gvs[] >>
  gvs[AFUPDKEY_def] >>
  ‘LENGTH s.clients + 1 − k = SUC (LENGTH s.clients − k)’ by decide_tac >>
  simp[GENLIST, SNOC_APPEND] >> metis_tac[]
QED

Theorem tick2_qinv:
  qinv lfd k s ⇒ qinv lfd k (tick2 s)
Proof
  strip_tac >> simp[tick2_def] >> CASE_TAC >>
  ‘∀st s. qinv lfd k s ⇒ qinv lfd k (FOLDL deliver2 s st)’
    by (Induct >> simp[deliver2_qinv]) >>
  first_x_assum irule >> fs[qinv_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The calls
   ------------------------------------------------------------------------ *)

Theorem client_of_hide[local]:
  qinv lfd k s ∧ hrel j s s' ∧ client_of s f = SOME i ⇒
  client_of s' f = SOME i ∧ i < k
Proof
  rw[client_of_def, AllCaseEqs()] >> fs[hrel_def, qinv_def] >>
  imp_res_tac ALOOKUP_MEM >> res_tac
QED

Theorem client_of_hrel[local]:
  hrel j s s' ⇒ client_of s' f = client_of s f
Proof
  rw[client_of_def, hrel_def]
QED

Theorem is_ready2_hide[local]:
  qinv lfd k s ∧ hrel j s s' ∧ k ≤ j ⇒ is_ready2 s' fd = is_ready2 s fd
Proof
  rw[is_ready2_def] >>
  ‘client_of s' fd = client_of s fd’ by metis_tac[client_of_hrel] >>
  ‘s'.listening = s.listening’ by fs[hrel_def] >> simp[] >>
  Cases_on ‘client_of s fd’ >> simp[] >>
  drule_all client_of_hide >> strip_tac >>
  ‘x ≠ j’ by decide_tac >> fs[hrel_def]
QED

Theorem update_client_hide[local]:
  hrel j s s' ∧ i ≠ j ⇒ hrel j (update_client i g s) (update_client i g s')
Proof
  rw[hrel_def, update_client_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem update_client_qinv[local]:
  qinv lfd k s ⇒ qinv lfd k (update_client i g s)
Proof
  rw[qinv_def, update_client_def]
QED

(* The answer to a call, and the relation after it *)
Theorem oracle_hide:
  qinv lfd k s ∧ hrel j s s' ∧
  socket2_oracle (ExtCall n) s conf (MAP FST bl) = Oracle_return s1 (MAP SND bl) ∧
  k + LENGTH (accepted_fds [IO_event (ExtCall n) conf bl]) ≤ j ⇒
  ∃s1'. socket2_oracle (ExtCall n) s' conf (MAP FST bl) = Oracle_return s1' (MAP SND bl) ∧
        hrel j s1 s1' ∧ qinv lfd (k + LENGTH (accepted_fds [IO_event (ExtCall n) conf bl])) s1
Proof
  strip_tac >>
  qpat_x_assum ‘socket2_oracle _ _ _ _ = _’ mp_tac >>
  simp[socket2_oracle_def, socket2_fn_def] >>
  ‘k ≤ j’ by fs[] >>
  rw[] >> gvs[AllCaseEqs()]
  >- ((* poll *)
      gvs[ffi_sock_poll2_def, sock_poll2_def, accepted_fds_def, event_accepted_def] >>
      ‘hrel j (tick2 s) (tick2 s') ∧ qinv lfd k (tick2 s)’ by simp[tick2_hrel, tick2_qinv] >>
      ‘∀fd. is_ready2 (tick2 s') fd = is_ready2 (tick2 s) fd’ by metis_tac[is_ready2_hide] >>
      simp[])
  >- ((* accept *)
      gvs[ffi_sock_accept2_def, AllCaseEqs(), sock_accept2_def] >>
      qpat_x_assum ‘_ = MAP SND bl’ (assume_tac o SYM) >>
      ‘s'.listening = s.listening ∧ used_fds s' = used_fds s ∧ s'.alloc = s.alloc’
        by fs[hrel_def, used_fds_def] >>
      fs[accepted_fds_def, event_accepted_def] >>
      rename1 ‘ALOOKUP s.listening l = SOME (i::q)’ >>
      ‘LENGTH (fd_bytes (s.alloc i (used_fds s))) = 8’
        by (qpat_x_assum ‘MAP SND bl = _’ (mp_tac o Q.AP_TERM ‘LENGTH’) >> simp[]) >>
      fs[] >>
      ‘i = k ∧ q = GENLIST (λi. i + (k + 1)) (LENGTH s.clients − (k + 1)) ∧
       l = lfd ∧ k < LENGTH s.clients’
        by (fs[qinv_def] >> gvs[AllCaseEqs()] >>
            Cases_on ‘LENGTH s.clients − k’ >> gvs[GENLIST_CONS] >>
            simp[combinTheory.o_DEF, ADD1] >> rw[] >> TRY decide_tac >>
            AP_TERM_TAC >> decide_tac) >>
      gvs[] >> conj_tac
      >- (fs[hrel_def, AFUPDKEY_def] >> metis_tac[])
      >> fs[qinv_def, AFUPDKEY_def] >> rw[] >> res_tac >> decide_tac)
  >- ((* read *)
      gvs[ffi_sock_read2_def, AllCaseEqs(), sock_read2_def, accepted_fds_def,
          event_accepted_def] >>
      drule_all client_of_hide >> strip_tac >>
      ‘j' ≠ j ∧ EL j' s'.clients = EL j' s.clients’ by (fs[hrel_def] >> decide_tac) >>
      gvs[] >> simp[update_client_hide, update_client_qinv])
  >- ((* write *)
      gvs[ffi_sock_write2_def, AllCaseEqs(), sock_write2_def, accepted_fds_def,
          event_accepted_def] >>
      drule_all client_of_hide >> strip_tac >>
      ‘j' ≠ j’ by decide_tac >> simp[update_client_hide, update_client_qinv])
  >> (* close *)
  gvs[ffi_sock_close2_def, AllCaseEqs(), sock_close2_def, accepted_fds_def,
      event_accepted_def] >>
  drule_all client_of_hide >> strip_tac >> simp[] >>
  fs[hrel_def, qinv_def] >> rw[] >> fs[MEM_FILTER, ADELKEY_def] >> res_tac
QED

(* MAIN: along a run accepting at most j clients in all, the two worlds
   give the same answers *)
Theorem hide_events:
  ∀evs k s s' t.
    replays socket2_oracle s evs t ∧ qinv lfd k s ∧ hrel j s s' ∧
    k + LENGTH (accepted_fds evs) ≤ j ⇒
    ffi_answers (lifetime_ffi s') (calls_of evs) = ffi_answers (lifetime_ffi s) (calls_of evs)
Proof
  Induct >- simp[calls_of_def, ffi_answers_def] >>
  Cases >> rename1 ‘IO_event nm conf bl’ >> rpt gen_tac >> strip_tac >>
  fs[replays_def] >>
  ‘∃n. nm = ExtCall n’
    by (qpat_x_assum ‘socket2_oracle _ _ _ _ = _’ mp_tac >>
        Cases_on ‘nm’ >> simp[socket2_oracle_def]) >>
  gvs[] >>
  ‘accepted_fds (IO_event (ExtCall n) conf bl :: evs) =
   accepted_fds [IO_event (ExtCall n) conf bl] ++ accepted_fds evs’
    by simp[accepted_fds_def] >>
  ‘k + LENGTH (accepted_fds [IO_event (ExtCall n) conf bl]) ≤ j’ by fs[] >>
  drule_all oracle_hide >> strip_tac >>
  simp[calls_of_def, ffi_answers_def, lifetime_ffi_def] >>
  REWRITE_TAC[GSYM calls_of_def] >>
  ‘∀st. <|oracle := socket2_oracle; ffi_state := st; io_events := []|> = lifetime_ffi st’
    by simp[lifetime_ffi_def] >>
  simp[] >>
  first_x_assum irule >> simp[] >> reverse conj_tac >- metis_tac[] >>
  qexists_tac ‘k + LENGTH (accepted_fds [IO_event (ExtCall n) conf bl])’ >> fs[]
QED

(* MAIN: a diverging run that accepts at most j clients is a run in any
   world that differs only in client j's stream and arrivals *)
Theorem hide_diverge:
  semantics_prog (init_state (lifetime_ffi s)) init_env prog (Diverge io) ∧
  qinv lfd 0 s ∧ hrel j s s' ∧
  (∀evs. LPREFIX (fromList evs) io ⇒ LENGTH (accepted_fds evs) ≤ j) ⇒
  semantics_prog (init_state (lifetime_ffi s')) init_env prog (Diverge io)
Proof
  strip_tac >>
  ‘init_state (lifetime_ffi s') = init_state (lifetime_ffi s) with ffi := lifetime_ffi s'’
    by simp[ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality] >>
  pop_assum SUBST1_TAC >> irule semantics_prog_upto >>
  simp[ml_progTheory.init_state_def] >>
  rpt conj_tac >> TRY (simp[lifetime_ffi_def] >> NO_TAC) >>
  REWRITE_TAC[GSYM ml_progTheory.init_state_def] >>
  rw[agree_upto_def] >>
  ‘(lifetime_ffi s).io_events = [] ∧ (lifetime_ffi s).oracle = socket2_oracle ∧
   (lifetime_ffi s).ffi_state = s’ by simp[lifetime_ffi_def] >>
  drule_all clock_calls_trace >> strip_tac >> gvs[] >>
  CONV_TAC SYM_CONV >> irule hide_events >> simp[] >> reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [‘j’, ‘0’, ‘lfd’] >> simp[]
QED
