(*
  Assumptions on the socket world's schedule, the liveness facts they
  give, and a non-vacuity lemma.

  In this model an arrival is delivered at the first readiness check
  («sock_poll») after it is scheduled: a delay in the network is a later
  position in the schedule.  So "data sent eventually becomes readable"
  and "pending connections are eventually acceptable" are not extra
  fairness assumptions here, but lemmas, under ONE named assumption:

    sched_wf: every arrival of the schedule makes sense when it arrives
              (no data for an unknown connection, no data after EOF, new
              connections are on listeners and use fresh fds), so that
              no arrival is silently dropped.

  The liveness lemmas are about one round (tick) and the world left alone
  (ticks); a program's own operations between rounds only consume data or
  pending connections (see the end of the file).
*)
Theory socketFair
Ancestors
  llist alist socketWorld
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The assumption *)

(* An arrival is effective in state s: deliver1 does not drop it. *)
Definition arrival_ok_def:
  (arrival_ok s (Connect l c) ⇔
     is_listener s l ∧ ¬is_listener s c ∧ ¬is_conn s c) ∧
  (arrival_ok s (Data c bs) ⇔
     ∃cn. ALOOKUP s.conns c = SOME cn ∧ ¬cn.peer_closed) ∧
  (arrival_ok s (Eof c) ⇔
     ∃cn. ALOOKUP s.conns c = SOME cn ∧ ¬cn.peer_closed)
End

(* Every arrival of a step is effective when it is delivered. *)
Definition step_ok_def:
  step_ok s [] = T ∧
  step_ok s (a::as) = (arrival_ok s a ∧ step_ok (deliver1 s a) as)
End

(* The world left alone for n rounds. *)
Definition ticks_def:
  ticks 0 s = s ∧
  ticks (SUC n) s = ticks n (tick s)
End

Definition next_step_def:
  next_step s = case LHD s.sched of NONE => [] | SOME as => as
End

(* ASSUMPTION sched_wf: left alone, the world never drops an arrival. *)
Definition sched_wf_def:
  sched_wf s ⇔ ∀n. step_ok (ticks n s) (next_step (ticks n s))
End

(*---------------------------------------------------------------------------*)
(* Readiness only grows as time passes *)

Theorem deliver1_ready_mono:
  is_ready s fd ⇒ is_ready (deliver1 s a) fd
Proof
  Cases_on ‘a’
  \\ rw [deliver1_def, is_ready_def, AFUPDKEY_ALOOKUP, is_listener_def,
         is_conn_def]
  \\ every_case_tac \\ gvs []
QED

Theorem deliver_ready_mono:
  ∀as s. is_ready s fd ⇒ is_ready (deliver s as) fd
Proof
  Induct \\ rw [deliver_def] \\ fs [GSYM deliver_def]
  \\ first_x_assum irule \\ simp [deliver1_ready_mono]
QED

(* §9's readiness_honest, for a world left alone: a ready fd stays ready
   until it is read. *)
Theorem tick_ready_mono:
  is_ready s fd ⇒ is_ready (tick s) fd
Proof
  rw [tick_def] \\ CASE_TAC \\ simp []
  \\ irule deliver_ready_mono
  \\ fs [is_ready_def]
QED

(*---------------------------------------------------------------------------*)
(* Each effective arrival makes its fd ready *)

(* The fd an arrival makes ready: the listener for a connection, the
   connection for data or EOF. *)
Definition arrival_fd_def:
  arrival_fd (Connect l c) = l ∧
  arrival_fd (Data c bs) = c ∧
  arrival_fd (Eof c) = c
End

(* Data arrivals of no bytes make nothing ready. *)
Definition arrival_nonempty_def:
  arrival_nonempty (Data c bs) = (bs ≠ []) ∧
  arrival_nonempty _ = T
End

Theorem deliver1_ready:
  arrival_ok s a ∧ arrival_nonempty a ⇒ is_ready (deliver1 s a) (arrival_fd a)
Proof
  Cases_on ‘a’
  \\ rw [arrival_ok_def, arrival_nonempty_def, arrival_fd_def, deliver1_def,
         is_ready_def, AFUPDKEY_ALOOKUP]
  \\ gvs [is_listener_def, is_conn_def]
  \\ every_case_tac \\ gvs []
QED

Theorem deliver_ready:
  ∀as s a. step_ok s as ∧ MEM a as ∧ arrival_nonempty a ⇒
           is_ready (deliver s as) (arrival_fd a)
Proof
  Induct \\ rw [step_ok_def, deliver_def] \\ fs [GSYM deliver_def]
  >- (irule deliver_ready_mono \\ irule deliver1_ready \\ simp [])
  \\ first_x_assum irule \\ simp []
QED

(* The schedule plays no part in delivering a step. *)
Theorem deliver1_sched[local]:
  deliver1 (s with sched := x) a = deliver1 s a with sched := x
Proof
  Cases_on ‘a’ \\ rw [deliver1_def, is_listener_def, is_conn_def]
QED

Theorem step_ok_sched[local]:
  ∀as s. step_ok (s with sched := x) as = step_ok s as
Proof
  Induct
  \\ rw [step_ok_def, deliver1_sched]
  \\ Cases_on ‘h’
  \\ simp [arrival_ok_def, is_listener_def, is_conn_def]
QED

(* LEMMA data_live / accept_live, one round: whatever arrives in the next
   step (data, EOF, a connection) is ready after the next poll. *)
Theorem tick_ready:
  step_ok s (next_step s) ∧ MEM a (next_step s) ∧ arrival_nonempty a ⇒
  is_ready (tick s) (arrival_fd a)
Proof
  rw [tick_def, next_step_def] \\ every_case_tac \\ gvs []
  \\ irule deliver_ready \\ simp [step_ok_sched]
QED

Theorem ticks_tick[local]:
  ∀n s. ticks n (tick s) = tick (ticks n s)
Proof
  Induct \\ simp [ticks_def]
QED

Theorem ticks_SUC:
  ticks (SUC n) s = tick (ticks n s)
Proof
  simp [ticks_def, ticks_tick]
QED

(* LEMMA data_live / accept_live: left alone, an arrival scheduled for
   round k is ready after round k (and stays ready). *)
Theorem ticks_ready:
  ∀k s a. sched_wf s ∧ MEM a (next_step (ticks k s)) ∧ arrival_nonempty a ⇒
          ∀m. k < m ⇒ is_ready (ticks m s) (arrival_fd a)
Proof
  rw [sched_wf_def]
  \\ Induct_on ‘m’ \\ rw [ticks_SUC]
  \\ Cases_on ‘k = m’ \\ gvs []
  >- (irule tick_ready \\ simp [])
  \\ irule tick_ready_mono \\ simp []
QED

(*---------------------------------------------------------------------------*)
(* Honest reads and accepts *)

(* A ready connection's read does not block. *)
Theorem ready_read_not_block:
  ALOOKUP s.conns c = SOME cn ∧ (cn.incoming ≠ [] ∨ cn.peer_closed) ⇒
  ∃d s'. sock_read c n s = SOME (SOME d, s')
Proof
  rw [sock_read_def]
QED

(* A ready listener's accept returns a connection. *)
Theorem ready_accept:
  ALOOKUP s.listeners l = SOME q ∧ q ≠ [] ⇒
  ∃c s'. sock_accept l s = SOME (SOME c, s')
Proof
  Cases_on ‘q’ \\ rw [sock_accept_def]
QED

(*---------------------------------------------------------------------------*)
(* Non-vacuity *)

Theorem deliver_sched[simp]:
  ∀as s. (deliver s as).sched = s.sched
Proof
  Induct \\ rw [deliver_def] \\ fs [GSYM deliver_def]
  \\ Cases_on ‘h’ \\ rw [deliver1_def]
QED

Theorem ticks_quiet[local]:
  ∀n s. s.sched = [||] ⇒ ticks n s = s
Proof
  Induct \\ rw [ticks_def, tick_def]
QED

Theorem quiet_tick[local]:
  every ($= []) s.sched ⇒ every ($= []) (tick s).sched ∧ next_step s = []
Proof
  rw [tick_def, next_step_def] \\ Cases_on ‘s.sched’ \\ gvs [deliver_def]
QED

(* A world with listener 3 and no connections, where in the first round a
   connection 4 arrives with the data "hi\n" followed by EOF, and nothing
   arrives after that. *)
Definition hello_world_def:
  hello_world =
    <| listeners := [(3w, [])]
     ; conns := []
     ; sched := [|[Connect 3w 4w; Data 4w [104w; 105w; 10w]; Eof 4w]|] |>
End

(* NON-VACUITY: the assumption sched_wf holds of a world in which a
   connection, data and EOF arrive. *)
Theorem hello_world_sched_wf:
  sched_wf hello_world
Proof
  rw [sched_wf_def] \\ Cases_on ‘n’
  >- simp [ticks_def, next_step_def, hello_world_def, step_ok_def,
           arrival_ok_def, deliver1_def, is_listener_def, is_conn_def,
           AFUPDKEY_def, empty_conn_def]
  \\ ‘(tick hello_world).sched = [||]’
    by simp [tick_def, hello_world_def]
  \\ simp [ticks_def, ticks_quiet, next_step_def, step_ok_def]
QED

(* NON-VACUITY: every world in which nothing ever arrives satisfies
   sched_wf (e.g. an infinite schedule of empty steps). *)
Theorem quiet_sched_wf:
  every ($= []) s.sched ⇒ sched_wf s
Proof
  rw [sched_wf_def]
  \\ ‘∀n s. every ($= []) s.sched ⇒ every ($= []) (ticks n s).sched’
    by (Induct \\ rw [ticks_def] \\ first_x_assum irule
        \\ simp [quiet_tick])
  \\ metis_tac [quiet_tick, step_ok_def]
QED

(*---------------------------------------------------------------------------*)
(* The assumption survives the program's operations *)

(* Two worlds have the same shape: the same listeners and connections,
   the same EOF flags, and the same schedule.  They may differ in pending
   queues, unread data and written data, which is all that the program's
   operations change. *)
Definition same_shape_def:
  same_shape s s' ⇔
    MAP FST s.listeners = MAP FST s'.listeners ∧
    MAP (λ(c,cn). (c, cn.peer_closed)) s.conns =
      MAP (λ(c,cn). (c, cn.peer_closed)) s'.conns ∧
    s.sched = s'.sched
End

Theorem ALOOKUP_peer_closed[local]:
  ∀conns. ALOOKUP (MAP (λ(c,cn). (c, cn.peer_closed)) conns) c =
          OPTION_MAP (λcn. cn.peer_closed) (ALOOKUP conns c)
Proof
  Induct \\ simp [FORALL_PROD] \\ rw []
QED

Theorem same_shape_lookups[local]:
  same_shape s s' ⇒
  (is_listener s fd ⇔ is_listener s' fd) ∧
  (is_conn s fd ⇔ is_conn s' fd) ∧
  OPTION_MAP (λcn. cn.peer_closed) (ALOOKUP s.conns fd) =
    OPTION_MAP (λcn. cn.peer_closed) (ALOOKUP s'.conns fd)
Proof
  rw [same_shape_def, is_listener_def, is_conn_def, ALOOKUP_NONE]
  >- (first_assum (mp_tac o Q.AP_TERM ‘MAP FST’)
      \\ simp [MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY]
      \\ simp [ETA_AX])
  \\ metis_tac [ALOOKUP_peer_closed]
QED

Theorem arrival_ok_shape[local]:
  same_shape s s' ⇒ (arrival_ok s a ⇔ arrival_ok s' a)
Proof
  strip_tac \\ drule same_shape_lookups \\ strip_tac
  \\ Cases_on ‘a’ \\ simp [arrival_ok_def]
  \\ rename1 ‘ALOOKUP _ c’
  \\ first_x_assum (qspec_then ‘c’ mp_tac)
  \\ Cases_on ‘ALOOKUP s.conns c’ \\ Cases_on ‘ALOOKUP s'.conns c’ \\ simp []
QED

Theorem MAP_FST_AFUPDKEY_eq[local]:
  MAP FST (AFUPDKEY k f al) = MAP FST al
Proof
  simp [MAP_FST_AFUPDKEY]
QED

Theorem MAP_peer_closed_AFUPDKEY[local]:
  ∀al. (∀cn. (f cn).peer_closed = cn.peer_closed) ⇒
       MAP (λ(c,cn). (c, cn.peer_closed)) (AFUPDKEY k f al) =
       MAP (λ(c,cn). (c, cn.peer_closed)) al
Proof
  Induct \\ simp [AFUPDKEY_def, FORALL_PROD] \\ rw []
QED

Theorem MAP_peer_closed_AFUPDKEY_shape[local]:
  ∀al al'. MAP (λ(c,cn). (c, cn.peer_closed)) al =
           MAP (λ(c,cn). (c, cn.peer_closed)) al' ∧
           (∀cn cn'. cn.peer_closed = cn'.peer_closed ⇒
                     (f cn).peer_closed = (f cn').peer_closed) ⇒
           MAP (λ(c,cn). (c, cn.peer_closed)) (AFUPDKEY k f al) =
           MAP (λ(c,cn). (c, cn.peer_closed)) (AFUPDKEY k f al')
Proof
  Induct \\ rpt gen_tac \\ Cases_on ‘al'’ \\ simp [AFUPDKEY_def]
  \\ PairCases_on ‘h’ \\ PairCases_on ‘h'’ \\ rw [AFUPDKEY_def] \\ gvs []
QED

Theorem MAP_FST_AFUPDKEY_shape[local]:
  ∀al al'. MAP FST al = MAP FST al' ⇒
           MAP FST (AFUPDKEY k f al) = MAP FST (AFUPDKEY k g al')
Proof
  simp [MAP_FST_AFUPDKEY]
QED

Theorem deliver1_shape[local]:
  same_shape s s' ⇒ same_shape (deliver1 s a) (deliver1 s' a)
Proof
  strip_tac \\ drule same_shape_lookups \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs [deliver1_def, same_shape_def]
  \\ rw [] \\ gvs [MAP_FST_AFUPDKEY]
  \\ irule MAP_peer_closed_AFUPDKEY_shape \\ rw []
QED

Theorem step_ok_shape[local]:
  ∀as s s'. same_shape s s' ⇒ (step_ok s as ⇔ step_ok s' as)
Proof
  Induct \\ rw [step_ok_def]
  \\ metis_tac [arrival_ok_shape, deliver1_shape]
QED

Theorem deliver_shape[local]:
  ∀as s s'. same_shape s s' ⇒ same_shape (deliver s as) (deliver s' as)
Proof
  Induct \\ rw [deliver_def] \\ fs [GSYM deliver_def]
  \\ metis_tac [deliver1_shape]
QED

Theorem tick_shape[local]:
  same_shape s s' ⇒ same_shape (tick s) (tick s')
Proof
  rw [tick_def]
  \\ ‘s'.sched = s.sched’ by fs [same_shape_def] \\ simp []
  \\ CASE_TAC \\ simp []
  \\ irule deliver_shape \\ fs [same_shape_def]
QED

Theorem ticks_shape[local]:
  ∀n s s'. same_shape s s' ⇒ same_shape (ticks n s) (ticks n s')
Proof
  Induct \\ rw [ticks_def] \\ metis_tac [tick_shape]
QED

Theorem sched_wf_shape:
  same_shape s s' ⇒ (sched_wf s ⇔ sched_wf s')
Proof
  rw [sched_wf_def] \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then ‘n’ mp_tac)
  \\ ‘same_shape (ticks n s) (ticks n s')’ by metis_tac [ticks_shape]
  \\ ‘next_step (ticks n s) = next_step (ticks n s')’
    by fs [same_shape_def, next_step_def]
  \\ metis_tac [step_ok_shape]
QED

Theorem sched_wf_tick:
  sched_wf s ⇒ sched_wf (tick s)
Proof
  rw [sched_wf_def]
  \\ first_x_assum (qspec_then ‘SUC n’ mp_tac) \\ simp [ticks_def]
QED

(* LEMMA: the assumption holds for as long as the program runs: it is
   preserved by all four operations. *)
Theorem sched_wf_preserved:
  sched_wf s ⇒
  sched_wf (SND (sock_poll fds s)) ∧
  (sock_accept l s = SOME (r, s') ⇒ sched_wf s') ∧
  (sock_read c n s = SOME (d, s') ⇒ sched_wf s') ∧
  (sock_write c bs s = SOME s' ⇒ sched_wf s')
Proof
  rw [sock_poll_def, sched_wf_tick]
  \\ irule (iffLR sched_wf_shape) \\ first_x_assum (irule_at Any)
  \\ gvs [sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs(),
          same_shape_def, MAP_FST_AFUPDKEY]
  \\ simp [MAP_peer_closed_AFUPDKEY]
QED
