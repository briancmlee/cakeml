(*
  An invariant of the socket world for a server with one listener, and
  when its socket operations succeed (shared by echo_safe and echo_live).

     sinv lfd acc s ⇔ the only listener is lfd, with queue q;
                      the fds handed out so far (acc) and the queued ones
                      are distinct, and all of them are connections.

  It holds in EchoSpec's server_world (sinv_init) and is preserved by
  arrivals (tick, sock_poll) and by every successful operation.  Under it,
  accepting on lfd never fails, and reading from or writing to a handed-out
  fd never fails (sock_do_ok): the world-side half of M3's no-misuse
  condition (srun_ok).  The distinctness gives the model's `fresh`.
*)
Theory loopSockInv
Ancestors
  alist socketWorld loopPollWorld
Libs
  preamble

Definition sinv_def:
  sinv lfd acc s ⇔
    ∃q. s.listeners = [(lfd, q)] ∧ ALL_DISTINCT (acc ++ q) ∧
        ∀c. MEM c (acc ++ q) ⇒ is_conn s c
End

(* An action the server may take, given the fds handed out so far *)
Definition action_ok_def:
  action_ok lfd acc (Accept l) = (l = lfd) ∧
  action_ok lfd acc (Read c n) = (0 < n ∧ n < 256 ** 8 ∧ MEM c acc) ∧
  action_ok lfd acc (Write c bs) = MEM c acc
End

(* The fds handed out by a list of performed actions, in order *)
Definition wacc_def:
  wacc [] = [] ∧
  wacc ((a, r) :: ps) =
    (case (a, r) of
       (Accept l, Accepted (SOME c)) => [c]
     | _ => []) ++ wacc ps
End

Theorem wacc_APPEND[simp]:
  ∀l1 l2. wacc (l1 ++ l2) = wacc l1 ++ wacc l2
Proof
  Induct >> simp[wacc_def, FORALL_PROD]
QED

Theorem action_ok_mono:
  action_ok lfd acc a ∧ set acc ⊆ set acc' ⇒ action_ok lfd acc' a
Proof
  Cases_on ‘a’ >> rw[action_ok_def, SUBSET_DEF]
QED

(* ------------------------------------------------------------------------
   The invariant
   ------------------------------------------------------------------------ *)

(* MAIN: the invariant holds in EchoSpec's initial worlds (one listener
   with nothing pending, no connections) *)
Theorem sinv_init:
  s.listeners = [(lfd, [])] ∧ s.conns = [] ⇒ sinv lfd [] s
Proof
  simp[sinv_def]
QED

Theorem is_conn_AFUPDKEY[local]:
  is_conn (s with conns := AFUPDKEY c f s.conns) x ⇔ is_conn s x
Proof
  rw[is_conn_def, AFUPDKEY_ALOOKUP] >> Cases_on ‘ALOOKUP s.conns x’ >> rw[]
QED

Theorem sinv_deliver1:
  sinv lfd acc s ⇒ sinv lfd acc (deliver1 s a)
Proof
  Cases_on ‘a’ >> simp[deliver1_def]
  >- (rw[sinv_def] >> gvs[is_listener_def, AFUPDKEY_def] >>
      gvs[ALL_DISTINCT_APPEND] >> rw[]
      >- (strip_tac >> res_tac >> gvs[])
      >- (strip_tac >> res_tac >> gvs[])
      >> gvs[is_conn_def] >> rw[] >> metis_tac[])
  >> gvs[sinv_def, is_conn_AFUPDKEY]
QED

Theorem sinv_FOLDL_deliver1[local]:
  ∀arr s. sinv lfd acc s ⇒ sinv lfd acc (FOLDL deliver1 s arr)
Proof
  Induct >> simp[] >> metis_tac[sinv_deliver1]
QED

Theorem sinv_tick:
  sinv lfd acc s ⇒ sinv lfd acc (tick s)
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def] >>
  irule sinv_FOLDL_deliver1 >> fs[sinv_def, is_conn_def] >> metis_tac[]
QED

Theorem sinv_sock_poll:
  sinv lfd acc s ⇒ sinv lfd acc (SND (sock_poll fds s))
Proof
  simp[sock_poll_def, sinv_tick]
QED

(* ------------------------------------------------------------------------
   The operations succeed
   ------------------------------------------------------------------------ *)

(* MAIN: under the invariant, every allowed action succeeds, and the
   invariant holds afterwards, with the newly handed-out fd (if any)
   added *)
Theorem sock_do_ok:
  sinv lfd acc s ∧ action_ok lfd acc a ⇒
  ∃r s'. sock_do s a = SOME (r, s') ∧ sinv lfd (acc ++ wacc [(a, r)]) s'
Proof
  Cases_on ‘a’ >> rw[action_ok_def, sock_do_def, wacc_def]
  >- (gvs[sinv_def, sock_accept_def] >> Cases_on ‘q’ >> simp[wacc_def]
      >- fs[]
      >> rename1 ‘h :: t’ >> qexists_tac ‘t’ >>
      fs[AFUPDKEY_def, is_conn_def] >>
      rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[])
  >- (‘is_conn s c’ by gvs[sinv_def] >>
      gvs[is_conn_def, sock_read_def] >>
      Cases_on ‘ALOOKUP s.conns c’ >> gvs[] >> rw[wacc_def] >>
      gvs[sinv_def, is_conn_AFUPDKEY] >> metis_tac[])
  >> ‘is_conn s c’ by gvs[sinv_def] >>
  gvs[is_conn_def, sock_write_def] >>
  Cases_on ‘ALOOKUP s.conns c’ >> gvs[wacc_def] >>
  gvs[sinv_def, is_conn_AFUPDKEY] >> metis_tac[]
QED

(* A round's actions, performed in order: if each is allowed (given the
   fds handed out before the round), they all succeed, one response
   each, and the invariant holds afterwards. *)
Theorem sock_acts_ok:
  ∀acts acc s.
    sinv lfd acc s ∧ EVERY (action_ok lfd acc) acts ⇒
    ∃rs evs s'. sock_acts s acts = SOME (rs, evs, s') ∧
                LENGTH rs = LENGTH acts ∧
                sinv lfd (acc ++ wacc (ZIP (acts, rs))) s'
Proof
  Induct >> simp[sock_acts_def, wacc_def] >> rpt strip_tac >>
  drule_all sock_do_ok >> strip_tac >> simp[] >>
  first_x_assum (qspecl_then [‘acc ++ wacc [(h, r)]’, ‘s'’] mp_tac) >>
  impl_tac
  >- (gvs[EVERY_MEM] >> rw[] >> irule action_ok_mono >>
      first_x_assum (irule_at Any) >> simp[]) >>
  strip_tac >> simp[] >> gvs[wacc_def]
QED

(* The events of a successful round: one per action *)
Theorem sock_acts_events:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ⇒
    LENGTH rs = LENGTH acts ∧ evs = MAP2 act_event acts rs
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()] >> res_tac >> simp[]
QED

(* The response of each performed action is one sock_do gives *)
Theorem sock_acts_responses:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ⇒
    ∀i. i < LENGTH acts ⇒ ∃t t'. sock_do t (EL i acts) = SOME (EL i rs, t')
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()] >>
  Cases_on ‘i’ >> gvs[] >> metis_tac[]
QED
