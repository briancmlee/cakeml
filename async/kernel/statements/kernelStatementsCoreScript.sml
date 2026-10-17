(*
  L3 (the real kernel): the headline statements that need no CakeML
  program semantics (layer L3-00, split from kernelStatements so that the
  kernel layers can build against them; the definitions are unchanged).

  - l1pf_simple_claim (R2′, the headline: user decision Q-L3-2) and its
    optional corollary l1pf_simple_eq_claim, with their vocabulary (upto,
    conns_of, data_of, within, delays, kernel_steps, round_instant,
    fds_room, ...).  See kernelStatements' header for the claims.
  - hup_spin_bite (PROVED), the L0-model fact behind D19.

  kernelStatements imports this theory and adds the whole-program claims
  (l0_echo2_claim, l0_echo2_strong_claim, quiet_on_kernel_claim), which
  need semantics_prog and honestL0Part's l0_replay.
*)
Theory kernelStatementsCore
Ancestors
  llist ffi
  honestL0 honestL0World honestL0WorldProps honestL0Rely
  honestL1Model honestL1Refine honestL1PFModel honestL1PFRefine
  honestL1PFRound honestL1PFLive honestL1PFConnRun socketV2FFI socketV2Fair asyncCore
Libs
  preamble

(* ========================================================================
   R2′: l1pf_simple
   ======================================================================== *)

(* The arrivals of the first n steps of a schedule *)
Definition upto_def:
  upto (g : num -> arrival2 list) n = FLAT (GENLIST g n)
End

Definition conns_of_def:
  conns_of (as : arrival2 list) = LENGTH (FILTER (λa. ∃l. a = Connect2 l) as)
End

Definition data_of_def:
  data_of j (as : arrival2 list) =
    FLAT (MAP (λa. case a of Data2 j' bs => if j' = j then bs else [] | _ => []) as)
End

(* as' shows no more than as: fewer or as many connections, and per client
   a prefix of the data, and EOF only if as has it *)
Definition within_def:
  within as' as ⇔
    conns_of as' ≤ conns_of as ∧
    ∀j. data_of j as' ≼ data_of j as ∧ (MEM (Eof2 j) as' ⇒ MEM (Eof2 j) as)
End

(* g' is a delay of g, with instant map t (step n of g' happens when g has
   made t n steps): g' is never ahead of g, and misses nothing of it *)
Definition delays_def:
  delays t g' g ⇔
    (∀n. within (upto g' (SUC n)) (upto g (t n))) ∧
    (∀n. ∃n'. within (upto g n) (upto g' n'))
End

(* The channel an L0 arrival is about *)
Definition arr_chan_def:
  arr_chan (LData j bs) = SOME j ∧
  arr_chan (LEof j) = SOME j ∧
  arr_chan (LBreak j e k) = SOME j ∧
  arr_chan (LDrain j k) = SOME j ∧
  arr_chan (LConnUp j) = SOME j ∧
  arr_chan (LConnFail j e) = SOME j ∧
  arr_chan (LIncoming p) = NONE
End

(* The connections made in the first i steps (the channels are numbered
   in that order) *)
Definition sched_conns_def:
  sched_conns p (sched : num -> l0_arrival list) i =
    LENGTH (FILTER (λa. a = LIncoming p) (FLAT (GENLIST sched i)))
End

(* A prompt schedule: at most one connection per step, at most one arrival
   per channel per step, at most pf_chunk bytes each, and nothing for a
   channel in the step it connects in *)
Definition prompt_sched_def:
  prompt_sched p (sched : num -> l0_arrival list) ⇔
    ∀i. LENGTH (FILTER (λa. a = LIncoming p) (sched i)) ≤ 1 ∧
        (∀j. LENGTH (FILTER (λa. arr_chan a = SOME j) (sched i)) ≤ 1) ∧
        (∀j bs. MEM (LData j bs) (sched i) ⇒ LENGTH bs ≤ pf_chunk) ∧
        (MEM (LIncoming p) (sched i) ⇒
         ∀a. MEM a (sched i) ⇒ arr_chan a ≠ SOME (sched_conns p sched i))
End

(* A prompt server: each round polls once, and after each round's actions
   the fetched input is consumed, the accept queue is empty and every
   outbox is within hw *)
Definition prompt_server_def:
  prompt_server lfd hw ifds m w1 ⇔
    ∀n. npolls (rworld lfd hw ifds m w1 (SUC n)).hist =
        npolls (rworld lfd hw ifds m w1 n).hist + 1 ∧
        ∀rs evs w ps.
          pacts lfd (rworld lfd hw ifds m w1 n, rstate lfd hw ifds m w1 n)
                (new_actions (log_of m) (rhist lfd hw ifds m w1 n)) =
            SOME (rs, evs, (w, ps)) ⇒
          ps.acq = [] ∧ ps.inb = [] ∧ ∀f. LENGTH (outbox_of ps.b f) ≤ hw
End

(* The kernel's schedule, from w1 on, as version-2 steps (sk_of's future) *)
Definition kernel_steps_def:
  kernel_steps p lfd sched (w1 : l0world) =
    λi. conv_step p lfd (sched (npolls w1.hist + i))
End

(* The polls made by the end of round n, from w1 on: round n's instant *)
Definition round_instant_def:
  round_instant lfd hw ifds m w1 n =
    npolls (rworld lfd hw ifds m w1 (SUC n)).hist − npolls w1.hist
End

(* Room for one more fd at each round's start: fewer fds in use than the
   limit.  A bound on the connections open at once (coordinator-required
   concurrency bound, in a weaker form than "used fds + queued connections
   < limit"), not on all connections the run ever accepts *)
Definition fds_room_def:
  fds_room lfd hw ifds m w1 ⇔
    ∀n. CARD (set (l0_used (rworld lfd hw ifds m w1 n))) < w1.fd_limit
End

(* R2′, the headline (user decision Q-L3-2), for the server m (its type is the server's).  w1 is the world just
   after the listen.  Two simple-class conditions (coordinator-approved):
   sched_wf2 of the kernel's schedule (sk_of): otherwise the schedule may
   hold arrivals the world drops (data for a channel not yet connected), and
   no delay relation can hold; no emfile_drops: otherwise the world may
   reset a queued connection under EMFILE and L1 fetches an EOF the kernel's
   schedule never sent.  F1 is not a hypothesis:
   simple worlds have no transient failures.  fds_room (above): with it no
   accept fails, so every queued connection is accepted (proved:
   honestL1PFSimple's simple_F1 and conns_caught_up) *)
Definition l1pf_simple_claim_def:
  l1pf_simple_claim m ⇔
    ∀p lfd sched hw ifds w1.
      simple_v2 p lfd sched w1 ∧ sched_wf2 (sk_of p lfd sched w1) ∧
      (∀h. ¬w1.ch.emfile_drops h) ∧ winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧
      w1.chans = [] ∧ w1.open_fds = [] ∧
      run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64)) ∧
      fds_room lfd hw ifds m w1 ∧
      S1 lfd hw ifds m w1 ∧ S2 lfd hw ifds m w1 ∧ S3 lfd hw ifds m w1 ∧
      (∀f. S4 lfd hw ifds m w1 f) ⇒
      delays (round_instant lfd hw ifds m w1) (parr lfd hw ifds m w1)
             (kernel_steps p lfd sched w1)
End

(* The optional corollary (user decision Q-L3-2: the delay form is the
   headline): with a prompt schedule and a prompt server, no delay *)
Definition l1pf_simple_eq_claim_def:
  l1pf_simple_eq_claim m ⇔
    ∀p lfd sched hw ifds w1.
      simple_v2 p lfd sched w1 ∧ sched_wf2 (sk_of p lfd sched w1) ∧
      (∀h. ¬w1.ch.emfile_drops h) ∧ winv w1 ∧ w1.listeners = [(lfd, p, [])] ∧
      w1.chans = [] ∧ w1.open_fds = [] ∧
      run_ok lfd hw ifds m w1 ∧ (∀n. SND (pcm lfd hw ifds m w1 n) + 1 < dimword (:64)) ∧
      fds_room lfd hw ifds m w1 ∧
      S1 lfd hw ifds m w1 ∧ S2 lfd hw ifds m w1 ∧ S3 lfd hw ifds m w1 ∧
      (∀f. S4 lfd hw ifds m w1 f) ∧
      prompt_sched p sched ∧ prompt_server lfd hw ifds m w1 ⇒
      parr lfd hw ifds m w1 = kernel_steps p lfd sched w1
End

(* ------------------------------------------------------------------------
   hup_spin_bite (PROVED): a hung-up fd wakes every blocking poll
   ------------------------------------------------------------------------ *)

(* fd f's channel is established, its peer has closed (or it broke), and
   the world reports POLLHUP for it ([P poll] leaves POLLHUP on sockets to
   the implementation; the L0 model makes it a world choice, show_hup) *)
Definition hup_fd_def:
  hup_fd w f ⇔
    ∃j. l0_chan_of w f = SOME j ∧ ¬(EL j w.chans).connecting ∧
        ((EL j w.chans).peer_eof ∨ (EL j w.chans).broken) ∧ ∀h. w.ch.show_hup h j
End

Theorem hup_fd_deliver:
  hup_fd w f ⇒ hup_fd (l0_deliver w a) f
Proof
  rw[hup_fd_def] >> qexists_tac ‘j’ >>
  gvs[l0_chan_of_def, AllCaseEqs()] >>
  Cases_on ‘a’ >> simp[l0_deliver_def] >> rw[] >>
  gvs[upd_lchan_def, EL_LUPDATE, break_lchan_def] >> rw[] >>
  every_case_tac >> gvs[EL_APPEND1] >> rw[] >> gvs[]
QED

Theorem hup_fd_FOLDL_deliver:
  ∀as w. hup_fd w f ⇒ hup_fd (FOLDL l0_deliver w as) f
Proof
  Induct >> rw[] >> first_x_assum irule >> irule hup_fd_deliver >> simp[]
QED

Theorem hup_fd_tick:
  hup_fd w f ⇒ hup_fd (l0_tick nm w) f
Proof
  rw[l0_tick_def] >> irule hup_fd_FOLDL_deliver >>
  gvs[hup_fd_def, l0_chan_of_def, AllCaseEqs()]
QED

Theorem hup_fd_ticks:
  ∀n w. hup_fd w f ⇒ hup_fd (l0_ticks nm n w) f
Proof
  Induct >> rw[l0_ticks_def] >> first_x_assum irule >> irule hup_fd_tick >> simp[]
QED

(* Whatever events are asked for on f (none, too: a paused fd), its
   revents are not 0 *)
Theorem hup_fd_revents:
  hup_fd w f ⇒ fd_revents w (f, ev) ≠ 0w
Proof
  rw[hup_fd_def] >> simp[fd_revents_def, chan_revents_def, revents_byte_def] >>
  rw[]
QED

Theorem hup_fd_wait:
  hup_fd w f ∧ MEM (f, ev) fes ⇒ l0_wait fes w = SOME 0
Proof
  strip_tac >>
  ‘any_revents (l0_ticks «sys_poll» 0 w) fes’
    by (simp[l0_ticks_def, any_revents_def, EXISTS_MEM] >>
        qexists_tac ‘(f, ev)’ >> simp[] >> metis_tac[hup_fd_revents]) >>
  simp[l0_wait_def] >> conj_tac >- metis_tac[] >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> Cases_on ‘n’ >> gvs[]
QED

(* MAIN (the bite): in a world where f is hung up, every blocking poll that
   lists f returns at once, now and after any number of steps of time *)
Theorem hup_wakes_forever:
  hup_fd w f ∧ MEM (f, ev) fes ⇒ ∀n. l0_wait fes (l0_ticks nm n w) = SOME 0
Proof
  metis_tac[hup_fd_ticks, hup_fd_wait]
QED

(* MAIN (the bite, at the FFI): a poll call listing f never blocks forever,
   so a program that keeps a hung-up fd in its blocking set is never
   asleep_l0 there *)
Theorem hup_spin_bite:
  hup_fd w f ∧ MEM (f, ev) (poll_entries (DROP 1 conf)) ⇒
  l0_ffi_fn «sys_poll» conf bytes w ≠ SOME FFIdiverge
Proof
  strip_tac >>
  ‘hup_fd (l0_tick «sys_poll» w) f’ by metis_tac[hup_fd_tick] >>
  ‘l0_wait (poll_entries (DROP 1 conf)) (l0_tick «sys_poll» w) = SOME 0’
    by metis_tac[hup_fd_wait] >>
  simp[l0_ffi_fn_def, l0_call_def] >> rw[] >> every_case_tac >> gvs[]
QED
