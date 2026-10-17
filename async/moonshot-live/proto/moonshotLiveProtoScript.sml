(*
  Moonshot liveness, MODEL-LEVEL PROTOTYPE (stage 3; design: ../README.md).
  No CakeML, no L0: one logical connection of client C → proxy P → KV K,
  with the backpressure rules of the real programs, abstract kernels, and
  weak fairness in the observed form.  Byte counts only.

  Hops (a direction of one connection): Q1 = C→P (requests on the front),
  Q2 = P→K (requests on the backend), R1 = K→P (replies on the backend),
  R2 = P→C (replies on the front).  Per hop x:
   - ob x: the sender's L1 outbox (written, not yet taken by the kernel);
   - fl x: in the kernel (taken, not yet delivered);
   - ib x: the receiver's L1 inbox (delivered, not yet read by its L2),
     at most one chunk CH.
  The kernel takes t bytes at a send ([F2]: at least one when nothing is in
  flight; otherwise any number, 0 included: a closed window), and moves up
  to CH bytes into a receiver's empty inbox only while the receiver ASKS
  (its L1 inbox is empty and its L1 does not pause the fd).

  The policies (pol):
   - Gate (the moonshot): the proxy's L1 never pauses (pol_never); its L2
     reads the front only if the backend's outbox, as of the start of the
     step (the Level it last saw), is ≤ hw, and the backend only if the
     front's outbox is ≤ hw (the credit gate);
   - PerFd (design/45 finding 1): the proxy's L1 pauses each fd on its own
     outbox, as a server's does, and its L2 reads whatever is there.
  KV is pol_self in both: it does not fetch while its outbox is > hw, and
  it answers what it has read with rb reply bytes per request byte.  The
  client writes all its requests at its first step and always reads.

  The write timeout (D23) is a PARAMETER: a Drop x label empties x's
  outbox, and may occur only where the run's history satisfies dok (any
  rule: never, after K stalled sender steps, after K timed polls, ...).

  Results:
   - P1 moonshot_drains: in every fair run, every receiver asks infinitely
     often and every hop's kernel is empty infinitely often;
   - P2 moonshot_served: with no Drop, the client eventually reads every
     reply; with drops, served or a Drop happened;
   - P3 perfd_deadlock: with PerFd there is a fair run in which the client
     never gets its replies;
   - P4 moonshot_bounded: the proxy's outboxes stay ≤ hw + CH.
*)
Theory moonshotLiveProto
Ancestors
  arithmetic combin
Libs
  BasicProvers boolSimps

Datatype:
  hop = Q1 | Q2 | R1 | R2
End

Datatype:
  pol = Gate | PerFd
End

Datatype:
  st = <| rem : num; ob : hop -> num; fl : hop -> num; ib : hop -> num;
          got : num; done : num |>
End

Datatype:
  lab = CStep num | PStep num num | KStep num | Move hop num | Drop hop
End

(*---------------------------------------------------------------------------*)
(* The model *)

(* the kernel takes t of x's outbox ([F2]: ≥ 1 if nothing is in flight) *)
Definition flush_ok_def:
  flush_ok s x t ⇔ t ≤ s.ob x ∧ (s.fl x = 0 ∧ 0 < s.ob x ⇒ 0 < t)
End

Definition flush_def:
  flush x t s = s with <| ob := (x =+ s.ob x - t) s.ob; fl := (x =+ s.fl x + t) s.fl |>
End

(* the receiver of x asks: its inbox is empty and its L1 does not pause x *)
Definition asks_def:
  asks pol hw s x ⇔
    s.ib x = 0 ∧
    case x of
    | Q1 => (pol = PerFd ⇒ s.ob R2 ≤ hw)
    | Q2 => s.ob R1 ≤ hw
    | R1 => (pol = PerFd ⇒ s.ob Q2 ≤ hw)
    | R2 => T
End

(* the proxy's L2 may read x (the gate, on the start-of-step Levels) *)
Definition prd_def:
  prd pol hw s x ⇔ pol = Gate ⇒ s.ob (if x = Q1 then Q2 else R2) ≤ hw
End

Definition step_def:
  (step pol hw CH rb s (CStep t) s' ⇔
     let s1 = s with <| rem := 0; ob := (Q1 =+ s.ob Q1 + s.rem) s.ob |> in
       flush_ok s1 Q1 t ∧
       s' = (flush Q1 t s1) with <| got := s.got + s.ib R2; ib := (R2 =+ 0) s.ib |>) ∧
  (step pol hw CH rb s (PStep t2 t4) s' ⇔
     let g1 = prd pol hw s Q1; g2 = prd pol hw s R1;
         s1 = flush R2 t4 (flush Q2 t2 s) in
       flush_ok s Q2 t2 ∧ flush_ok s R2 t4 ∧
       s' = s1 with <| ob := (Q2 =+ s1.ob Q2 + (if g1 then s.ib Q1 else 0))
                              ((R2 =+ s1.ob R2 + (if g2 then s.ib R1 else 0)) s1.ob);
                       ib := (Q1 =+ (if g1 then 0 else s.ib Q1))
                              ((R1 =+ (if g2 then 0 else s.ib R1)) s.ib) |>) ∧
  (step pol hw CH rb s (KStep t) s' ⇔
     flush_ok s R1 t ∧
     let s1 = flush R1 t s in
       s' = s1 with <| done := s.done + s.ib Q2;
                       ob := (R1 =+ s1.ob R1 + rb * s.ib Q2) s1.ob;
                       ib := (Q2 =+ 0) s.ib |>) ∧
  (step pol hw CH rb s (Move x n) s' ⇔
     asks pol hw s x ∧ 0 < n ∧ n ≤ s.fl x ∧ n ≤ CH ∧
     s' = s with <| fl := (x =+ s.fl x - n) s.fl; ib := (x =+ n) s.ib |>) ∧
  (step pol hw CH rb s (Drop x) s' ⇔ s' = s with ob := (x =+ 0) s.ob)
End

Definition init_def:
  init R = <| rem := R; ob := K 0; fl := K 0; ib := K 0; got := 0; done := 0 |>
End

Definition run_def:
  run pol hw CH rb R dok (ss : num -> st) (ls : num -> lab) ⇔
    ss 0 = init R ∧
    ∀n. step pol hw CH rb (ss n) (ls n) (ss (SUC n)) ∧
        ∀x. ls n = Drop x ⇒ dok ss ls n x
End

(*---------------------------------------------------------------------------*)
(* Fairness, in the observed weak form *)

Definition io_def:
  io (P : num -> bool) ⇔ ∀m. ∃n. m ≤ n ∧ P n
End

Definition is_c_def:
  is_c l ⇔ ∃t. l = CStep t
End

Definition is_p_def:
  is_p l ⇔ ∃t2 t4. l = PStep t2 t4
End

Definition is_k_def:
  is_k l ⇔ ∃t. l = KStep t
End

(* every process steps infinitely often (each is always enabled) *)
Definition sched_def:
  sched (ls : num -> lab) ⇔
    io (λn. is_c (ls n)) ∧ io (λn. is_p (ls n)) ∧ io (λn. is_k (ls n))
End

(* delivery to a receiver that asks infinitely often: its hop's kernel is
   not non-empty for ever *)
Definition kfair_def:
  kfair pol hw (ss : num -> st) ⇔
    ∀x. io (λn. asks pol hw (ss n) x) ⇒ ∀m. ∃n. m ≤ n ∧ (ss n).fl x = 0
End

(* the sender of each hop *)
Definition sender_def:
  sender Q1 = is_c ∧ sender Q2 = is_p ∧ sender R2 = is_p ∧ sender R1 = is_k
End

(*---------------------------------------------------------------------------*)
(* Generic lemmas about runs *)

Theorem io_mono:
  io P ∧ (∀n. P n ⇒ Q n) ⇒ io Q
Proof
  rw[io_def] >> metis_tac[]
QED

(* the first n ≥ m with P n *)
Theorem io_first:
  io P ⇒ ∀m. ∃n. m ≤ n ∧ P n ∧ ∀k. m ≤ k ∧ k < n ⇒ ¬P k
Proof
  rw[io_def] >> first_x_assum (qspec_then ‘m’ strip_assume_tac) >>
  qspec_then ‘λk. m ≤ k ∧ P k’ mp_tac WOP >> simp[] >>
  impl_tac >- metis_tac[] >> strip_tac >> qexists_tac ‘n'’ >> rw[] >>
  CCONTR_TAC >> fs[] >> res_tac >> fs[]
QED

(* a property kept by every step that is not a P-step holds at the next
   P-step *)
Theorem keep_until_lem[local]:
  ∀d. Q (ss n0) ∧
      (∀k. n0 ≤ k ∧ k < n0 + d ⇒ ¬P (ls k)) ∧
      (∀k. n0 ≤ k ∧ ¬P (ls k) ∧ Q (ss k) ⇒ Q (ss (SUC k))) ⇒
      Q (ss (n0 + d))
Proof
  Induct >> rw[] >> fs[ADD_CLAUSES] >> first_x_assum irule >> simp[]
QED

Theorem keep_until:
  n0 ≤ n1 ∧ Q (ss n0) ∧
  (∀k. n0 ≤ k ∧ k < n1 ⇒ ¬P (ls k)) ∧
  (∀k. n0 ≤ k ∧ ¬P (ls k) ∧ Q (ss k) ⇒ Q (ss (SUC k))) ⇒
  Q (ss n1)
Proof
  strip_tac >> qspec_then ‘n1 - n0’ mp_tac keep_until_lem >> simp[] >>
  disch_then irule >> simp[] >> qexistsl_tac [‘P’, ‘ls’] >> simp[]
QED

Theorem keep_until_inst:
  ∀Q P. n0 ≤ n1 ∧ Q (ss n0) ∧
  (∀k. n0 ≤ k ∧ k < n1 ⇒ ¬P (ls k)) ∧
  (∀k. n0 ≤ k ∧ ¬P (ls k) ∧ Q (ss k) ⇒ Q (ss (SUC k))) ⇒
  Q (ss n1)
Proof
  metis_tac[keep_until]
QED

(* a natural-number sequence that never increases cannot fall infinitely
   often *)
Theorem no_infinite_descent:
  ∀f m. (∀n. m ≤ n ⇒ f (SUC n) ≤ f n) ∧ io (λn. m ≤ n ∧ f (SUC n) < f n) ⇒ F
Proof
  rpt strip_tac >>
  ‘∀d. ∃n. m ≤ n ∧ f n + d ≤ f m’ suffices_by
    (disch_then (qspec_then ‘SUC (f m)’ strip_assume_tac) >> fs[]) >>
  Induct >- (qexists_tac ‘m’ >> simp[]) >>
  fs[] >> fs[io_def] >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  qexists_tac ‘SUC n'’ >> simp[] >>
  ‘∀k. n ≤ k ⇒ f k ≤ f n’ suffices_by (disch_then (qspec_then ‘n'’ mp_tac) >> simp[]) >>
  Induct_on ‘k’ >> rw[] >> Cases_on ‘n = SUC k’ >> fs[] >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]
QED

Theorem not_io:
  ¬io P ⇔ ∃m. ∀n. m ≤ n ⇒ ¬P n
Proof
  rw[io_def] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* One-step facts *)

Theorem step_cases[local] = SIMP_RULE (srw_ss()) [LET_THM] step_def

val stepss = [step_cases, flush_def, flush_ok_def, combinTheory.APPLY_UPDATE_THM, prd_def]

(* fl x = 0 is kept by every step but x's sender's *)
Theorem fl_zero_keep:
  step pol hw CH rb s l s' ∧ s.fl x = 0 ∧ ¬sender x l ⇒ s'.fl x = 0
Proof
  Cases_on ‘l’ >> Cases_on ‘x’ >> rw stepss >> fs[sender_def, is_c_def, is_p_def, is_k_def] >>
  rw[] >> fs[]
QED

(* the receiver's inbox is emptied by its reader, or kept *)
Theorem ib_keep_pos:
  step pol hw CH rb s l s' ∧ 0 < s.ib x ⇒ s'.ib x = s.ib x ∨
    (x = Q1 ∧ is_p l ∧ prd pol hw s Q1) ∨ (x = R1 ∧ is_p l ∧ prd pol hw s R1) ∨
    (x = Q2 ∧ is_k l) ∨ (x = R2 ∧ is_c l)
Proof
  Cases_on ‘l’ >> Cases_on ‘x’ >> rw stepss >> fs[is_c_def, is_p_def, is_k_def, asks_def]
QED

(* the outboxes the gate guards do not grow while over hw *)
Theorem ob_gated_nogrow:
  step Gate hw CH rb s l s' ∧ (x = Q2 ∨ x = R2) ∧ hw < s.ob x ⇒ s'.ob x ≤ s.ob x
Proof
  Cases_on ‘l’ >> rw stepss >> rw[]
QED

(* KV's outbox grows only by replies to what it has read *)
Theorem ob_r1_nogrow:
  step pol hw CH rb s l s' ∧ s.ib Q2 = 0 ⇒ s'.ob R1 ≤ s.ob R1
Proof
  Cases_on ‘l’ >> rw stepss >> rw[]
QED

(* the sender's step with nothing in flight takes a byte; with no growth
   that is a fall *)
Theorem sender_falls:
  step pol hw CH rb s l s' ∧ sender x l ∧ s.fl x = 0 ∧ 0 < s.ob x ∧
  (x = Q2 ⇒ ¬prd pol hw s Q1 ∨ s.ib Q1 = 0) ∧ (x = R2 ⇒ ¬prd pol hw s R1 ∨ s.ib R1 = 0) ∧
  (x = R1 ⇒ s.ib Q2 = 0) ∧ (x = Q1 ⇒ s.rem = 0) ⇒
  s'.ob x < s.ob x
Proof
  Cases_on ‘l’ >> Cases_on ‘x’ >> fs[sender_def, is_c_def, is_p_def, is_k_def] >>
  rw stepss >> rw[] >> fs[]
QED

Theorem ib_q2_zero_keep:
  step pol hw CH rb s l s' ∧ s.ib Q2 = 0 ∧ ¬asks pol hw s Q2 ⇒ s'.ib Q2 = 0
Proof
  Cases_on ‘l’ >> rw stepss >> rw[] >> fs[asks_def] >> rw[] >> fs[]
QED

Theorem ib_q2_after_k:
  step pol hw CH rb s l s' ∧ is_k l ⇒ s'.ib Q2 = 0
Proof
  rw[is_k_def] >> fs stepss >> rw[]
QED

Theorem ib_r2_after_c:
  step pol hw CH rb s l s' ∧ is_c l ⇒ s'.ib R2 = 0
Proof
  rw[is_c_def] >> fs stepss >> rw[]
QED

(* the gate's input: the outbox x reads into, kept ≤ hw by any step but a
   proxy step *)
Theorem ob_low_keep:
  step pol hw CH rb s l s' ∧ (x = Q2 ∨ x = R2) ∧ s.ob x ≤ hw ∧ ¬is_p l ⇒ s'.ob x ≤ hw
Proof
  Cases_on ‘l’ >> rw stepss >> fs[is_p_def] >> rw[]
QED

Theorem ob_r1_low_keep:
  step pol hw CH rb s l s' ∧ s.ob R1 ≤ hw ∧ ¬is_k l ⇒ s'.ob R1 ≤ hw
Proof
  Cases_on ‘l’ >> rw stepss >> fs[is_k_def] >> rw[]
QED

Theorem proxy_reads:
  step Gate hw CH rb s l s' ∧ is_p l ∧ (x = Q1 ∨ x = R1) ∧
  s.ob (if x = Q1 then Q2 else R2) ≤ hw ⇒ s'.ib x = 0
Proof
  rw[is_p_def] >> fs stepss >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* P1: the drains induction *)

Theorem run_step:
  run pol hw CH rb R dok ss ls ⇒ step pol hw CH rb (ss n) (ls n) (ss (SUC n))
Proof
  rw[run_def]
QED

(* asks infinitely often ⇒ the hop's kernel is empty infinitely often *)
Theorem fl_zero_io:
  kfair pol hw ss ∧ io (λn. asks pol hw (ss n) x) ⇒ io (λn. (ss n).fl x = 0)
Proof
  rpt strip_tac >> fs[kfair_def] >> first_x_assum drule >> simp[io_def]
QED

(* an outbox whose kernel is empty infinitely often, and that does not grow
   while over hw (from some point on, given that it stays over hw), is ≤ hw
   infinitely often *)
Theorem ob_low_io:
  run pol hw CH rb R dok ss ls ∧ io (λn. sender x (ls n)) ∧ io (λn. (ss n).fl x = 0) ∧
  (∀m. (∀n. m ≤ n ⇒ h < (ss n).ob x) ⇒
       ∃m'. m ≤ m' ∧ ∀n. m' ≤ n ⇒
            (ss (SUC n)).ob x ≤ (ss n).ob x ∧
            (sender x (ls n) ∧ (ss n).fl x = 0 ⇒ (ss (SUC n)).ob x < (ss n).ob x)) ⇒
  io (λn. (ss n).ob x ≤ h)
Proof
  rpt strip_tac >> CCONTR_TAC >>
  ‘∃m. ∀n. m ≤ n ⇒ h < (ss n).ob x’ by (fs[io_def] >> metis_tac[NOT_LESS_EQUAL]) >>
  qpat_x_assum ‘∀m. (∀n. _) ⇒ _’ drule >> strip_tac >>
  qspecl_then [‘λn. (ss n).ob x’, ‘m'’] mp_tac no_infinite_descent >>
  simp[io_def] >> rw[] >>
  qpat_x_assum ‘io (λn. (ss n).fl x = 0)’ mp_tac >> simp[io_def] >>
  disch_then (qspec_then ‘m' + m''’ strip_assume_tac) >>
  qpat_x_assum ‘io (λn. sender x (ls n))’ assume_tac >>
  drule io_first >> disch_then (qspec_then ‘n’ strip_assume_tac) >> fs[] >>
  qexists_tac ‘n'’ >> simp[] >>
  ‘(ss n').fl x = 0’ by
    (qspecl_then [‘λs. s.fl x = 0’, ‘sender x’] mp_tac
       (keep_until_inst |> Q.INST [‘n1’ |-> ‘n'’, ‘n0’ |-> ‘n’]) >>
     simp[] >> disch_then irule >> rw[] >>
     irule fl_zero_keep >> metis_tac[run_step]) >>
  qpat_x_assum ‘∀n. m' ≤ n ⇒ _’ (qspec_then ‘n'’ mp_tac) >> simp[]
QED

(* R2: the client reads every step it takes *)
Theorem asks_r2_io:
  run pol hw CH rb R dok ss ls ∧ sched ls ⇒ io (λn. asks pol hw (ss n) R2)
Proof
  strip_tac >> ‘io (λn. is_c (ls n))’ by fs[sched_def] >>
  fs[io_def, asks_def] >> rw[] >>
  first_x_assum (qspec_then ‘m’ strip_assume_tac) >>
  qexists_tac ‘SUC n’ >> simp[] >> irule ib_r2_after_c >> metis_tac[run_step]
QED

Theorem ob_r2_low_io:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒ io (λn. (ss n).ob R2 ≤ hw)
Proof
  strip_tac >>
  ‘io (λn. sender R2 (ls n))’ by fs[sched_def, sender_def] >>
  ‘io (λn. asks Gate hw (ss n) R2)’ by metis_tac[asks_r2_io] >>
  ‘io (λn. (ss n).fl R2 = 0)’ by (drule_all fl_zero_io >> simp[]) >>
  ‘(∀m. (∀n. m ≤ n ⇒ hw < (ss n).ob R2) ⇒
         ∃m'. m ≤ m' ∧ ∀n. m' ≤ n ⇒
              (ss (SUC n)).ob R2 ≤ (ss n).ob R2 ∧
              (sender R2 (ls n) ∧ (ss n).fl R2 = 0 ⇒ (ss (SUC n)).ob R2 < (ss n).ob R2))’ by
    (rw[] >> qexists_tac ‘m’ >> rw[]
      >- (irule ob_gated_nogrow >> simp[] >> metis_tac[run_step])
      >- (‘step Gate hw CH rb (ss n) (ls n) (ss (SUC n))’ by metis_tac[run_step] >>
          ‘hw < (ss n).ob R2’ by simp[] >>
          drule sender_falls >> disch_then (qspec_then ‘R2’ mp_tac) >> simp[prd_def])) >>
  drule_all ob_low_io >> simp[]
QED

(* R1, the proxy's backend: read whenever the gate is open *)
Theorem asks_r1_io:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒ io (λn. asks Gate hw (ss n) R1)
Proof
  strip_tac >> simp[asks_def] >> CCONTR_TAC >>
  ‘∃m. ∀n. m ≤ n ⇒ (ss n).ib R1 ≠ 0’ by (fs[io_def] >> metis_tac[]) >>
  ‘io (λn. (ss n).ob R2 ≤ hw)’ by metis_tac[ob_r2_low_io] >>
  ‘io (λn. is_p (ls n))’ by fs[sched_def] >>
  ‘∃n. m ≤ n ∧ (ss n).ob R2 ≤ hw’ by
    (qpat_x_assum ‘io (λn. (ss n).ob R2 ≤ hw)’ mp_tac >> rw[io_def] >> metis_tac[]) >>
  qpat_x_assum ‘io (λn. is_p (ls n))’ assume_tac >>
  drule io_first >> disch_then (qspec_then ‘n’ strip_assume_tac) >> fs[] >>
  ‘(ss n').ob R2 ≤ hw’ by
    (qspecl_then [‘λs. s.ob R2 ≤ hw’, ‘is_p’] mp_tac
       (keep_until_inst |> Q.INST [‘n1’ |-> ‘n'’, ‘n0’ |-> ‘n’]) >>
     simp[] >> disch_then irule >> rw[] >> fs[] >>
     irule ob_low_keep >> metis_tac[run_step]) >>
  ‘(ss (SUC n')).ib R1 = 0’ by (irule proxy_reads >> simp[] >> metis_tac[run_step]) >>
  qpat_x_assum ‘∀n. m ≤ n ⇒ (ss n).ib R1 ≠ 0’ (qspec_then ‘SUC n'’ mp_tac) >> simp[]
QED

(* R1, KV's outbox: once over hw for good, KV is paused, so it reads
   nothing new and only drains *)
Theorem ob_r1_low_io:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒ io (λn. (ss n).ob R1 ≤ hw)
Proof
  strip_tac >>
  ‘io (λn. sender R1 (ls n))’ by fs[sched_def, sender_def] >>
  ‘io (λn. asks Gate hw (ss n) R1)’ by metis_tac[asks_r1_io] >>
  ‘io (λn. (ss n).fl R1 = 0)’ by (drule_all fl_zero_io >> simp[]) >>
  ‘(∀m. (∀n. m ≤ n ⇒ hw < (ss n).ob R1) ⇒
         ∃m'. m ≤ m' ∧ ∀n. m' ≤ n ⇒
              (ss (SUC n)).ob R1 ≤ (ss n).ob R1 ∧
              (sender R1 (ls n) ∧ (ss n).fl R1 = 0 ⇒ (ss (SUC n)).ob R1 < (ss n).ob R1))’ by
    (rw[] >>
      ‘io (λn. is_k (ls n))’ by fs[sched_def] >>
      fs[io_def] >> first_x_assum (qspec_then ‘m’ strip_assume_tac) >>
      qexists_tac ‘SUC n’ >> simp[] >>
      ‘∀k. SUC n ≤ k ⇒ (ss k).ib Q2 = 0’ by
        (Induct >> rw[] >> Cases_on ‘SUC n = SUC k’
         >- (fs[] >> irule ib_q2_after_k >> metis_tac[run_step]) >>
         ‘SUC n ≤ k ∧ m ≤ k’ by simp[] >> fs[] >>
         ‘¬asks Gate hw (ss k) Q2’ by (simp[asks_def] >> res_tac >> simp[]) >>
         metis_tac[ib_q2_zero_keep, run_step]) >>
      rw[]
      >- (irule ob_r1_nogrow >> metis_tac[run_step])
      >- (‘step Gate hw CH rb (ss n') (ls n') (ss (SUC n'))’ by metis_tac[run_step] >>
          ‘hw < (ss n').ob R1 ∧ (ss n').ib Q2 = 0’ by simp[] >>
          drule sender_falls >> disch_then (qspec_then ‘R1’ mp_tac) >> simp[prd_def])) >>
  drule_all ob_low_io >> simp[]
QED

(* Q2: KV asks (empty inbox, outbox ≤ hw) infinitely often *)
Theorem asks_q2_io:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒ io (λn. asks Gate hw (ss n) Q2)
Proof
  strip_tac >> CCONTR_TAC >>
  ‘∃m. ∀n. m ≤ n ⇒ ¬asks Gate hw (ss n) Q2’ by (fs[io_def] >> metis_tac[]) >>
  ‘io (λn. is_k (ls n))’ by fs[sched_def] >>
  ‘io (λn. (ss n).ob R1 ≤ hw)’ by metis_tac[ob_r1_low_io] >>
  ‘∃n. m ≤ n ∧ is_k (ls n)’ by
    (qpat_x_assum ‘io (λn. is_k (ls n))’ mp_tac >> rw[io_def] >> metis_tac[]) >>
  ‘∀k. SUC n ≤ k ⇒ (ss k).ib Q2 = 0’ by
    (Induct >> rw[] >> Cases_on ‘SUC n = SUC k’
     >- (fs[] >> irule ib_q2_after_k >> metis_tac[run_step]) >>
     ‘SUC n ≤ k ∧ m ≤ k’ by simp[] >> fs[] >>
     metis_tac[ib_q2_zero_keep, run_step]) >>
  ‘∃n'. SUC n ≤ n' ∧ (ss n').ob R1 ≤ hw’ by
    (qpat_x_assum ‘io (λn. (ss n).ob R1 ≤ hw)’ mp_tac >> rw[io_def] >> metis_tac[]) >>
  ‘m ≤ n'’ by simp[] >>
  qpat_x_assum ‘∀n. m ≤ n ⇒ ¬asks _ _ _ _’ (qspec_then ‘n'’ mp_tac) >> simp[asks_def]
QED

Theorem ob_q2_low_io:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒ io (λn. (ss n).ob Q2 ≤ hw)
Proof
  strip_tac >>
  ‘io (λn. sender Q2 (ls n))’ by fs[sched_def, sender_def] >>
  ‘io (λn. asks Gate hw (ss n) Q2)’ by metis_tac[asks_q2_io] >>
  ‘io (λn. (ss n).fl Q2 = 0)’ by (drule_all fl_zero_io >> simp[]) >>
  ‘(∀m. (∀n. m ≤ n ⇒ hw < (ss n).ob Q2) ⇒
         ∃m'. m ≤ m' ∧ ∀n. m' ≤ n ⇒
              (ss (SUC n)).ob Q2 ≤ (ss n).ob Q2 ∧
              (sender Q2 (ls n) ∧ (ss n).fl Q2 = 0 ⇒ (ss (SUC n)).ob Q2 < (ss n).ob Q2))’ by
    (rw[] >> qexists_tac ‘m’ >> rw[]
      >- (irule ob_gated_nogrow >> simp[] >> metis_tac[run_step])
      >- (‘step Gate hw CH rb (ss n) (ls n) (ss (SUC n))’ by metis_tac[run_step] >>
          ‘hw < (ss n).ob Q2’ by simp[] >>
          drule sender_falls >> disch_then (qspec_then ‘Q2’ mp_tac) >> simp[prd_def])) >>
  drule_all ob_low_io >> simp[]
QED

Theorem asks_q1_io:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒ io (λn. asks Gate hw (ss n) Q1)
Proof
  strip_tac >> simp[asks_def] >> CCONTR_TAC >>
  ‘∃m. ∀n. m ≤ n ⇒ (ss n).ib Q1 ≠ 0’ by (fs[io_def] >> metis_tac[]) >>
  ‘io (λn. (ss n).ob Q2 ≤ hw)’ by metis_tac[ob_q2_low_io] >>
  ‘io (λn. is_p (ls n))’ by fs[sched_def] >>
  ‘∃n. m ≤ n ∧ (ss n).ob Q2 ≤ hw’ by
    (qpat_x_assum ‘io (λn. (ss n).ob Q2 ≤ hw)’ mp_tac >> rw[io_def] >> metis_tac[]) >>
  qpat_x_assum ‘io (λn. is_p (ls n))’ assume_tac >>
  drule io_first >> disch_then (qspec_then ‘n’ strip_assume_tac) >> fs[] >>
  ‘(ss n').ob Q2 ≤ hw’ by
    (qspecl_then [‘λs. s.ob Q2 ≤ hw’, ‘is_p’] mp_tac
       (keep_until_inst |> Q.INST [‘n1’ |-> ‘n'’, ‘n0’ |-> ‘n’]) >>
     simp[] >> disch_then irule >> rw[] >> fs[] >>
     irule ob_low_keep >> metis_tac[run_step]) >>
  ‘(ss (SUC n')).ib Q1 = 0’ by (irule proxy_reads >> simp[] >> metis_tac[run_step]) >>
  qpat_x_assum ‘∀n. m ≤ n ⇒ (ss n).ib Q1 ≠ 0’ (qspec_then ‘SUC n'’ mp_tac) >> simp[]
QED

(* P1: every receiver asks infinitely often, and every hop's kernel is
   empty infinitely often (each process's `drains`) *)
Theorem moonshot_drains:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒
  ∀x. io (λn. asks Gate hw (ss n) x) ∧ io (λn. (ss n).fl x = 0)
Proof
  strip_tac >>
  ‘∀x. io (λn. asks Gate hw (ss n) x)’ by
    (Cases >> metis_tac[asks_q1_io, asks_q2_io, asks_r1_io, asks_r2_io]) >>
  metis_tac[fl_zero_io]
QED

(*---------------------------------------------------------------------------*)
(* P4: the proxy's buffers are bounded *)

Definition bnd_def:
  bnd hw CH s ⇔ (∀x. s.ib x ≤ CH) ∧ s.ob Q2 ≤ hw + CH ∧ s.ob R2 ≤ hw + CH
End

Theorem bnd_step:
  step Gate hw CH rb s l s' ∧ bnd hw CH s ⇒ bnd hw CH s'
Proof
  strip_tac >> fs[bnd_def] >> ‘s.ib Q1 ≤ CH ∧ s.ib R1 ≤ CH’ by simp[] >>
  Cases_on ‘l’ >> fs stepss >> rw[] >> fs[] >> rw[] >> fs[]
QED

Theorem moonshot_bounded:
  run Gate hw CH rb R dok ss ls ⇒ ∀n. bnd hw CH (ss n)
Proof
  strip_tac >> Induct >- fs[run_def, init_def, bnd_def] >>
  metis_tac[bnd_step, run_step]
QED

(*---------------------------------------------------------------------------*)
(* P2: every reply is read *)

(* conservation, while nothing is dropped *)
Definition cons_def:
  cons R rb s ⇔
    s.rem + s.ob Q1 + s.fl Q1 + s.ib Q1 + s.ob Q2 + s.fl Q2 + s.ib Q2 + s.done = R ∧
    rb * s.done = s.ob R1 + s.fl R1 + s.ib R1 + s.ob R2 + s.fl R2 + s.ib R2 + s.got
End

Theorem cons_step:
  step pol hw CH rb s l s' ∧ (∀x. l ≠ Drop x) ∧ cons R rb s ⇒ cons R rb s'
Proof
  Cases_on ‘l’ >> rw (cons_def :: stepss) >> fs[] >>
  rw[LEFT_ADD_DISTRIB] >> fs[asks_def]
QED

(* a count that never grows (from m) and is 0 infinitely often is 0 for
   good *)
Theorem ez_of_io:
  (∀n. m ≤ n ⇒ g (SUC n) ≤ (g n : num)) ∧ io (λn. g n = 0) ⇒ ∃m'. ∀n. m' ≤ n ⇒ g n = 0
Proof
  rw[io_def] >> first_x_assum (qspec_then ‘m’ strip_assume_tac) >>
  qexists_tac ‘n’ >> Induct >> rw[] >> Cases_on ‘n = SUC n'’ >> fs[] >>
  ‘n ≤ n'’ by simp[] >> fs[] >> first_x_assum (qspec_then ‘n'’ mp_tac) >> simp[]
QED

(* an outbox that never grows (from m) and falls at every sender step
   with its kernel empty is 0 for good *)
Theorem ez_ob:
  run pol hw CH rb R dok ss ls ∧ io (λn. sender x (ls n)) ∧ io (λn. (ss n).fl x = 0) ∧
  (∀n. m ≤ n ⇒ (ss (SUC n)).ob x ≤ (ss n).ob x ∧
                (sender x (ls n) ∧ (ss n).fl x = 0 ∧ 0 < (ss n).ob x ⇒
                 (ss (SUC n)).ob x < (ss n).ob x)) ⇒
  ∃m'. ∀n. m' ≤ n ⇒ (ss n).ob x = 0
Proof
  strip_tac >>
  ‘(∀m'. (∀n. m' ≤ n ⇒ 0 < (ss n).ob x) ⇒
         ∃m''. m' ≤ m'' ∧ ∀n. m'' ≤ n ⇒
              (ss (SUC n)).ob x ≤ (ss n).ob x ∧
              (sender x (ls n) ∧ (ss n).fl x = 0 ⇒ (ss (SUC n)).ob x < (ss n).ob x))’ by
    (rw[] >> qexists_tac ‘m + m'’ >> rw[]) >>
  ‘io (λn. (ss n).ob x ≤ 0)’ by (drule_all ob_low_io >> simp[]) >>
  irule (ez_of_io |> Q.INST [‘g’ |-> ‘λn. (ss n).ob x’] |> SIMP_RULE std_ss []) >>
  conj_tac >- (qexists_tac ‘m’ >> fs[]) >> fs[]
QED

(* step facts for the drain: nothing in, nothing grows *)
Theorem fl_nogrow:
  step pol hw CH rb s l s' ∧ s.ob x = 0 ∧ (x = Q1 ⇒ s.rem = 0) ⇒ s'.fl x ≤ s.fl x
Proof
  Cases_on ‘l’ >> Cases_on ‘x’ >> rw stepss >> rw[]
QED

Theorem ib_nogrow:
  step pol hw CH rb s l s' ∧ s.fl x = 0 ⇒ s'.ib x ≤ s.ib x
Proof
  Cases_on ‘l’ >> Cases_on ‘x’ >> rw stepss >> rw[]
QED

Theorem ob_nogrow:
  step pol hw CH rb s l s' ∧
  (x = Q1 ⇒ s.rem = 0) ∧ (x = Q2 ⇒ s.ib Q1 = 0) ∧ (x = R1 ⇒ s.ib Q2 = 0) ∧
  (x = R2 ⇒ s.ib R1 = 0) ⇒
  s'.ob x ≤ s.ob x
Proof
  Cases_on ‘l’ >> Cases_on ‘x’ >> rw stepss >> rw[]
QED

Theorem rem_nogrow:
  step pol hw CH rb s l s' ⇒ s'.rem ≤ s.rem ∧ (is_c l ⇒ s'.rem = 0)
Proof
  Cases_on ‘l’ >> rw (is_c_def :: stepss)
QED

Theorem asks_ib:
  asks pol hw s x ⇒ s.ib x = 0
Proof
  rw[asks_def]
QED

(* the stages of the drain, each from "upstream is quiet for good" *)
Theorem ez_stage_ob:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ∧
  (∀n. m ≤ n ⇒ (x = Q1 ⇒ (ss n).rem = 0) ∧ (x = Q2 ⇒ (ss n).ib Q1 = 0) ∧
                (x = R1 ⇒ (ss n).ib Q2 = 0) ∧ (x = R2 ⇒ (ss n).ib R1 = 0)) ⇒
  ∃m'. ∀n. m' ≤ n ⇒ (ss n).ob x = 0
Proof
  strip_tac >>
  ‘io (λn. sender x (ls n))’ by (Cases_on ‘x’ >> fs[sched_def, sender_def]) >>
  ‘io (λn. (ss n).fl x = 0)’ by metis_tac[moonshot_drains] >>
  ‘∀n. m ≤ n ⇒ (ss (SUC n)).ob x ≤ (ss n).ob x ∧
                (sender x (ls n) ∧ (ss n).fl x = 0 ∧ 0 < (ss n).ob x ⇒
                 (ss (SUC n)).ob x < (ss n).ob x)’ by
    (rpt gen_tac >> strip_tac >>
     ‘step Gate hw CH rb (ss n) (ls n) (ss (SUC n))’ by metis_tac[run_step] >>
     first_x_assum drule >> strip_tac >> conj_tac
     >- (irule ob_nogrow >> metis_tac[])
     >> strip_tac >> drule sender_falls >> disch_then (qspec_then ‘x’ mp_tac) >> simp[] >>
     disch_then irule >> Cases_on ‘x’ >> fs[]) >>
  drule_all ez_ob >> simp[]
QED

Theorem ez_stage_fl:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ∧
  (∀n. m ≤ n ⇒ (ss n).ob x = 0 ∧ (x = Q1 ⇒ (ss n).rem = 0)) ⇒
  ∃m'. ∀n. m' ≤ n ⇒ (ss n).fl x = 0
Proof
  strip_tac >> irule (ez_of_io |> Q.INST [‘g’ |-> ‘λn. (ss n).fl x’] |> SIMP_RULE std_ss []) >>
  conj_tac
  >- (qexists_tac ‘m’ >> rw[] >> irule fl_nogrow >> metis_tac[run_step])
  >> metis_tac[moonshot_drains]
QED

Theorem ez_stage_ib:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ∧
  (∀n. m ≤ n ⇒ (ss n).fl x = 0) ⇒
  ∃m'. ∀n. m' ≤ n ⇒ (ss n).ib x = 0
Proof
  strip_tac >> irule (ez_of_io |> Q.INST [‘g’ |-> ‘λn. (ss n).ib x’] |> SIMP_RULE std_ss []) >>
  conj_tac
  >- (qexists_tac ‘m’ >> rw[] >> irule ib_nogrow >> metis_tac[run_step])
  >> ‘io (λn. asks Gate hw (ss n) x)’ by metis_tac[moonshot_drains] >>
  fs[io_def] >> metis_tac[asks_ib]
QED

Theorem ez_rem:
  run pol hw CH rb R dok ss ls ∧ sched ls ⇒ ∃m. ∀n. m ≤ n ⇒ (ss n).rem = 0
Proof
  strip_tac >> irule (ez_of_io |> Q.INST [‘g’ |-> ‘λn. (ss n).rem’] |> SIMP_RULE std_ss []) >>
  conj_tac >- (qexists_tac ‘0’ >> metis_tac[rem_nogrow, run_step]) >>
  ‘io (λn. is_c (ls n))’ by fs[sched_def] >>
  fs[io_def] >> rw[] >> first_x_assum (qspec_then ‘m’ strip_assume_tac) >>
  qexists_tac ‘SUC n’ >> simp[] >> metis_tac[rem_nogrow, run_step]
QED

(* everything upstream of x, and x itself, is empty for good *)
Theorem ez_all:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒
  ∃m. ∀n. m ≤ n ⇒ (ss n).rem = 0 ∧
                  ∀x. (ss n).ob x = 0 ∧ (ss n).fl x = 0 ∧ (ss n).ib x = 0
Proof
  strip_tac >>
  drule_all ez_rem >> strip_tac >> rename1 ‘∀n. m0 ≤ n ⇒ (ss n).rem = 0’ >>
  (* one hop: ob, then fl, then ib, from its upstream's quiet point *)
  ‘∀x m. (∀n. m ≤ n ⇒ (ss n).rem = 0 ∧ (x = Q2 ⇒ (ss n).ib Q1 = 0) ∧
              (x = R1 ⇒ (ss n).ib Q2 = 0) ∧ (x = R2 ⇒ (ss n).ib R1 = 0)) ⇒
         ∃m'. m ≤ m' ∧ ∀n. m' ≤ n ⇒ (ss n).ob x = 0 ∧ (ss n).fl x = 0 ∧ (ss n).ib x = 0’ by
    (rpt strip_tac >>
     qspecl_then [‘x’, ‘m’] mp_tac (Q.GENL [‘x’, ‘m’] ez_stage_ob) >>
     impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
     qspecl_then [‘x’, ‘m + m'’] mp_tac (Q.GENL [‘x’, ‘m’] ez_stage_fl) >>
     impl_tac >- (simp[] >> rw[] >> fs[]) >> strip_tac >>
     qspecl_then [‘x’, ‘m + m' + m''’] mp_tac (Q.GENL [‘x’, ‘m’] ez_stage_ib) >>
     impl_tac >- (simp[] >> rw[] >> fs[]) >> strip_tac >>
     qexists_tac ‘m + m' + m'' + m'³'’ >> rw[] >> fs[]) >>
  first_assum (qspecl_then [‘Q1’, ‘m0’] mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  first_assum (qspecl_then [‘Q2’, ‘m'’] mp_tac) >> impl_tac >- (rw[] >> fs[]) >> strip_tac >>
  first_assum (qspecl_then [‘R1’, ‘m''’] mp_tac) >> impl_tac >- (rw[] >> fs[]) >> strip_tac >>
  first_assum (qspecl_then [‘R2’, ‘m'³'’] mp_tac) >> impl_tac >- (rw[] >> fs[]) >> strip_tac >>
  qexists_tac ‘m'⁴'’ >> rw[] >> fs[] >> Cases_on ‘x’ >> fs[]
QED

Theorem cons_run:
  run pol hw CH rb R dok ss ls ∧ (∀n x. ls n ≠ Drop x) ⇒ ∀n. cons R rb (ss n)
Proof
  strip_tac >> Induct >- fs[run_def, init_def, cons_def] >>
  metis_tac[cons_step, run_step]
QED

(* P2, strong form: with no drop, the client eventually reads every reply *)
Theorem moonshot_served:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ∧ (∀n x. ls n ≠ Drop x) ⇒
  ∃n. (ss n).got = rb * R
Proof
  strip_tac >> drule_all ez_all >> strip_tac >>
  drule_all cons_run >> disch_then (qspec_then ‘m’ mp_tac) >>
  first_x_assum (qspec_then ‘m’ mp_tac) >> rw[cons_def] >> qexists_tac ‘m’ >> fs[]
QED

(* P2, main form: served, or the write timeout dropped an outbox *)
Theorem moonshot_served_unless:
  run Gate hw CH rb R dok ss ls ∧ sched ls ∧ kfair Gate hw ss ⇒
  (∃n x. ls n = Drop x) ∨ ∃n. (ss n).got = rb * R
Proof
  metis_tac[moonshot_served]
QED

(*---------------------------------------------------------------------------*)
(* P3: the bite.  With per-fd pausing in the proxy there is a fair run in
   which the client never gets a reply (hw = 0, CH = 1, rb = 2, R = 3):
   the proxy's backend outbox and KV's outbox stay over hw, each receiver
   pauses on its own outbox, and both kernels stay non-empty *)

(* the step, as a function (its guards apart) *)
Definition nxt_def:
  (nxt pol hw rb s (CStep t) =
     let s1 = s with <| rem := 0; ob := (Q1 =+ s.ob Q1 + s.rem) s.ob |> in
       (flush Q1 t s1) with <| got := s.got + s.ib R2; ib := (R2 =+ 0) s.ib |>) ∧
  (nxt pol hw rb s (PStep t2 t4) =
     let g1 = prd pol hw s Q1; g2 = prd pol hw s R1;
         s1 = flush R2 t4 (flush Q2 t2 s) in
       s1 with <| ob := (Q2 =+ s1.ob Q2 + (if g1 then s.ib Q1 else 0))
                         ((R2 =+ s1.ob R2 + (if g2 then s.ib R1 else 0)) s1.ob);
                  ib := (Q1 =+ (if g1 then 0 else s.ib Q1))
                         ((R1 =+ (if g2 then 0 else s.ib R1)) s.ib) |>) ∧
  (nxt pol hw rb s (KStep t) =
     let s1 = flush R1 t s in
       s1 with <| done := s.done + s.ib Q2;
                  ob := (R1 =+ s1.ob R1 + rb * s.ib Q2) s1.ob;
                  ib := (Q2 =+ 0) s.ib |>) ∧
  (nxt pol hw rb s (Move x n) = s with <| fl := (x =+ s.fl x - n) s.fl; ib := (x =+ n) s.ib |>) ∧
  (nxt pol hw rb s (Drop x) = s with ob := (x =+ 0) s.ob)
End

Definition guard_def:
  (guard pol hw CH s (CStep t) ⇔ flush_ok (s with <| rem := 0; ob := (Q1 =+ s.ob Q1 + s.rem) s.ob |>) Q1 t) ∧
  (guard pol hw CH s (PStep t2 t4) ⇔ flush_ok s Q2 t2 ∧ flush_ok s R2 t4) ∧
  (guard pol hw CH s (KStep t) ⇔ flush_ok s R1 t) ∧
  (guard pol hw CH s (Move x n) ⇔ asks pol hw s x ∧ 0 < n ∧ n ≤ s.fl x ∧ n ≤ CH) ∧
  (guard pol hw CH s (Drop x) ⇔ T)
End

Theorem step_nxt:
  step pol hw CH rb s l s' ⇔ guard pol hw CH s l ∧ s' = nxt pol hw rb s l
Proof
  Cases_on ‘l’ >> simp[step_def, nxt_def, guard_def, LET_THM] >> metis_tac[]
QED

Definition trace_def:
  trace pol hw rb s [] = [s] ∧
  trace pol hw rb s (l :: ls) = s :: trace pol hw rb (nxt pol hw rb s l) ls
End

Theorem trace_len:
  ∀s. LENGTH (trace pol hw rb s ls) = SUC (LENGTH ls)
Proof
  Induct_on ‘ls’ >> simp[trace_def]
QED

Theorem trace_EL:
  ∀s n. n < LENGTH ls ⇒
    EL (SUC n) (trace pol hw rb s ls) = nxt pol hw rb (EL n (trace pol hw rb s ls)) (EL n ls)
Proof
  Induct_on ‘ls’ >> simp[trace_def] >> rw[] >> Cases_on ‘n’ >> simp[trace_def] >>
  Cases_on ‘ls’ >> fs[trace_def]
QED

Definition bite_pre_def:
  bite_pre = [CStep 1; Move Q1 1; PStep 0 0; CStep 1; Move Q1 1; PStep 1 0; Move Q2 1;
              KStep 0; KStep 1; CStep 1; Move Q1 1; PStep 1 0]
End

Definition bite_loop_def:
  bite_loop = [CStep 0; PStep 0 0; KStep 0]
End

Definition bite_tr_def:
  bite_tr = trace PerFd 0 2 (init 3) bite_pre
End

Definition bite_ss_def:
  bite_ss n = if n ≤ 12 then EL n bite_tr else EL 12 bite_tr
End

Definition bite_ls_def:
  bite_ls n = if n < 12 then EL n bite_pre else EL ((n − 12) MOD 3) bite_loop
End

Theorem bite_stuck:
  let s = EL 12 bite_tr in
    s.ob Q2 = 1 ∧ s.fl Q2 = 1 ∧ s.ob R1 = 1 ∧ s.fl R1 = 1 ∧
    s.fl Q1 = 0 ∧ s.fl R2 = 0 ∧ s.ob Q1 = 0 ∧ s.ob R2 = 0 ∧
    (∀x. s.ib x = 0) ∧ s.rem = 0 ∧ s.got = 0
Proof
  simp[] >> EVAL_TAC >> Cases >> EVAL_TAC
QED

Theorem bite_loop_fix:
  MEM l bite_loop ⇒ guard PerFd 0 1 (EL 12 bite_tr) l ∧
                    nxt PerFd 0 2 (EL 12 bite_tr) l = EL 12 bite_tr
Proof
  assume_tac (SIMP_RULE std_ss [LET_THM] bite_stuck) >>
  qabbrev_tac ‘s = EL 12 bite_tr’ >>
  rw[bite_loop_def] >> simp[guard_def, nxt_def, flush_ok_def, flush_def, prd_def] >>
  simp[theorem "st_component_equality", FUN_EQ_THM] >> rw[] >> Cases_on ‘x’ >>
  simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem bite_pre_steps:
  ∀n. n < 12 ⇒ guard PerFd 0 1 (EL n bite_tr) (EL n bite_pre)
Proof
  CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL)) >> simp[]
QED

Theorem bite_pre_nodrop:
  n < 12 ⇒ EL n bite_pre ≠ Drop x
Proof
  strip_tac >> ‘MEM (EL n bite_pre) bite_pre’ by
    (simp[listTheory.MEM_EL] >> qexists_tac ‘n’ >> simp[bite_pre_def]) >>
  strip_tac >> fs[bite_pre_def]
QED

Theorem bite_tr_got:
  ∀n. n < 13 ⇒ (EL n bite_tr).got = 0
Proof
  CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL)) >> simp[]
QED

Theorem bite_run:
  run PerFd 0 1 2 3 dok bite_ss bite_ls
Proof
  rw[run_def]
  >- (simp[bite_ss_def, bite_tr_def, bite_pre_def] >> simp[trace_def])
  >- (simp[step_nxt] >> Cases_on ‘n < 12’
      >- (simp[bite_ss_def, bite_ls_def, bite_pre_steps] >>
          ‘LENGTH bite_pre = 12’ by EVAL_TAC >>
          simp[bite_tr_def, trace_EL])
      >> ‘MEM (bite_ls n) bite_loop’ by
           (simp[bite_ls_def] >> ‘(n − 12) MOD 3 < 3’ by simp[] >>
            ‘LENGTH bite_loop = 3’ by EVAL_TAC >> metis_tac[listTheory.MEM_EL]) >>
      ‘bite_ss n = EL 12 bite_tr ∧ bite_ss (SUC n) = EL 12 bite_tr’ by
        (rw[bite_ss_def] >> ‘n = 12’ by simp[] >> simp[]) >>
      metis_tac[bite_loop_fix])
  >> fs[bite_ls_def] >> Cases_on ‘n < 12’ >> fs[] >- metis_tac[bite_pre_nodrop] >>
  ‘(n − 12) MOD 3 < 3’ by simp[] >> qabbrev_tac ‘k = (n − 12) MOD 3’ >>
  ‘k = 0 ∨ k = 1 ∨ k = 2’ by simp[] >> fs[bite_loop_def]
QED

Theorem bite_ls_at:
  bite_ls (12 + 3 * k + j) = EL j bite_loop ∨ 3 ≤ j
Proof
  Cases_on ‘3 ≤ j’ >> simp[bite_ls_def] >>
  ‘(3 * k + j) MOD 3 = j’ suffices_by simp[] >>
  ‘3 * k + j = k * 3 + j’ by simp[] >> pop_assum SUBST1_TAC >> simp[MOD_MULT]
QED

Theorem bite_sched:
  sched bite_ls
Proof
  ‘∀j m. j < 3 ⇒ ∃n. m ≤ n ∧ bite_ls n = EL j bite_loop’ by
    (rw[] >> qexists_tac ‘12 + 3 * m + j’ >> simp[] >>
     qspecl_then [‘m’, ‘j’] mp_tac (Q.GENL [‘k’, ‘j’] bite_ls_at) >> simp[]) >>
  rw[sched_def, io_def] >| [
    first_x_assum (qspecl_then [‘0’, ‘m’] mp_tac),
    first_x_assum (qspecl_then [‘1’, ‘m’] mp_tac),
    first_x_assum (qspecl_then [‘2’, ‘m’] mp_tac)] >>
  simp[] >> strip_tac >> qexists_tac ‘n’ >> fs[bite_loop_def, is_c_def, is_p_def, is_k_def]
QED

Theorem bite_ss_late:
  12 ≤ n ⇒ bite_ss n = EL 12 bite_tr
Proof
  rw[bite_ss_def] >> ‘n = 12’ by simp[] >> simp[]
QED

Theorem bite_kfair:
  kfair PerFd 0 bite_ss
Proof
  assume_tac (SIMP_RULE std_ss [LET_THM] bite_stuck) >>
  rw[kfair_def] >> Cases_on ‘x’
  >- (qexists_tac ‘m + 12’ >> simp[bite_ss_late])
  >- (fs[io_def] >> first_x_assum (qspec_then ‘12’ strip_assume_tac) >>
      rfs[bite_ss_late, asks_def])
  >- (fs[io_def] >> first_x_assum (qspec_then ‘12’ strip_assume_tac) >>
      rfs[bite_ss_late, asks_def])
  >> qexists_tac ‘m + 12’ >> simp[bite_ss_late]
QED

Theorem bite_got:
  (bite_ss n).got = 0
Proof
  rw[bite_ss_def] >> irule bite_tr_got >> simp[]
QED

(* P3: per-fd pausing in the relay deadlocks: a fair run (scheduler and
   observed kernel fairness), with no drop, in which the client reads
   nothing, for any timeout rule dok *)
Theorem perfd_deadlock:
  ∃ss ls. run PerFd 0 1 2 3 dok ss ls ∧ sched ls ∧ kfair PerFd 0 ss ∧
          (∀n x. ls n ≠ Drop x) ∧ ∀n. (ss n).got < 2 * 3
Proof
  qexistsl_tac [‘bite_ss’, ‘bite_ls’] >>
  simp[bite_run, bite_sched, bite_kfair, bite_got] >> rw[bite_ls_def]
  >- metis_tac[bite_pre_nodrop] >>
  ‘(n − 12) MOD 3 < 3’ by simp[] >> qabbrev_tac ‘k = (n − 12) MOD 3’ >>
  ‘k = 0 ∨ k = 1 ∨ k = 2’ by simp[] >> fs[bite_loop_def]
QED
