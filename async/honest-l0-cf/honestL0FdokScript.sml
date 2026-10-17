(*
  D33's startup prefix, at the world level: a program's three sys_fdok
  calls on fds 0, 1, 2 leave the world as it was (but for the step of
  time before each call, which delivers nothing to a fresh world), and
  answer 1 for all three exactly when 0, 1 and 2 are in use, which in a
  fresh world means reserved.  So a claim that drops MEM 0w/1w/2w from its
  world assumption gets them back after the prefix (fdok_shift), or the
  run is stdio_closed (fdok_closed).
*)
Theory honestL0Fdok
Ancestors
  honestL0 honestL0World honestL0Rely honestL1Model honestL0Part honestL0Outcome
Libs
  preamble

Theorem MAP_FST_AFUPDKEY[local]:
  ∀L. MAP FST (AFUPDKEY k f L) = MAP FST L
Proof
  Induct >> simp[AFUPDKEY_def] >> Cases >> rw[AFUPDKEY_def]
QED

Theorem l0_deliver_used[simp]:
  l0_used (l0_deliver w a) = l0_used w
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, l0_used_def, upd_lchan_def] >>
  every_case_tac >> simp[MAP_FST_AFUPDKEY]
QED

Theorem l0_tick_used[simp]:
  l0_used (l0_tick nm w) = l0_used w
Proof
  ‘∀as w. l0_used (FOLDL l0_deliver w as) = l0_used w’ by (Induct >> fs[]) >>
  simp[l0_tick_def] >> simp[l0_used_def]
QED

(* A fresh world: no listener, channel or open connection fd *)
Definition l0_fresh_world_def:
  l0_fresh_world (w : l0world) ⇔ w.listeners = [] ∧ w.chans = [] ∧ w.open_fds = []
End

Theorem l0_deliver_fresh:
  l0_fresh_world w ⇒ l0_deliver w a = w
Proof
  Cases_on ‘a’ >> rw[l0_fresh_world_def, l0_deliver_def]
QED

Theorem l0_tick_fresh:
  l0_fresh_world w ⇒ l0_tick nm w = w with clock := w.clock + 1
Proof
  strip_tac >>
  ‘∀as w. l0_fresh_world w ⇒ FOLDL l0_deliver w as = w’
    by (Induct >> rw[] >> simp[l0_deliver_fresh]) >>
  simp[l0_tick_def] >> first_x_assum irule >> fs[l0_fresh_world_def]
QED

Theorem l0_fresh_used:
  l0_fresh_world w ⇒ l0_used w = w.reserved
Proof
  rw[l0_fresh_world_def, l0_used_def]
QED

(* One sys_fdok call *)
Theorem fdok_do:
  l0_do «sys_fdok» [f] 1 w = SOME (out, w', ev) ⇔
  out = [if MEM (w2w f) (l0_used w) then 1w else 0w] ∧
  w' = (l0_tick «sys_fdok» w) with hist := w.hist ++ [(«sys_fdok», [f], [0w])] ∧
  ev = IO_event (ExtCall «sys_fdok») [f] [(0w, HD out)]
Proof
  ‘REPLICATE 1 (0w : word8) = [0w]’ by EVAL_TAC >>
  simp[l0_do_def, l0_ffi_fn_def, l0_call_def] >> eq_tac >> rw[] >> simp[]
QED

(* One call from a fresh world *)
Theorem fdok_fresh_step:
  l0_fresh_world w ∧ l0_do «sys_fdok» [f] 1 w = SOME (out, w', ev) ⇒
  l0_fresh_world w' ∧
  w' = w with <| clock := w.clock + 1; hist := w.hist ++ [(«sys_fdok», [f], [0w])] |> ∧
  out = [if MEM (w2w f) w.reserved then 1w else 0w] ∧
  ev = IO_event (ExtCall «sys_fdok») [f] [(0w, HD out)] ∧
  w'.reserved = w.reserved
Proof
  strip_tac >> ‘l0_used w = w.reserved’ by fs[l0_fresh_used] >>
  qpat_x_assum ‘l0_do _ _ _ _ = _’ mp_tac >> simp[fdok_do, l0_tick_fresh] >>
  strip_tac >> rveq >> fs[l0_fresh_world_def]
QED

(* The prefix from a fresh world *)
Theorem fdok_shift:
  l0_fresh_world w0 ∧
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ⇒
  w3 = w0 with <| clock := w0.clock + 3;
                  hist := w0.hist ++ [(«sys_fdok», [0w], [0w]); («sys_fdok», [1w], [0w]);
                                      («sys_fdok», [2w], [0w])] |> ∧
  (o0 = [1w] ∧ o1 = [1w] ∧ o2 = [1w] ⇔
   MEM 0w w0.reserved ∧ MEM 1w w0.reserved ∧ MEM 2w w0.reserved) ∧
  (∀w. l0_reach w w0 ⇒ l0_reach w w3)
Proof
  strip_tac >>
  ‘REPLICATE 1 (0w : word8) = [0w]’ by EVAL_TAC >>
  ‘∀w. l0_reach w w0 ⇒ l0_reach w w3’
    by (rpt strip_tac >> fs[l0_do_def, AllCaseEqs()] >>
        metis_tac[l0_reach_step]) >>
  simp[] >>
  drule_all fdok_fresh_step >> strip_tac >>
  qpat_x_assum ‘l0_do _ [1w] _ _ = _’ assume_tac >>
  drule_all fdok_fresh_step >> strip_tac >>
  qpat_x_assum ‘l0_do _ [2w] _ _ = _’ assume_tac >>
  drule_all fdok_fresh_step >> strip_tac >>
  rveq >> simp[honestL0WorldTheory.l0world_component_equality] >>
  fs[] >> rw[] >> fs[]
QED

(* Otherwise the run is stdio_closed *)
Theorem fdok_closed:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ ¬(o0 = [1w] ∧ o1 = [1w] ∧ o2 = [1w]) ⇒
  stdio_closed (Terminate Success [e0; e1; e2])
Proof
  rw[fdok_do, stdio_closed_def] >> rw[] >> fs[]
QED
