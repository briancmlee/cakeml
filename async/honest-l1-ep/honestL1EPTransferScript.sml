(*
  E1, as a transfer principle: a guarantee proved of the endpoint handle
  layer, in every world of a class P with the run-local rely, holds of the
  honest L1's own run, in the world pew that E1 builds from that run (the
  Level oracle being E1's elv).  For the moonshot's client (step 10) and
  proxy (step 9).
*)
Theory honestL1EPTransfer
Ancestors
  honestL1EPRefine honestL1EPModel endpointHLModel endpointWorld
Libs
  preamble

Theorem l1_of_hl:
  (∀lv W. P W ∧ (∀n. eh_round_ok lfd lv ifds m W n) ⇒ G lv W) ∧
  P (pew lfd a hw ifds m w0 calls) ∧
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (ecm lfd hw ifds m w0 n) + 1 < dimword (:64)) ∧
  (∀n. erounds lfd hw ifds m (w0, einit) n ≠ NONE) ⇒
  G (elv lfd hw ifds m w0) (pew lfd a hw ifds m w0 calls) ∧
  ∀n. ehhist lfd (elv lfd hw ifds m w0) ifds m (pew lfd a hw ifds m w0 calls) n =
      FST (THE (erounds lfd hw ifds m (w0, einit) n))
Proof
  strip_tac >>
  ‘∀n. ∃h ws evs logs. erounds lfd hw ifds m (w0, einit) n = SOME (h, ws, evs, logs)’
    by (gen_tac >> first_x_assum (qspec_then ‘n’ mp_tac) >>
        Cases_on ‘erounds lfd hw ifds m (w0, einit) n’ >> simp[] >>
        PairCases_on ‘x’ >> simp[]) >>
  conj_tac
  >- (first_x_assum irule >> simp[] >> gen_tac >>
      first_x_assum (qspec_then ‘SUC n’ strip_assume_tac) >>
      drule_all l1ep_refines_ehl >> disch_then (qspecl_then [‘calls’, ‘a’] strip_assume_tac) >> simp[]) >>
  gen_tac >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  drule_all l1ep_refines_ehl >> disch_then (qspecl_then [‘calls’, ‘a’] strip_assume_tac) >> simp[]
QED
