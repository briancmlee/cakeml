(*
  D(c) from the trace to round boundaries, for any run (close-v2's part
  (d)): the trace-level drains w0 io c (if nothing more is sent on c after
  a prefix, c's bytes in flight eventually reach 0) gives the same at the
  run's round boundaries B n (the start and the first n rounds' events).

  B is generic: any increasing sequence of prefixes of io whose worlds are
  defined and which every finite prefix of io lies within (eventually).
  For an E1 run, B n = pre ++ FLAT (GENLIST f n): e1_lprefix_rounds gives
  the last, erounds_world_at the worlds.

  As honest-echo-live's drains_round (b58968e19), over smono.

  MAIN: drains_bounds.
*)
Theory e1TraceDrains
Ancestors
  e1TraceWorld e1TracePrefix clientLiveCopy honestL0World
Libs
  preamble

(* The world at round boundary n *)
Definition bworld_def:
  bworld w0 (B : num -> io_event list) n = THE (world_at w0 (B n))
End

(* The boundaries B cover io *)
Definition bounds_def:
  bounds w0 io (B : num -> io_event list) ⇔
    (∀n. LPREFIX (fromList (B n)) io) ∧
    (∀n. ∃w. world_at w0 (B n) = SOME w) ∧
    (∀n m. n ≤ m ⇒ B n ≼ B m) ∧
    (∀evs. LPREFIX (fromList evs) io ⇒ ∃n. evs ≼ B n)
End

(* drains, at the boundaries *)
Definition bdrains_def:
  bdrains w0 B c ⇔
    ∀n. c < LENGTH (bworld w0 B n).chans ∧
        (∀m. n ≤ m ⇒ (EL c (bworld w0 B m).chans).sent = (EL c (bworld w0 B n).chans).sent) ⇒
        ∃M. n ≤ M ∧ (EL c (bworld w0 B M).chans).inflight = 0
End

Theorem bounds_world:
  bounds w0 io B ⇒ world_at w0 (B n) = SOME (bworld w0 B n)
Proof
  rw[bounds_def, bworld_def] >>
  qpat_x_assum ‘∀n. ∃w. _’ (qspec_then ‘n’ strip_assume_tac) >> simp[]
QED

Theorem bounds_locate:
  bounds w0 io B ∧ LPREFIX (fromList evs) io ⇒ ∀Kb. ∃M. Kb ≤ M ∧ evs ≼ B M
Proof
  rw[bounds_def] >>
  last_x_assum drule >> strip_tac >>
  qexists_tac ‘n + Kb’ >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘B n’ >> simp[]
QED

Theorem bounds_smono:
  bounds w0 io B ∧ a ≤ b ⇒ smono c (bworld w0 B a) (bworld w0 B b)
Proof
  strip_tac >>
  ‘B a ≼ B b’ by fs[bounds_def] >>
  fs[IS_PREFIX_APPEND] >>
  irule world_at_smono >> qexistsl_tac [‘B a’, ‘l’, ‘w0’] >>
  metis_tac[bounds_world]
QED

(* MAIN *)
Theorem drains_bounds:
  bounds w0 io B ∧ drains w0 io c ⇒ bdrains w0 B c
Proof
  rw[bdrains_def] >>
  (* past n's boundary, any world has n's sent and is below a later boundary *)
  ‘∀evs' w'. LPREFIX (fromList (B n ++ evs')) io ∧
             world_at w0 (B n ++ evs') = SOME w' ⇒
             c < LENGTH w'.chans ∧
             (EL c w'.chans).sent = (EL c (bworld w0 B n).chans).sent ∧
             ∃M. n ≤ M ∧ smono c w' (bworld w0 B M)’
    by (rpt gen_tac >> strip_tac >>
        drule_all bounds_locate >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
        fs[IS_PREFIX_APPEND] >>
        ‘smono c (bworld w0 B n) w'’
          by (irule world_at_smono >> metis_tac[bounds_world]) >>
        ‘smono c w' (bworld w0 B M)’
          by (irule world_at_smono >> qexistsl_tac [‘B n ++ evs'’, ‘l’, ‘w0’] >>
              metis_tac[bounds_world, APPEND_ASSOC]) >>
        ‘(EL c (bworld w0 B M).chans).sent = (EL c (bworld w0 B n).chans).sent’
          by (first_x_assum irule >> simp[]) >>
        fs[smono_def] >> rfs[] >>
        conj_tac >- metis_tac[IS_PREFIX_ANTISYM] >>
        qexists_tac ‘M’ >> simp[]) >>
  qpat_x_assum ‘drains _ _ _’
    (qspecl_then [‘B n’, ‘bworld w0 B n’] mp_tac o REWRITE_RULE [drains_def]) >>
  impl_tac
  >- (rpt conj_tac
      >- fs[bounds_def]
      >- metis_tac[bounds_world]
      >- simp[] >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac ‘M’ >> simp[] >>
  qpat_x_assum ‘smono _ w' _’ mp_tac >> simp[smono_def] >>
  ‘(EL c (bworld w0 B M).chans).sent = (EL c w'.chans).sent’
    suffices_by (strip_tac >> fs[]) >>
  ‘(EL c (bworld w0 B M).chans).sent = (EL c (bworld w0 B n).chans).sent’
    by (first_x_assum irule >> simp[]) >>
  fs[]
QED

(* An E1 run that diverges: its rounds' boundaries cover its trace *)
Theorem bounds_rounds:
  (∀n. ∃w. world_at w0 (pre ++ FLAT (GENLIST f n)) = SOME w) ⇒
  bounds w0 (LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)))
         (λn. pre ++ FLAT (GENLIST f n))
Proof
  rw[bounds_def]
  >- (REWRITE_TAC[e1TracePrefixTheory.LPREFIX_LAPPEND_fromList] >> MATCH_ACCEPT_TAC e1TracePrefixTheory.rounds_LPREFIX)
  >- (rename1 ‘n ≤ m’ >> simp[IS_PREFIX_APPEND] >>
      ‘∃k. m = n + k’ by (qexists_tac ‘m − n’ >> decide_tac) >>
      pop_assum SUBST1_TAC >>
      qexists_tac ‘FLAT (GENLIST (λi. f (n + i)) k)’ >>
      qid_spec_tac ‘k’ >> Induct >>
      fs[GENLIST, ADD_CLAUSES, FLAT_SNOC])
  >- metis_tac[e1_lprefix_rounds]
QED

(* A run that terminates: its whole trace is the one boundary *)
Theorem bounds_fromList:
  (∃w. world_at w0 l = SOME w) ⇒ bounds w0 (fromList l) (λn. l)
Proof
  rw[bounds_def, e1_lprefix_fromList] >> metis_tac[]
QED
