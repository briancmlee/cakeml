(*
  B2 (l0sys_causal): the kernel's invariant on an l0sys run, and the
  causality bridge.

  kinv s: the pairing is symmetric; of a paired end's stream, its peer has
  received a prefix of what was moved, all of it unless the peer stopped
  taking data (frozen); an end that has not been paired has moved nothing,
  and while it connects it has neither sent nor received anything.
*)
Theory l0sysCausal
Ancestors
  honestL0 honestL0World honestL0Rely l0sys l0sysEpisodes l0sysEpisodesEcho
  l0sysInv l0sysInvCall l0sysMono
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The kernel's invariant *)

Definition kinv_def:
  kinv (s : sysstate) ⇔
    (∀e. ¬is_end s e ⇒ s.peer e = NONE ∧ s.moved e = 0 ∧ s.target e = NONE) ∧
    (∀e e'. s.peer e = SOME e' ⇒
       s.peer e' = SOME e ∧ is_end s e ∧ ¬(sys_chan s e).connecting ∧
       (s.target e = NONE ⇔ s.target e' ≠ NONE) ∧
       s.moved e ≤ LENGTH (sys_chan s e).sent ∧
       (sys_chan s e').peer_sent ≼ TAKE (s.moved e) (sys_chan s e).sent ∧
       (frozen (sys_chan s e') ∨
        (sys_chan s e').peer_sent = TAKE (s.moved e) (sys_chan s e).sent)) ∧
    (∀e. is_end s e ∧ s.peer e = NONE ⇒
       s.moved e = 0 ∧
       ((sys_chan s e).connecting ⇒ (sys_chan s e).peer_sent = [] ∧ (sys_chan s e).sent = []))
End

(* Ends and channels live in procs only *)
Theorem is_end_fields[simp]:
  (is_end (s with target := X1) e ⇔ is_end s e) ∧ (is_end (s with peer := X2) e ⇔ is_end s e) ∧
  (is_end (s with moved := X3) e ⇔ is_end s e) ∧ (is_end (s with acked := X4) e ⇔ is_end s e) ∧
  (is_end (s with finned := X5) e ⇔ is_end s e) ∧ (is_end (s with alive := X6) e ⇔ is_end s e)
Proof
  Cases_on ‘e’ >> simp[is_end_def]
QED

Theorem sys_chan_fields[simp]:
  sys_chan (s with target := X1) e = sys_chan s e ∧ sys_chan (s with peer := X2) e = sys_chan s e ∧
  sys_chan (s with moved := X3) e = sys_chan s e ∧ sys_chan (s with acked := X4) e = sys_chan s e ∧
  sys_chan (s with finned := X5) e = sys_chan s e ∧ sys_chan (s with alive := X6) e = sys_chan s e
Proof
  Cases_on ‘e’ >> simp[sys_chan_def]
QED

Theorem sys_chan_LUPDATE:
  k < LENGTH s.procs ⇒
  sys_chan (s with procs := LUPDATE w k s.procs) (k', j) =
  if k' = k then EL j w.chans else sys_chan s (k', j)
Proof
  rw[sys_chan_def, EL_LUPDATE]
QED

Theorem is_end_LUPDATE:
  k < LENGTH s.procs ⇒
  (is_end (s with procs := LUPDATE w k s.procs) (k', j) ⇔
   if k' = k then j < LENGTH w.chans else is_end s (k', j))
Proof
  rw[is_end_def, EL_LUPDATE]
QED

Theorem local_chans:
  k < LENGTH s.procs ∧ wmono (EL k s.procs) w' ⇒
  (∀e. is_end s e ⇒
       is_end (s with procs := LUPDATE w' k s.procs) e ∧
       cmono (sys_chan s e) (sys_chan (s with procs := LUPDATE w' k s.procs) e)) ∧
  (∀e. is_end (s with procs := LUPDATE w' k s.procs) e ∧ ¬is_end s e ⇒
       (sys_chan (s with procs := LUPDATE w' k s.procs) e).sent = [] ∧
       (sys_chan (s with procs := LUPDATE w' k s.procs) e).peer_sent = [])
Proof
  strip_tac >> conj_tac >> Cases >> simp[is_end_LUPDATE, sys_chan_LUPDATE] >>
  rw[] >> gvs[wmono_def, is_end_def, sys_chan_def]
QED

Theorem TAKE_prefix:
  x ≼ y ∧ m ≤ LENGTH x ⇒ TAKE m y = TAKE m x
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_APPEND1]
QED

(* A process's own change of its channels (wmono) keeps kinv *)
Theorem kinv_local:
  kinv s ∧ k < LENGTH s.procs ∧ wmono (EL k s.procs) w' ⇒
  kinv (s with procs := LUPDATE w' k s.procs)
Proof
  strip_tac >> drule_all local_chans >> strip_tac >>
  qabbrev_tac ‘s' = s with procs := LUPDATE w' k s.procs’ >>
  ‘s'.peer = s.peer ∧ s'.moved = s.moved ∧ s'.target = s.target’ by simp[Abbr ‘s'’] >>
  fs[kinv_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> ‘¬is_end s e’ by metis_tac[] >>
      first_x_assum drule >> simp[])
  >- (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      ‘is_end s e'’ by (CCONTR_TAC >> res_tac >> gvs[]) >>
      ‘cmono (sys_chan s e) (sys_chan s' e) ∧ cmono (sys_chan s e') (sys_chan s' e')’
        by metis_tac[] >>
      ‘(sys_chan s e).sent ≼ (sys_chan s' e).sent’ by gvs[cmono_def] >>
      ‘TAKE (s.moved e) (sys_chan s' e).sent = TAKE (s.moved e) (sys_chan s e).sent’
        by (irule TAKE_prefix >> simp[]) >>
      ‘s.moved e ≤ LENGTH (sys_chan s' e).sent’
        by (irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (sys_chan s e).sent’ >> simp[] >>
            irule IS_PREFIX_LENGTH >> simp[]) >>
      gvs[cmono_def]) >>
  rpt gen_tac >> strip_tac >> Cases_on ‘is_end s e’
  >- (‘cmono (sys_chan s e) (sys_chan s' e)’ by metis_tac[] >> gvs[cmono_def] >>
      res_tac >> rw[] >> gvs[]) >>
  res_tac >> gvs[]
QED

(* A connect sets the target of its new, unpaired end *)
Theorem kinv_target:
  kinv s ∧ is_end s e ∧ s.peer e = NONE ⇒ kinv (s with target := (e =+ x) s.target)
Proof
  rw[kinv_def, APPLY_UPDATE_THM] >> rw[] >> gvs[] >>
  res_tac >> gvs[]
QED

(* Arrivals other than data, at one process *)
Theorem kinv_deliver:
  kinv s ∧ k < LENGTH s.procs ∧ (∀j bs. a ≠ LData j bs) ⇒ kinv (sys_deliver k a s)
Proof
  rw[sys_deliver_def] >> irule kinv_local >> simp[wmono_deliver]
QED

(* Data from outside, on an unpaired end that is not connecting *)
(* Data arriving at end (k, j), as the channels see it *)
Theorem data_chans:
  k < LENGTH s.procs ⇒
  let s' = sys_deliver k (LData j bs) s in
    (∀e. is_end s' e ⇔ is_end s e) ∧
    ∀e. is_end s e ⇒
        (sys_chan s' e).sent = (sys_chan s e).sent ∧
        ((sys_chan s' e).connecting ⇔ (sys_chan s e).connecting) ∧
        (frozen (sys_chan s' e) ⇔ frozen (sys_chan s e)) ∧
        (sys_chan s' e).peer_sent =
        if e = (k, j) ∧ ¬frozen (sys_chan s e) ∧ ¬(sys_chan s e).connecting
        then (sys_chan s e).peer_sent ++ bs else (sys_chan s e).peer_sent
Proof
  rw[sys_deliver_def] >> Cases_on ‘e’ >>
  simp[is_end_LUPDATE, sys_chan_LUPDATE] >> rw[] >>
  gvs[is_end_def, sys_chan_def, deliver_data] >> rw[] >> gvs[]
QED

(* Data from outside, on an unpaired end *)
Theorem kinv_arrive_data:
  kinv s ∧ k < LENGTH s.procs ∧ s.peer (k, j) = NONE ⇒
  kinv (sys_deliver k (LData j bs) s)
Proof
  strip_tac >> drule data_chans >> disch_then (qspecl_then [‘j’, ‘bs’] mp_tac) >>
  simp[] >> qabbrev_tac ‘s' = sys_deliver k (LData j bs) s’ >> strip_tac >>
  ‘s'.peer = s.peer ∧ s'.moved = s.moved ∧ s'.target = s.target’
    by simp[Abbr ‘s'’, sys_deliver_def] >>
  fs[kinv_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST [
    ‘¬is_end s e’ by gvs[] >> qpat_x_assum ‘∀e. ¬is_end s e ⇒ _’ drule >> simp[] >> NO_TAC,
    qpat_x_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’ drule >> strip_tac >>
    ‘is_end s e'’ by (CCONTR_TAC >> res_tac >> gvs[]) >>
    ‘e' ≠ (k, j)’ by (strip_tac >> gvs[]) >> gvs[] >> NO_TAC,
    ‘is_end s e’ by gvs[] >> res_tac >> gvs[] >> rw[] >> gvs[]]
QED

(* Bytes moving from (k, j) to its peer *)
Theorem kinv_move:
  kinv s ∧ is_end s (k, j) ∧ s.peer (k, j) = SOME (k', j') ∧
  s.moved (k, j) + n ≤ LENGTH (sys_chan s (k, j)).sent ⇒
  kinv ((sys_deliver k' (LData j' (TAKE n (DROP (s.moved (k, j)) (sys_chan s (k, j)).sent))) s)
          with moved := ((k, j) =+ s.moved (k, j) + n) s.moved)
Proof
  strip_tac >>
  ‘s.peer (k', j') = SOME (k, j) ∧ is_end s (k', j') ∧ ¬(sys_chan s (k, j)).connecting’
    by (gvs[kinv_def] >> res_tac >> gvs[] >> CCONTR_TAC >> res_tac >> gvs[]) >>
  ‘¬(sys_chan s (k', j')).connecting’ by (gvs[kinv_def] >> res_tac >> gvs[]) >>
  ‘k' < LENGTH s.procs’ by gvs[is_end_def] >>
  qabbrev_tac ‘bs = TAKE n (DROP (s.moved (k, j)) (sys_chan s (k, j)).sent)’ >>
  drule data_chans >> disch_then (qspecl_then [‘j'’, ‘bs’] mp_tac) >> simp[] >>
  qabbrev_tac ‘s1 = sys_deliver k' (LData j' bs) s’ >> strip_tac >>
  ‘s1.peer = s.peer ∧ s1.moved = s.moved ∧ s1.target = s.target’
    by simp[Abbr ‘s1’, sys_deliver_def] >>
  ‘TAKE (s.moved (k, j)) (sys_chan s (k, j)).sent ++ bs =
   TAKE (s.moved (k, j) + n) (sys_chan s (k, j)).sent’ by simp[Abbr ‘bs’, TAKE_SUM] >>
  ‘TAKE (s.moved (k, j)) (sys_chan s (k, j)).sent ≼
   TAKE (s.moved (k, j) + n) (sys_chan s (k, j)).sent’
    by (qpat_x_assum ‘TAKE _ _ ++ bs = _’ (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> strip_tac >>
  rpt conj_tac
  >- ((* not an end *)
      rpt gen_tac >> strip_tac >>
      ‘¬is_end s e’ by (qpat_x_assum ‘¬is_end _ e’ mp_tac >> simp[is_end_fields] >> metis_tac[]) >>
      ‘(k, j) ≠ e’ by (CCONTR_TAC >> fs[]) >> simp[APPLY_UPDATE_THM] >> fs[])
  >- ((* a pair *)
      rpt gen_tac >> simp[APPLY_UPDATE_THM] >> strip_tac >>
      Cases_on ‘(k, j) = e’
      >- (rveq >>
          ‘e' = (k', j')’
            by (qpat_x_assum ‘s.peer (k, j) = SOME e'’ mp_tac >>
                qpat_x_assum ‘s.peer (k, j) = SOME (k', j')’ (fn th => simp[th])) >>
          rveq >> fs[] >>
          qpat_x_assum ‘∀e. is_end s e ⇒ _’ (qspec_then ‘(k', j')’ mp_tac) >>
          simp[] >> strip_tac >>
          qpat_x_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’
            (qspecl_then [‘(k, j)’, ‘(k', j')’] mp_tac) >> simp[] >> strip_tac >>
          Cases_on ‘frozen (sys_chan s (k', j'))’ >> fs[]
          >- (irule IS_PREFIX_TRANS >>
              qexists_tac ‘TAKE (s.moved (k, j)) (sys_chan s (k, j)).sent’ >> simp[]) >>
          qpat_x_assum ‘TAKE _ _ ++ bs = _’ (SUBST1_TAC o SYM) >> simp[]) >>
      qpat_x_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’ drule >> strip_tac >>
      ‘is_end s e'’ by (CCONTR_TAC >> res_tac >> fs[]) >>
      ‘(k', j') ≠ e'’ by (CCONTR_TAC >> fs[] >> rveq >> fs[]) >>
      qpat_x_assum ‘∀e. is_end s e ⇒ _’ (qspec_then ‘e'’ mp_tac) >> simp[] >> fs[]) >>
  (* an unpaired end *)
  rpt gen_tac >> strip_tac >>
  ‘is_end s e’ by (qpat_x_assum ‘is_end _ e’ mp_tac >> simp[is_end_fields] >> metis_tac[]) >>
  ‘s.peer e = NONE’
    by (qpat_x_assum ‘_.peer e = NONE’ mp_tac >>
        qpat_x_assum ‘s1.peer = s.peer’ (fn th => simp[th])) >>
  ‘(k, j) ≠ e’
    by (strip_tac >> qpat_x_assum ‘s.peer e = NONE’ mp_tac >>
        qpat_x_assum ‘(k, j) = e’ (fn th => rewrite_tac[GSYM th]) >>
        qpat_x_assum ‘s.peer (k, j) = SOME _’ (fn th => rewrite_tac[th]) >> simp[]) >>
  ‘(k', j') ≠ e’
    by (strip_tac >> qpat_x_assum ‘s.peer e = NONE’ mp_tac >>
        qpat_x_assum ‘(k', j') = e’ (fn th => rewrite_tac[GSYM th]) >>
        qpat_x_assum ‘s.peer (k', j') = SOME _’ (fn th => rewrite_tac[th]) >> simp[]) >>
  simp[APPLY_UPDATE_THM] >>
  qpat_x_assum ‘∀e. is_end s e ⇒ _’ (qspec_then ‘e’ mp_tac) >> simp[] >> fs[]
QED

Theorem deliver_incoming_chans:
  FILTER (λ(l, p', q). p' = p) w.listeners ≠ [] ⇒
  (l0_deliver w (LIncoming p)).chans = w.chans ++ [fresh_lchan]
Proof
  rw[l0_deliver_def] >> every_case_tac >> gvs[] >> PairCases_on ‘h’ >> gvs[]
QED

(* An incoming connection at k''s listener on port p: one new end *)
Theorem incoming_chans:
  sys_room s k' p ⇒
  let e' = (k', LENGTH (EL k' s.procs).chans); s1 = sys_deliver k' (LIncoming p) s in
    (∀e. is_end s e ⇒ is_end s1 e ∧ sys_chan s1 e = sys_chan s e) ∧
    (∀e. is_end s1 e ⇔ is_end s e ∨ e = e') ∧ ¬is_end s e' ∧
    sys_chan s1 e' = fresh_lchan ∧
    s1.peer = s.peer ∧ s1.moved = s.moved ∧ s1.target = s.target
Proof
  simp[] >> strip_tac >>
  ‘k' < LENGTH s.procs ∧
   (l0_deliver (EL k' s.procs) (LIncoming p)).chans = (EL k' s.procs).chans ++ [fresh_lchan]’
    by (gvs[sys_room_def] >> irule deliver_incoming_chans >> every_case_tac >> gvs[]) >>
  simp[sys_deliver_def] >> rpt conj_tac >> TRY Cases >>
  simp[is_end_LUPDATE, sys_chan_LUPDATE, is_end_def, sys_chan_def] >>
  rw[EL_APPEND1, EL_APPEND2] >> gvs[]
QED

Theorem kinv_pair_gen:
  kinv s ∧ is_end s e ∧ s.peer e = NONE ∧ ¬(sys_chan s e).connecting ∧
  (sys_chan s e).peer_sent = [] ∧ s.target e ≠ NONE ∧
  (∀x. is_end s x ⇒ is_end s1 x ∧ sys_chan s1 x = sys_chan s x) ∧
  (∀x. is_end s1 x ⇔ is_end s x ∨ x = e') ∧ ¬is_end s e' ∧
  sys_chan s1 e' = fresh_lchan ∧ s1.peer = s.peer ∧ s1.moved = s.moved ∧ s1.target = s.target ⇒
  kinv (s1 with peer := (e =+ SOME e') ((e' =+ SOME e) s1.peer))
Proof
  strip_tac >>
  ‘e ≠ e'’ by (strip_tac >> fs[]) >>
  ‘s.peer e' = NONE ∧ s.moved e' = 0 ∧ s.target e' = NONE’ by fs[kinv_def] >>
  ‘s.moved e = 0’ by fs[kinv_def] >>
  ‘is_end s1 e ∧ sys_chan s1 e = sys_chan s e ∧ is_end s1 e'’ by fs[] >>
  ‘∀x. is_end (s1 with peer := (e =+ SOME e') ((e' =+ SOME e) s1.peer)) x ⇔
       is_end s x ∨ x = e'’ by (Cases >> fs[is_end_def]) >>
  ‘∀x. sys_chan (s1 with peer := (e =+ SOME e') ((e' =+ SOME e) s1.peer)) x = sys_chan s1 x’
    by (Cases >> simp[sys_chan_def]) >>
  qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> strip_tac >>
  rpt conj_tac
  >- ((* not an end *)
      rpt gen_tac >> strip_tac >> rename1 ‘¬is_end _ x’ >>
      ‘¬is_end s x ∧ x ≠ e'’
        by (qpat_x_assum ‘¬is_end _ x’ mp_tac >>
            qpat_x_assum ‘∀x. is_end (_ with peer := _) x ⇔ _’ (fn th => rewrite_tac[th]) >>
            simp[]) >> ‘x ≠ e’ by (strip_tac >> fs[]) >>
      simp[APPLY_UPDATE_THM] >> fs[])
  >- ((* a pair *)
      rpt gen_tac >> strip_tac >> rename1 ‘_.peer x = SOME y’ >> Cases_on ‘x = e’
      >- (qpat_x_assum ‘x = e’ SUBST_ALL_TAC >>
          ‘y = e'’ by (qpat_x_assum ‘_.peer e = SOME y’ mp_tac >> simp[APPLY_UPDATE_THM]) >>
          qpat_x_assum ‘y = e'’ SUBST_ALL_TAC >>
          asm_simp_tac (srw_ss()) [APPLY_UPDATE_THM, fresh_lchan_def] >> fs[]) >>
      Cases_on ‘x = e'’
      >- (qpat_x_assum ‘x = e'’ SUBST_ALL_TAC >>
          ‘y = e’ by (qpat_x_assum ‘_.peer e' = SOME y’ mp_tac >> simp[APPLY_UPDATE_THM]) >>
          qpat_x_assum ‘y = e’ SUBST_ALL_TAC >>
          asm_simp_tac (srw_ss()) [APPLY_UPDATE_THM, fresh_lchan_def] >> fs[]) >>
      ‘s.peer x = SOME y’
        by (qpat_x_assum ‘_.peer x = SOME y’ mp_tac >>
            asm_simp_tac (srw_ss()) [APPLY_UPDATE_THM]) >>
      qpat_x_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’
        (fn th => assume_tac th >> drule th >> strip_tac) >>
      ‘is_end s y’ by (qpat_x_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’
                         (qspecl_then [‘y’, ‘x’] mp_tac) >> simp[]) >>
      ‘y ≠ e’
        by (strip_tac >> qpat_x_assum ‘s.peer y = SOME x’ mp_tac >>
            qpat_x_assum ‘y = e’ SUBST1_TAC >>
            qpat_x_assum ‘s.peer e = NONE’ (fn th => rewrite_tac[th]) >> simp[]) >>
      ‘y ≠ e'’
        by (strip_tac >> qpat_x_assum ‘s.peer y = SOME x’ mp_tac >>
            qpat_x_assum ‘y = e'’ SUBST1_TAC >>
            qpat_x_assum ‘s.peer e' = NONE’ (fn th => rewrite_tac[th]) >> simp[]) >>
      ‘sys_chan s1 x = sys_chan s x’
        by (qpat_x_assum ‘∀x. is_end s x ⇒ is_end s1 x ∧ _’ (qspec_then ‘x’ mp_tac) >>
            impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
      ‘sys_chan s1 y = sys_chan s y’
        by (qpat_x_assum ‘∀x. is_end s x ⇒ is_end s1 x ∧ _’ (qspec_then ‘y’ mp_tac) >>
            impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
      asm_simp_tac (srw_ss()) [APPLY_UPDATE_THM]) >>
  (* an unpaired end *)
  rpt gen_tac >> strip_tac >> rename1 ‘_.peer x = NONE’ >> ‘x ≠ e ∧ x ≠ e'’ by (conj_tac >> strip_tac >> fs[APPLY_UPDATE_THM]) >>
  ‘s.peer x = NONE’
    by (qpat_x_assum ‘_.peer x = NONE’ mp_tac >> asm_simp_tac (srw_ss()) [APPLY_UPDATE_THM]) >>
  ‘is_end s x’
    by (qpat_x_assum ‘is_end _ x’ mp_tac >>
        qpat_x_assum ‘∀x. is_end (_ with peer := _) x ⇔ _’ (fn th => rewrite_tac[th]) >>
        simp[]) >>
  ‘sys_chan s1 x = sys_chan s x’
    by (qpat_x_assum ‘∀x. is_end s x ⇒ is_end s1 x ∧ _’ (qspec_then ‘x’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qpat_x_assum ‘∀e. is_end s e ∧ s.peer e = NONE ⇒ _’ (qspec_then ‘x’ mp_tac) >>
  asm_simp_tac (srw_ss()) [APPLY_UPDATE_THM]
QED
