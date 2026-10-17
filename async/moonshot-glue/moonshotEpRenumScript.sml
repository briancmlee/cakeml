(*
  [R3] Episodes and channels, renumbered.  Under r3-close's (A), a connect
  that got a socket but failed at once, transiently (tconn), has L1 close
  the socket and report EConnected NONE: L1 makes no channel of it, but
  l0sysEpisodes counts it as an episode.  So the trace's episodes are E1's
  channels with some extra, transient ones.

  The channel numbering (cep_io) is l0sysEpisodes' ep_io with the
  transient connects not counted; tsig maps an episode to its channel
  (NONE: transient).  On any trace where nothing is sent (or received)
  on a fd whose latest episode is transient (nodead), episode j's bytes
  are its channel's, and a transient episode's are none.
*)
Theory moonshotEpRenum
Ancestors
  l0sysEpisodes honestL1Model
Libs
  preamble

(* A connect that got a socket (value not 0) but failed transiently *)
Definition tconn_def:
  tconn ev ⇔
    ∃conf bl e x.
      ev = IO_event (ExtCall «sys_connect») conf bl ∧ LENGTH conf = 2 ∧
      dec_res (MAP SND bl) = SOME (Fail e x) ∧ l1_transient e ∧
      l0sysEpisodes$res_val (MAP SND bl) ≠ 0
End

Theorem tconn_new:
  tconn ev ⇒ ∃f p. ev_new ev = SOME (f, INL p)
Proof
  rw[tconn_def] >> simp[ev_new_def]
QED

(* The channel numbering: transient connects start no channel *)
Definition cev_new_def:
  cev_new ev = if tconn ev then NONE else ev_new ev
End

Theorem cev_new_none:
  ev_new ev = NONE ⇒ cev_new ev = NONE
Proof
  simp[cev_new_def]
QED

Definition cep_io_def:
  cep_io sel (j : num) (opn : (word64 # num) list) (n : num) [] = [] ∧
  cep_io sel j opn n (ev :: evs) =
    (case sel ev of
     | SOME (f, bs) => if ALOOKUP opn f = SOME j then bs else []
     | NONE => []) ++
    (case cev_new ev of
     | SOME (f, _) => cep_io sel j (if f = 0w then opn else (f, n) :: opn) (n + 1) evs
     | NONE => cep_io sel j opn n evs)
End

(* Episode to channel: the transient episodes map to NONE *)
Definition snext_def:
  snext (sg : num option list, k : num) ev =
    case ev_new ev of
    | NONE => (sg, k)
    | SOME _ => if tconn ev then (sg ++ [NONE], k) else (sg ++ [SOME k], k + 1)
End

Definition sat_def:
  sat (sg : num option list) t = if t < LENGTH sg then EL t sg else NONE
End

Definition tsig_def:
  tsig evs j = sat (FST (FOLDL snext ([], 0) evs)) j
End

(* The fds whose latest episode is transient *)
Definition dnext_def:
  dnext (D : word64 list) ev =
    case ev_new ev of
    | NONE => D
    | SOME (f, _) => if tconn ev then f :: D else FILTER (λg. g ≠ f) D
End

(* Nothing picked by sel on such a fd *)
Definition nodead_def:
  nodead sel D evs ⇔
    ∀pre ev post f bs.
      evs = pre ++ ev :: post ∧ sel ev = SOME (f, bs) ∧ MEM f (FOLDL dnext D pre) ⇒ bs = []
End

Theorem nodead_nil[simp]:
  nodead sel D []
Proof
  simp[nodead_def]
QED

Theorem nodead_cons:
  nodead sel D (ev :: evs) ⇔
    (∀f bs. sel ev = SOME (f, bs) ∧ MEM f D ⇒ bs = []) ∧ nodead sel (dnext D ev) evs
Proof
  simp[nodead_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspecl_then [‘[]’, ‘ev’, ‘evs’] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [‘ev :: pre’, ‘ev'’, ‘post’] mp_tac) >> simp[])
  >> Cases_on ‘pre’ >> gvs[] >> metis_tac[]
QED

Theorem nodead_append:
  ∀xs D. nodead sel D (xs ++ ys) ⇔ nodead sel D xs ∧ nodead sel (FOLDL dnext D xs) ys
Proof
  Induct >> simp[nodead_cons] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The map: injective on channels, extended at the end
   ------------------------------------------------------------------------ *)

Definition sinj_def:
  sinj sg ⇔ ∀t t' c. sat sg t = SOME c ∧ sat sg t' = SOME c ⇒ t = t'
End

Definition sbnd_def:
  sbnd sg k ⇔ ∀t c. sat sg t = SOME c ⇒ c < k
End

Theorem sat_append:
  t < LENGTH sg ⇒ sat (sg ++ x) t = sat sg t
Proof
  simp[sat_def, EL_APPEND1]
QED

Theorem sat_none_snoc:
  sat (sg ++ [NONE]) = sat sg
Proof
  simp[FUN_EQ_THM, sat_def] >> rw[] >> gvs[EL_APPEND1, EL_APPEND2] >>
  ‘x = LENGTH sg’ by simp[] >> simp[EL_APPEND2]
QED

Theorem sat_some_snoc:
  sat (sg ++ [SOME k]) t = if t = LENGTH sg then SOME k else sat sg t
Proof
  simp[sat_def] >> rw[] >> gvs[EL_APPEND1, EL_APPEND2]
QED

Theorem snext_props:
  sinj sg ∧ sbnd sg k ∧ snext (sg, k) ev = (sg', k') ⇒
  sinj sg' ∧ sbnd sg' k' ∧ k ≤ k' ∧
  (∀t. t < LENGTH sg ⇒ sat sg' t = sat sg t) ∧
  (∀t c. LENGTH sg ≤ t ∧ sat sg' t = SOME c ⇒ k ≤ c) ∧
  LENGTH sg' = LENGTH sg + (if ev_new ev = NONE then 0 else 1)
Proof
  simp[snext_def] >> every_case_tac >> rw[] >>
  gvs[sat_none_snoc, sat_some_snoc, sat_append, sinj_def, sbnd_def] >> rw[] >>
  gvs[sat_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >> res_tac >> gvs[]
QED

Theorem snext_fold:
  ∀evs sg k.
    sinj sg ∧ sbnd sg k ⇒
    sinj (FST (FOLDL snext (sg, k) evs)) ∧ sbnd (FST (FOLDL snext (sg, k) evs)) (SND (FOLDL snext (sg, k) evs)) ∧
    (∀t. t < LENGTH sg ⇒ sat (FST (FOLDL snext (sg, k) evs)) t = sat sg t) ∧
    (∀t c. LENGTH sg ≤ t ∧ sat (FST (FOLDL snext (sg, k) evs)) t = SOME c ⇒ k ≤ c)
Proof
  Induct >- simp[sat_def] >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘snext (sg, k) h’ >> rename1 ‘_ = (sg1, k1)’ >>
  drule_all snext_props >> strip_tac >>
  first_x_assum (qspecl_then [‘sg1’, ‘k1’] mp_tac) >> simp[] >> strip_tac >>
  rpt strip_tac
  >- (‘sat (FST (FOLDL snext (sg1, k1) evs)) t = sat sg1 t’
        by (first_x_assum irule >> rw[]) >> simp[])
  >> Cases_on ‘t < LENGTH sg + (if ev_new h = NONE then 0 else 1)’
  >- (‘sat sg1 t = SOME c’ by metis_tac[] >> res_tac >> simp[])
  >> ‘k1 ≤ c’ by (first_x_assum irule >> qexists_tac ‘t’ >> fs[NOT_LESS]) >> simp[]
QED

Theorem tsig_inj:
  tsig evs j = SOME c ∧ tsig evs j' = SOME c ⇒ j = j'
Proof
  rw[tsig_def] >>
  qspecl_then [‘evs’, ‘[]’, ‘0’] mp_tac snext_fold >>
  impl_tac >- simp[sinj_def, sbnd_def, sat_def] >>
  simp[sinj_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The renumbering
   ------------------------------------------------------------------------ *)

Theorem renum_inv_tconn:
  ∀opn cm sg D f.
  ALOOKUP opn 0w = NONE ∧
  (∀g. ¬MEM g D ⇒ OPTION_BIND (ALOOKUP opn g) (sat sg) = ALOOKUP cm g) ∧
  (∀g t. ALOOKUP opn g = SOME t ∧ sat sg t = NONE ⇒ MEM g D) ⇒
  ALOOKUP (if f = 0w then opn else (f, LENGTH sg) :: opn) 0w = NONE ∧
  (∀g. ¬MEM g (f :: D) ⇒
       OPTION_BIND (ALOOKUP (if f = 0w then opn else (f, LENGTH sg) :: opn) g)
                   (sat (sg ++ [NONE])) = ALOOKUP cm g) ∧
  (∀g t. ALOOKUP (if f = 0w then opn else (f, LENGTH sg) :: opn) g = SOME t ∧
         sat (sg ++ [NONE]) t = NONE ⇒ MEM g (f :: D))
Proof
  rpt gen_tac >> simp[sat_none_snoc] >> strip_tac >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem renum_inv_new:
  ∀opn cm kc sg D f.
  ALOOKUP opn 0w = NONE ∧ ALOOKUP cm 0w = NONE ∧
  (∀g c. ALOOKUP cm g = SOME c ⇒ c < kc) ∧
  (∀g. ¬MEM g D ⇒ OPTION_BIND (ALOOKUP opn g) (sat sg) = ALOOKUP cm g) ∧
  (∀g t. ALOOKUP opn g = SOME t ∧ sat sg t = NONE ⇒ MEM g D) ⇒
  ALOOKUP (if f = 0w then opn else (f, LENGTH sg) :: opn) 0w = NONE ∧
  ALOOKUP (if f = 0w then cm else (f, kc) :: cm) 0w = NONE ∧
  (∀g c. ALOOKUP (if f = 0w then cm else (f, kc) :: cm) g = SOME c ⇒ c < kc + 1) ∧
  (∀g. ¬MEM g (FILTER (λg. g ≠ f) D) ⇒
       OPTION_BIND (ALOOKUP (if f = 0w then opn else (f, LENGTH sg) :: opn) g)
                   (sat (sg ++ [SOME kc])) =
       ALOOKUP (if f = 0w then cm else (f, kc) :: cm) g) ∧
  (∀g t. ALOOKUP (if f = 0w then opn else (f, LENGTH sg) :: opn) g = SOME t ∧
         sat (sg ++ [SOME kc]) t = NONE ⇒ MEM g (FILTER (λg. g ≠ f) D))
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- rw[]
  >- rw[]
  >- (rw[] >> pop_assum mp_tac >> rw[] >> res_tac >> simp[])
  >- (rpt strip_tac >> Cases_on ‘g = f’
      >- (qpat_x_assum ‘g = f’ SUBST_ALL_TAC >> Cases_on ‘f = 0w’ >>
          asm_simp_tac (srw_ss()) [sat_some_snoc]) >>
      ‘¬MEM g D’ by (qpat_x_assum ‘¬MEM g (FILTER _ _)’ mp_tac >> asm_simp_tac (srw_ss()) [MEM_FILTER]) >>
      ‘ALOOKUP (if f = 0w then opn else (f, LENGTH sg) :: opn) g = ALOOKUP opn g’
        by (qpat_assum ‘g ≠ f’ (fn th => rw[th, GSYM th])) >>
      pop_assum SUBST1_TAC >>
      ‘ALOOKUP (if f = 0w then cm else (f, kc) :: cm) g = ALOOKUP cm g’
        by (qpat_assum ‘g ≠ f’ (fn th => rw[th, GSYM th])) >>
      pop_assum SUBST1_TAC >>
      Cases_on ‘ALOOKUP opn g’
      >- (qpat_x_assum ‘∀g. ¬MEM g D ⇒ _’ (qspec_then ‘g’ mp_tac) >>
          qpat_assum ‘¬MEM g D’ (fn th => REWRITE_TAC [th]) >>
          qpat_assum ‘ALOOKUP opn g = _’ (fn th => REWRITE_TAC [th]) >>
          simp_tac (srw_ss()) []) >>
      rename1 ‘ALOOKUP opn g = SOME t’ >>
      Cases_on ‘sat sg t’
      >- (qpat_x_assum ‘∀g t. _ ⇒ MEM g D’ (qspecl_then [‘g’, ‘t’] mp_tac) >>
          asm_rewrite_tac []) >>
      ‘t ≠ LENGTH sg’
        by (strip_tac >> qpat_x_assum ‘sat sg t = SOME _’ mp_tac >> asm_simp_tac std_ss [sat_def]) >>
      qpat_x_assum ‘∀g. ¬MEM g D ⇒ _’ (qspec_then ‘g’ mp_tac) >>
      asm_simp_tac (srw_ss()) [sat_some_snoc])
  >> rpt strip_tac >> Cases_on ‘f = 0w’ >> gvs[sat_some_snoc, MEM_FILTER, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem renum_gen:
  ∀evs opn kt cm kc sg D.
    LENGTH sg = kt ∧ sinj sg ∧ sbnd sg kc ∧
    ALOOKUP opn 0w = NONE ∧ ALOOKUP cm 0w = NONE ∧
    (∀g c. ALOOKUP cm g = SOME c ⇒ c < kc) ∧
    (∀g. ¬MEM g D ⇒ OPTION_BIND (ALOOKUP opn g) (sat sg) = ALOOKUP cm g) ∧
    (∀g t. ALOOKUP opn g = SOME t ∧ sat sg t = NONE ⇒ MEM g D) ∧
    nodead sel D evs ⇒
    ∀j. ep_io sel j opn kt evs =
        case sat (FST (FOLDL snext (sg, kc) evs)) j of
        | SOME c => cep_io sel c cm kc evs
        | NONE => []
Proof
  Induct
  >- (simp[ep_io_def, cep_io_def] >> rpt strip_tac >> CASE_TAC >> simp[]) >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  qpat_x_assum ‘LENGTH sg = kt’ (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac ‘F' = FST (FOLDL snext (sg, kc) (h :: evs))’ >>
  ‘∀t. t < LENGTH sg ⇒ sat F' t = sat sg t’
    by (qspecl_then [‘h :: evs’, ‘sg’, ‘kc’] mp_tac snext_fold >> simp[Abbr ‘F'’]) >>
  ‘sinj F'’
    by (qspecl_then [‘h :: evs’, ‘sg’, ‘kc’] mp_tac snext_fold >> simp[Abbr ‘F'’]) >>
  ‘∀t c. LENGTH sg ≤ t ∧ sat F' t = SOME c ⇒ kc ≤ c’
    by (qspecl_then [‘h :: evs’, ‘sg’, ‘kc’] mp_tac snext_fold >>
        impl_tac >- simp[] >> strip_tac >> rpt strip_tac >>
        qpat_x_assum ‘∀t c. LENGTH sg ≤ t ∧ _ ⇒ _’ irule >>
        qexists_tac ‘t’ >> fs[Abbr ‘F'’]) >>
  qpat_x_assum ‘nodead _ _ _’ (strip_assume_tac o REWRITE_RULE [nodead_cons]) >>
  (* the head event's bytes *)
  ‘(case sel h of SOME (f, bs) => if ALOOKUP opn f = SOME j then bs else [] | NONE => []) =
   case sat F' j of
   | SOME c => (case sel h of SOME (f, bs) => if ALOOKUP cm f = SOME c then bs else []
                             | NONE => [])
   | NONE => []’
    by (Cases_on ‘sel h’ >> simp[] >- (CASE_TAC >> simp[]) >>
        rename1 ‘sel h = SOME fb’ >> PairCases_on ‘fb’ >> simp[] >>
        rename1 ‘sel h = SOME (f, bs)’ >>
        Cases_on ‘MEM f D’
        >- (‘bs = []’
              by (qpat_x_assum ‘∀f' bs'. _ ∧ MEM f' D ⇒ _’ (qspecl_then [‘f’, ‘bs’] mp_tac) >>
                  asm_rewrite_tac []) >>
            simp[] >> CASE_TAC >> simp[]) >>
        Cases_on ‘ALOOKUP opn f’
        >- (‘ALOOKUP cm f = NONE’
              by (qpat_x_assum ‘∀g. ¬MEM g D ⇒ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
            simp[] >> CASE_TAC >> simp[]) >>
        rename1 ‘ALOOKUP opn f = SOME t’ >>
        Cases_on ‘sat sg t’
        >- (qpat_x_assum ‘∀g t. ALOOKUP opn g = SOME t ∧ _ ⇒ _’ (qspecl_then [‘f’, ‘t’] mp_tac) >>
            asm_rewrite_tac []) >>
        rename1 ‘sat sg t = SOME c0’ >>
        ‘ALOOKUP cm f = SOME c0’
          by (qpat_x_assum ‘∀g. ¬MEM g D ⇒ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
        ‘t < LENGTH sg’
          by (CCONTR_TAC >> qpat_x_assum ‘sat sg t = SOME c0’ mp_tac >> simp[sat_def]) >>
        ‘sat F' t = SOME c0’
          by (qpat_x_assum ‘∀t. t < LENGTH sg ⇒ _’ (qspec_then ‘t’ mp_tac) >> simp[]) >>
        qpat_x_assum ‘ALOOKUP cm f = SOME c0’ (fn th => REWRITE_TAC [th]) >>
        Cases_on ‘t = j’
        >- (qpat_x_assum ‘t = j’ SUBST_ALL_TAC >>
            qpat_x_assum ‘sat F' j = SOME c0’ (fn th => REWRITE_TAC [th]) >>
            simp_tac std_ss []) >>
        qpat_assum ‘t ≠ j’ (fn th => REWRITE_TAC [th, optionTheory.SOME_11]) >>
        Cases_on ‘sat F' j’ >- simp_tac std_ss [] >>
        rename1 ‘sat F' j = SOME c1’ >>
        ‘c0 ≠ c1’
          by (strip_tac >> qpat_x_assum ‘c0 = c1’ SUBST_ALL_TAC >>
              qpat_x_assum ‘sinj F'’ mp_tac >> REWRITE_TAC [sinj_def] >>
              disch_then (qspecl_then [‘t’, ‘j’, ‘c1’] mp_tac) >>
              qpat_x_assum ‘t ≠ j’ mp_tac >>
              qpat_x_assum ‘sat F' j = SOME c1’ mp_tac >>
              qpat_x_assum ‘sat F' t = SOME c1’ mp_tac >>
              rpt (pop_assum kall_tac) >> simp_tac std_ss []) >>
        qpat_x_assum ‘c0 ≠ c1’ mp_tac >> simp_tac std_ss []) >>
  simp[ep_io_def, cep_io_def] >>
  pop_assum SUBST1_TAC >>
  Cases_on ‘snext (sg, kc) h’ >> rename1 ‘snext _ _ = (sg1, kc1)’ >>
  drule_all snext_props >> strip_tac >>
  ‘F' = FST (FOLDL snext (sg1, kc1) evs)’
    by (qpat_x_assum ‘Abbrev _’ mp_tac >> qpat_x_assum ‘snext _ _ = _’ mp_tac >>
        rpt (pop_assum kall_tac) >> simp[markerTheory.Abbrev_def]) >>
  Cases_on ‘ev_new h’
  >- (‘cev_new h = NONE’ by (irule cev_new_none >> first_assum ACCEPT_TAC) >>
      ‘dnext D h = D’
        by (qpat_x_assum ‘ev_new h = NONE’ mp_tac >> rpt (pop_assum kall_tac) >>
            simp[dnext_def]) >>
      ‘sg1 = sg ∧ kc1 = kc’
        by (qpat_x_assum ‘snext _ _ = _’ mp_tac >> qpat_x_assum ‘ev_new h = NONE’ mp_tac >>
            rpt (pop_assum kall_tac) >> simp[snext_def]) >>
      qpat_x_assum ‘sg1 = _’ SUBST_ALL_TAC >> qpat_x_assum ‘kc1 = _’ SUBST_ALL_TAC >>
      qpat_x_assum ‘ev_new h = NONE’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘cev_new h = NONE’ (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) [] >>
      qpat_x_assum ‘∀opn kt cm kc sg D. _’
        (qspecl_then [‘opn’, ‘LENGTH sg’, ‘cm’, ‘kc’, ‘sg’, ‘D’] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >>
          FIRST [REFL_TAC, first_assum ACCEPT_TAC,
                 qpat_x_assum ‘nodead _ (dnext D h) _’ mp_tac >>
                 qpat_x_assum ‘dnext D h = D’ (fn th => REWRITE_TAC [th])]) >>
      disch_then (qspec_then ‘j’ SUBST1_TAC) >>
      qpat_x_assum ‘F' = _’ (SUBST1_TAC o SYM) >>
      Cases_on ‘sat F' j’ >> simp_tac (srw_ss()) []) >>
  rename1 ‘ev_new h = SOME fp’ >> PairCases_on ‘fp’ >> rename1 ‘ev_new h = SOME (f, p)’ >>
  Cases_on ‘tconn h’
  >- (‘cev_new h = NONE’
        by (qpat_assum ‘tconn h’ (fn th => REWRITE_TAC [cev_new_def, th])) >>
      ‘dnext D h = f :: D’
        by (qpat_x_assum ‘ev_new h = _’ mp_tac >> qpat_x_assum ‘tconn h’ mp_tac >>
            rpt (pop_assum kall_tac) >> simp[dnext_def]) >>
      ‘sg1 = sg ++ [NONE] ∧ kc1 = kc’
        by (qpat_x_assum ‘snext _ _ = _’ mp_tac >> qpat_x_assum ‘ev_new h = _’ mp_tac >>
            qpat_x_assum ‘tconn h’ mp_tac >> rpt (pop_assum kall_tac) >> simp[snext_def]) >>
      qpat_x_assum ‘sg1 = _’ SUBST_ALL_TAC >> qpat_x_assum ‘kc1 = _’ SUBST_ALL_TAC >>
      qpat_x_assum ‘ev_new h = _’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘cev_new h = NONE’ (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) [] >>
      qspecl_then [‘opn’, ‘cm’, ‘sg’, ‘D’, ‘f’] mp_tac renum_inv_tconn >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_x_assum ‘∀opn kt cm kc sg D. _’
        (qspecl_then [‘if f = 0w then opn else (f, LENGTH sg) :: opn’, ‘LENGTH sg + 1’,
                      ‘cm’, ‘kc’, ‘sg ++ [NONE]’, ‘f :: D’] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >>
          FIRST [first_assum ACCEPT_TAC, simp_tac (srw_ss()) [] >> NO_TAC,
                 qpat_x_assum ‘nodead _ (dnext D h) _’ mp_tac >>
                 qpat_x_assum ‘dnext D h = _’ (fn th => REWRITE_TAC [th])]) >>
      disch_then (qspec_then ‘j’ SUBST1_TAC) >>
      qpat_x_assum ‘F' = _’ (SUBST1_TAC o SYM) >>
      Cases_on ‘sat F' j’ >> simp_tac (srw_ss()) []) >>
  ‘cev_new h = SOME (f, p)’
    by (qpat_assum ‘¬tconn h’ (fn th => REWRITE_TAC [cev_new_def, th]) >>
        first_assum ACCEPT_TAC) >>
  ‘dnext D h = FILTER (λg. g ≠ f) D’
    by (qpat_x_assum ‘ev_new h = _’ mp_tac >> qpat_x_assum ‘¬tconn h’ mp_tac >>
        rpt (pop_assum kall_tac) >> simp[dnext_def]) >>
  ‘sg1 = sg ++ [SOME kc] ∧ kc1 = kc + 1’
    by (qpat_x_assum ‘snext _ _ = _’ mp_tac >> qpat_x_assum ‘ev_new h = _’ mp_tac >>
        qpat_x_assum ‘¬tconn h’ mp_tac >> rpt (pop_assum kall_tac) >> simp[snext_def]) >>
  qpat_x_assum ‘sg1 = _’ SUBST_ALL_TAC >> qpat_x_assum ‘kc1 = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘ev_new h = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘cev_new h = _’ (fn th => REWRITE_TAC [th]) >>
  simp_tac (srw_ss()) [] >>
  qspecl_then [‘opn’, ‘cm’, ‘kc’, ‘sg’, ‘D’, ‘f’] mp_tac renum_inv_new >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum ‘∀opn kt cm kc sg D. _’
    (qspecl_then [‘if f = 0w then opn else (f, LENGTH sg) :: opn’, ‘LENGTH sg + 1’,
                  ‘if f = 0w then cm else (f, kc) :: cm’, ‘kc + 1’,
                  ‘sg ++ [SOME kc]’, ‘FILTER (λg. g ≠ f) D’] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp_tac (srw_ss()) [] >> NO_TAC,
             qpat_x_assum ‘nodead _ (dnext D h) _’ mp_tac >>
             qpat_x_assum ‘dnext D h = _’ (fn th => REWRITE_TAC [th])]) >>
  disch_then (qspec_then ‘j’ SUBST1_TAC) >>
  qpat_x_assum ‘F' = _’ (SUBST1_TAC o SYM) >>
  Cases_on ‘sat F' j’ >> simp_tac (srw_ss()) []
QED

Theorem ep_io_renum:
  nodead sel [] evs ⇒
  ∀j. ep_io sel j [] 0 evs =
      case tsig evs j of SOME c => cep_io sel c [] 0 evs | NONE => []
Proof
  strip_tac >> simp[tsig_def] >>
  qspecl_then [‘evs’, ‘[]’, ‘0’, ‘[]’, ‘0’, ‘[]’, ‘[]’] mp_tac renum_gen >>
  simp[sinj_def, sbnd_def, sat_def]
QED
