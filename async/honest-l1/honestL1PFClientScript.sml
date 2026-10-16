(*
  Live-data, part (B) (design/36 §6): what L1 fetches on an fd f is client
  j's data in the version-2 world built from its run (psk), with
  j = cl (pcm a) f for f's accept round a; FEof / FReset on f become
  Eof2 j.  Then (A) and (B) together: what c's kernel inbox holds is
  eventually client j's data in psk, unless the episode ended.
*)
Theory honestL1PFClient
Ancestors
  honestL1PFStream honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel
  honestL1Model honestL0World honestL0 socketV2FFI asyncCore alist
Libs
  preamble

(* Client j's data, and whether it ended, in a list of v2 arrivals *)
Definition cdata_def:
  cdata j as =
    FLAT (MAP (λa. case a of Data2 i bs => if i = j then bs else [] | _ => []) as)
End

Definition cend_def:
  cend j as ⇔ MEM (Eof2 j) as
End

Theorem cdata_simps[simp]:
  cdata j [] = [] ∧
  cdata j (Data2 i bs :: as) = (if i = j then bs else []) ++ cdata j as ∧
  cdata j (Eof2 i :: as) = cdata j as ∧
  cdata j (Connect2 l :: as) = cdata j as ∧
  (cend j [] ⇔ F) ∧
  (cend j (Data2 i bs :: as) ⇔ cend j as) ∧
  (cend j (Eof2 i :: as) ⇔ i = j ∨ cend j as) ∧
  (cend j (Connect2 l :: as) ⇔ cend j as)
Proof
  rw[cdata_def, cend_def] >> metis_tac[]
QED

(* The fds a fetch log reports input on *)
Definition log_fds_def:
  log_fds l = FLAT (MAP (λx. case x of FData g bs => [g] | FEof g => [g]
                                     | FReset g => [g] | FConn g => []) l)
End

Definition log_conns_def:
  log_conns l = FLAT (MAP (λx. case x of FConn g => [g] | _ => []) l)
End

Theorem cl_other:
  ALL_DISTINCT (MAP SND cm) ∧ ALOOKUP cm f = SOME j ∧ MEM g (MAP FST cm) ∧ g ≠ f ⇒
  cl cm g ≠ j
Proof
  rw[cl_def] >> CASE_TAC >- gvs[ALOOKUP_NONE] >>
  strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
  metis_tac[snd_unique]
QED

(* arrs turns f's entries into client j's arrivals, given that every fd the
   log reports input on is mapped, and that f is not reconnected *)
Theorem arrs_client:
  ∀l cm k as cm' k'.
    arrs lfd (cm, k) l = (as, (cm', k')) ∧
    ALL_DISTINCT (MAP SND cm) ∧ EVERY (λi. i < k) (MAP SND cm) ∧
    ALOOKUP cm f = SOME j ∧
    (∀g. MEM g (log_fds l) ⇒ MEM g (MAP FST cm)) ∧ ¬MEM f (log_conns l) ⇒
    cdata j as = fdata f l ∧ (cend j as ⇔ fend f l) ∧ ALOOKUP cm' f = SOME j
Proof
  Induct >- simp[arrs_def] >>
  Cases >> rpt gen_tac >> simp[arrs_def] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[log_fds_def, log_conns_def]
  >- ((* FConn *)
      first_x_assum drule >> impl_tac
      >- (gvs[EVERY_MEM] >> rpt conj_tac >> rpt strip_tac >> gvs[] >>
          TRY (qpat_x_assum ‘∀i. MEM i _ ⇒ _’ drule >> simp[] >> NO_TAC) >>
          res_tac >> gvs[]) >>
      simp[])
  >> first_x_assum drule >> simp[] >> strip_tac >> simp[] >>
  ‘cl cm c = j ⇔ c = f’
    by (eq_tac
        >- (strip_tac >> CCONTR_TAC >>
            ‘MEM c (MAP FST cm)’
              by (qpat_x_assum ‘∀g. _ ⇒ MEM g (MAP FST cm)’ (qspec_then ‘c’ mp_tac) >>
                  simp[]) >>
            metis_tac[cl_other]) >>
        rw[] >> simp[cl_def]) >>
  simp[] >> rw[] >> gvs[]
QED
