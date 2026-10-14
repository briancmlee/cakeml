(*
  Recursion at Level 2.

  A Level 2 computation is a pair of functions of the history (run and
  interest).  Packing them into one function of the history,

     pack c = λh. (c.run h, c.interest h)

  lets us reuse the guarded-recursion machinery of asyncCore unchanged:
  fix2 is fix on packed computations.  The rule is the same as at Level 1:
  a recursive call may appear anywhere after something that needs a
  snapshot (guarded2_bind2).

  Main results: fix2 unfolds (fix2_unfold); erasing a Level 2 fixpoint gives
  the Level 1 fixpoint of the erased body (erase_fix2); and a body that
  preserves Level 2 well-formedness (well-formed and quiet) gives a
  well-formed, quiet fixpoint (wf2_fix2).
*)
Theory asyncLoop2
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncLevel2
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Packing a Level 2 computation into one function of the history
   ------------------------------------------------------------------------ *)

Definition pack_def:
  pack c = λh. (c.run h, c.interest h)
End

Definition unpack_def:
  unpack f = <| run := λh. FST (f h); interest := λh. SND (f h) |>
End

Theorem unpack_pack[simp]:
  unpack (pack c) = c
Proof
  simp[pack_def, unpack_def, comp2_component_equality, FUN_EQ_THM]
QED

Theorem pack_unpack[simp]:
  pack (unpack f) = f
Proof
  simp[pack_def, unpack_def, FUN_EQ_THM]
QED

(* Agreeing on short histories, for packed computations *)
Theorem agree_below_pack:
  agree_below n (pack c1) (pack c2) ⇔
    ∀h. LENGTH h < n ⇒ c1.run h = c2.run h ∧ c1.interest h = c2.interest h
Proof
  simp[agree_below_def, pack_def]
QED

(* ------------------------------------------------------------------------
   Guarded recursion at Level 2
   ------------------------------------------------------------------------ *)

(* A Level 2 body, seen as a body on packed computations *)
Definition lift_body_def:
  lift_body body2 = λR p. pack (body2 (λq. unpack (R q)) p)
End

Definition guarded2_def:
  guarded2 G ⇔ guarded (λR. pack (G (λq. unpack (R q))))
End

Definition nonexpansive2_def:
  nonexpansive2 G ⇔ nonexpansive (λR. pack (G (λq. unpack (R q))))
End

Definition contractive2_def:
  contractive2 body2 ⇔ ∀p. guarded2 (λR. body2 R p)
End

Definition fix2_def:
  fix2 body2 p = unpack (fix (lift_body body2) p)
End

Theorem contractive2_lift:
  contractive2 body2 ⇔ contractive (lift_body body2)
Proof
  simp[contractive2_def, contractive_def, guarded2_def, lift_body_def]
QED

(* MAIN: a guarded recursive Level 2 definition can be unfolded once *)
Theorem fix2_unfold:
  contractive2 body2 ⇒ fix2 body2 = body2 (fix2 body2)
Proof
  rw[contractive2_lift, FUN_EQ_THM]
  >> simp[fix2_def]
  >> drule fix_unfold >> disch_then (fn th => simp[Once th])
  >> simp[lift_body_def]
  >> ‘(λq. unpack (fix (λR p. pack (body2 (λq. unpack (R q)) p)) q)) = fix2 body2’
       by simp[FUN_EQ_THM, fix2_def, lift_body_def]
  >> simp[]
QED

(* MAIN: erasing a Level 2 fixpoint gives the Level 1 fixpoint of the erased
   body *)
Theorem erase_fix2:
  contractive body1 ∧ contractive2 body2 ∧
  (∀R p. erase (body2 R p) = body1 (λq. erase (R q)) p) ⇒
  ∀p. erase (fix2 body2 p) = fix body1 p
Proof
  strip_tac
  >> ‘(λp. erase (fix2 body2 p)) = fix body1’ suffices_by simp[FUN_EQ_THM]
  >> irule fix_unique >> simp[FUN_EQ_THM] >> qx_gen_tac ‘p’
  >> qpat_x_assum ‘∀R p. _’ (qspecl_then [‘fix2 body2’, ‘p’] mp_tac)
  >> drule fix2_unfold >> disch_then (fn th => REWRITE_TAC[GSYM th])
  >> simp[]
QED

Theorem nonexpansive2_call:
  nonexpansive2 (λR. R p)
Proof
  simp[nonexpansive2_def, nonexpansive_call]
QED

Theorem nonexpansive2_const:
  nonexpansive2 (λR. c)
Proof
  simp[nonexpansive2_def, nonexpansive_const]
QED

(* bind2 only looks at its arguments on shorter histories *)
Theorem bind2_agree:
  agree_below n (pack c) (pack c') ∧ (∀x. agree_below n (pack (f x)) (pack (f' x))) ⇒
  agree_below n (pack (bind2 c f)) (pack (bind2 c' f'))
Proof
  simp[agree_below_pack] >> strip_tac >> qx_gen_tac ‘h’ >> strip_tac
  >> ‘agree_below n c.run c'.run ∧ ∀x. agree_below n (f x).run (f' x).run’
       by simp[agree_below_def]
  >> ‘agree_below n (bind c.run (λx. (f x).run)) (bind c'.run (λx. (f' x).run))’
       by (irule bind_agree >> simp[])
  >> conj_tac >- fs[bind2_def, agree_below_def]
  >> simp[bind2_def, bind_interest_def]
  >> ‘first_prefix (λp. (c.run p).result ≠ NONE) h =
      first_prefix (λp. (c'.run p).result ≠ NONE) h’
       by (irule first_prefix_cong >> rw[] >> fs[LENGTH_TAKE_EQ] >> rw[])
  >> simp[] >> CASE_TAC >> simp[]
  >> rename1 ‘TAKE j h’
  >> ‘j ≤ LENGTH h’ by fs[first_prefix_SOME]
  >> ‘c.run (TAKE j h) = c'.run (TAKE j h)’ by fs[]
  >> ‘new_actions (log_of c.run) (TAKE j h) = new_actions (log_of c'.run) (TAKE j h)’
       by (irule new_actions_cong >> rw[log_of_def])
  >> simp[]
QED

Theorem bind2_agree_guarded:
  (c.run []).result = NONE ∧ (∀x. agree_below n (pack (f x)) (pack (f' x))) ⇒
  agree_below (n + 1) (pack (bind2 c f)) (pack (bind2 c f'))
Proof
  simp[agree_below_pack] >> strip_tac >> qx_gen_tac ‘h’ >> strip_tac
  >> ‘∀x. agree_below n (f x).run (f' x).run’ by simp[agree_below_def]
  >> ‘agree_below (n + 1) (bind c.run (λx. (f x).run)) (bind c.run (λx. (f' x).run))’
       by (irule bind_agree_guarded >> simp[])
  >> conj_tac >- fs[bind2_def, agree_below_def]
  >> simp[bind2_def, bind_interest_def]
  >> CASE_TAC >> simp[]
  >> rename1 ‘TAKE j h’
  >> ‘j ≠ 0’ by (strip_tac >> gvs[first_prefix_SOME])
  >> ‘j ≤ LENGTH h’ by fs[first_prefix_SOME]
  >> simp[]
QED

Theorem nonexpansive2_bind2:
  nonexpansive2 (λR. M R) ∧ (∀x. nonexpansive2 (λR. G x R)) ⇒
  nonexpansive2 (λR. bind2 (M R) (λx. G x R))
Proof
  rw[nonexpansive2_def, nonexpansive_def] >> irule bind2_agree >> simp[]
QED

(* MAIN: the recursion rule at Level 2 *)
Theorem guarded2_bind2:
  (c.run []).result = NONE ∧ (∀x. nonexpansive2 (λR. G x R)) ⇒
  guarded2 (λR. bind2 c (λx. G x R))
Proof
  rw[guarded2_def, nonexpansive2_def, guarded_def, nonexpansive_def]
  >> irule bind2_agree_guarded >> simp[]
QED

(* ------------------------------------------------------------------------
   Well-formedness of Level 2 fixpoints
   ------------------------------------------------------------------------ *)

(* A Level 2 computation that never finishes and waits for nothing *)
Definition never2_def:
  never2 = <| run := never; interest := K ∅ |>
End

Theorem first_some_never[local]:
  ∀l. first_some (λs. NONE) l = NONE
Proof
  Induct >> simp[first_some_def]
QED

Theorem wf2_never2:
  wf2 never2
Proof
  simp[wf2_def, never2_def, quiet_def, never_def, wait_def, wf_wait,
       first_some_never]
QED

Theorem wf2_closed:
  closed (λF. wf2 (unpack F))
Proof
  rw[closed_def, wf2_def] >> rename1 ‘unpack m’
  >- (simp[wf_def, unpack_def] >> rpt gen_tac
      >> first_x_assum (qspec_then ‘LENGTH h + 2’ strip_assume_tac)
      >> rename1 ‘agree_below _ _ m'’
      >> gvs[wf_def, unpack_def, agree_below_def]
      >> ‘m h = m' h ∧ m (h ++ [s]) = m' (h ++ [s])’ by simp[]
      >> simp[])
  >> simp[quiet_def] >> rpt gen_tac >> strip_tac
  >> first_x_assum (qspec_then ‘LENGTH h + LENGTH h' + 2’ strip_assume_tac)
  >> rename1 ‘agree_below _ _ m'’
  >> gvs[quiet_def, unpack_def]
  >> ‘∀k. LENGTH k < LENGTH h + (LENGTH h' + 2) ⇒ m k = m' k’
       by fs[agree_below_def]
  >> ‘m (h ++ [s] ++ h') = m' (h ++ [s] ++ h') ∧ m (h ++ h') = m' (h ++ h') ∧
      m h = m' h’
       by (rpt conj_tac >> first_x_assum irule >> simp[])
  >> ‘new_actions (log_of (λh. FST (m h))) h = new_actions (log_of (λh. FST (m' h))) h’
       by (irule new_actions_cong >> rw[log_of_def] >> AP_TERM_TAC
           >> first_x_assum irule >> simp[])
  >> first_x_assum (qspecl_then [‘h’, ‘s’, ‘h'’] mp_tac)
  >> gvs[]
QED

(* MAIN: a guarded recursive Level 2 definition whose body preserves Level 2
   well-formedness (well-formed and quiet) is well-formed and quiet *)
Theorem wf2_fix2:
  contractive2 body2 ∧ (∀R. (∀p. wf2 (R p)) ⇒ ∀p. wf2 (body2 R p)) ⇒
  ∀p. wf2 (fix2 body2 p)
Proof
  rw[contractive2_lift, fix2_def]
  >> ‘∀p. (λF. wf2 (unpack F)) (fix (lift_body body2) p)’ suffices_by simp[]
  >> irule fix_preserves >> simp[wf2_closed]
  >> conj_tac
  >- (qexists_tac ‘pack never2’ >> simp[wf2_never2])
  >> simp[lift_body_def]
QED

(* ------------------------------------------------------------------------
   Level 2 well-formedness of the primitives and bind2
   ------------------------------------------------------------------------ *)

Theorem wf2_return2:
  wf2 (return2 x)
Proof
  simp[wf2_def, quiet_return2] >> simp[return2_def, wf_return]
QED

Theorem wf2_wait_on:
  wf2 (wait_on e p)
Proof
  simp[wf2_def, quiet_wait_on] >> simp[wait_on_def, wf_wait]
QED

Theorem wf2_emit2:
  wf2 (emit2 a)
Proof
  simp[wf2_def, quiet_emit2] >> simp[emit2_def, wf_emit]
QED

Theorem wf2_bind2:
  wf2 c ∧ (∀x. wf2 (f x)) ⇒ wf2 (bind2 c f)
Proof
  rw[wf2_def]
  >- (simp[bind2_def] >> irule wf_bind >> simp[])
  >> irule quiet_bind2 >> simp[]
QED
