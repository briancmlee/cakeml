(*
  The proxy's step with the ready handles as a list, for the HOL
  translator (which has no sets): preads tests ∈ rdy, the only use of the
  set; the list versions test EXISTS (not MEM, which the translator turns
  into ∈) and agree with the set ones at set rdy.
  pstepl st rdy rs = pstep st (ssnap rdy rs), as the generic E1 driver
  calls it (e1-driver's interface).
*)
Theory proxyStepL
Ancestors
  moonshotProxy asyncM3World
Libs
  preamble

Definition preadsl_def:
  preadsl hw lvs lw nw (rdy : word64 list) p =
    case p.bh of
    | NONE => []
    | SOME c =>
        if p.fo ∧ p.bo then
          (if p.bup ∧ EXISTS (λx. x = p.fh) rdy ∧ pgate hw lvs lw nw c then [ERead p.fh pread]
           else []) ++
          (if EXISTS (λx. x = c) rdy ∧ pgate hw lvs lw nw p.fh then [ERead c pread] else [])
        else []
End

Definition ponel_def:
  ponel b hw lvs lw nw rdy p = pconnects b p ++ pwrites p ++ preadsl hw lvs lw nw rdy p
End

Definition pactsl_def:
  pactsl lfd b hw st (rdy : word64 list) =
    pall plevels st.pc ++
    (if 2 * LENGTH st.pc + 2 ≤ cbound then [(0, EAccept lfd)] else []) ++
    pall (ponel b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy) st.pc
End

Definition pinitl_def:
  pinitl lfd b hw =
    let st = <| pc := []; last := []; lv := [] |> in
      st with last := pactsl lfd b hw st []
End

Definition pstepl_def:
  pstepl lfd b hw st rdy rs =
    let st1 = pupd (st with lv := []) st.last rs in
      st1 with last := pactsl lfd b hw st1 rdy
End

Theorem preadsl_set:
  preadsl hw lvs lw nw rdy p = preads hw lvs lw nw (set rdy) p
Proof
  simp[preadsl_def, preads_def, EXISTS_MEM]
QED

Theorem pactsl_set:
  pactsl lfd b hw st rdy = pacts lfd b hw st (set rdy)
Proof
  ‘∀lvs lw nw. ponel b hw lvs lw nw rdy = pone b hw lvs lw nw (set rdy)’
    by simp[FUN_EQ_THM, ponel_def, pone_def, preadsl_set] >>
  simp[pactsl_def, pacts_def]
QED

Theorem pinitl_pinit:
  pinitl lfd b hw = pinit lfd b hw
Proof
  simp[pinitl_def, pinit_def, pactsl_set]
QED

Theorem pstepl_ssnap:
  pstepl lfd b hw st rdy rs = pstep lfd b hw st (ssnap rdy rs)
Proof
  simp[pstepl_def, pstep_def, ssnap_def, pactsl_set]
QED

(*---------------------------------------------------------------------------*)
(* Index-free forms of pall and pupd, for the translator (no EL) *)

Definition palll_def:
  palll (f : pconn -> eact list) (n : num) [] = [] ∧
  palll f n (p :: ps) = MAP (λx. (n, x)) (f p) ++ palll f (n + 1) ps
End

Theorem palll_GENLIST:
  ∀ps n. palll f n ps = FLAT (GENLIST (λi. MAP (λx. (i + n, x)) (f (EL i ps))) (LENGTH ps))
Proof
  Induct >> simp[palll_def] >> rw[GSYM ADD1, GENLIST_CONS, o_DEF] >> simp[ADD1] >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ]
QED

Theorem pall_palll:
  pall f ps = palll f 0 ps
Proof
  simp[pall_def, palll_GENLIST]
QED

Definition upd_at_def:
  upd_at (g : pconn -> pconn) (n : num) [] = [] ∧
  upd_at g n (x :: xs) = if n = 0 then g x :: xs else x :: upd_at g (n - 1) xs
End

Theorem upd_at_LUPDATE:
  ∀l n. upd_at g n l = LUPDATE (g (EL n l)) n l
Proof
  Induct >> rw[upd_at_def, LUPDATE_def] >> Cases_on ‘n’ >> fs[LUPDATE_def]
QED

Theorem pupd_upd_at:
  (∀st rs. pupd st [] rs = st) ∧
  (∀st xs. pupd st xs [] = st) ∧
  (∀st i x xs r rs.
     pupd st ((i, x) :: xs) (r :: rs) =
     pupd (case (x, r) of
           | (ELevel h, ELvl l) => st with lv := (h, l) :: st.lv
           | (EAccept _, EAccepted (SOME hd)) => st with pc := st.pc ++ [pnew hd]
           | (EAccept _, _) => st
           | _ => st with pc := upd_at (λp. pres p x r) i st.pc)
          xs rs)
Proof
  rpt conj_tac >- simp[pupd_def] >- (Cases_on ‘xs’ >> simp[pupd_def] >> PairCases_on ‘h’ >> simp[pupd_def]) >>
  simp[pupd_def, upd_at_LUPDATE]
QED

Definition pupdl_def:
  pupdl st [] rs = st ∧
  pupdl st _ [] = st ∧
  pupdl st ((i, x) :: xs) (r :: rs) =
    pupdl (case (x, r) of
           | (ELevel h, ELvl l) => st with lv := (h, l) :: st.lv
           | (EAccept _, EAccepted (SOME hd)) => st with pc := st.pc ++ [pnew hd]
           | (EAccept _, _) => st
           | _ => st with pc := upd_at (λp. pres p x r) i st.pc)
          xs rs
End

Theorem pupd_pupdl:
  ∀st xs rs. pupd st xs rs = pupdl st xs rs
Proof
  ho_match_mp_tac pupdl_ind >> rw[pupd_def, pupdl_def, upd_at_LUPDATE]
QED
