(*
  The proxy's step with the ready handles as a list, for the HOL
  translator (which has no sets): preads tests ∈ rdy, the only use of the
  set; the list versions test MEM and agree with the set ones at set rdy.
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
          (if p.bup ∧ MEM p.fh rdy ∧ pgate hw lvs lw nw c then [ERead p.fh pread] else []) ++
          (if MEM c rdy ∧ pgate hw lvs lw nw p.fh then [ERead c pread] else [])
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
  simp[preadsl_def, preads_def]
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
