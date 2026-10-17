(*
  The proxy's side of the generic E1 driver's interface (e1-driver), in
  one place: the fold program (proxyFold.pprog_fold) and, for its pieces,
  the translated functions (proxyProg) with the equations that relate them
  to the model:
    init  pinit lfd b hw                      = pinitl lfd b hw    (pinitl_v_thm)
    step  λst rdy rs. pstep lfd b hw st (ssnap rdy rs)
                                              = pstepl lfd b hw    (pstepl_v_thm)
    acts  λst. MAP SND st.last                 = pacts_of          (pacts_of_v_thm)
    ifds  pifds lfd b hw h = pifds_of lfd (FOLDL (pstep lfd b hw) (pinit lfd b hw) h)
                                                                   (pifds_of_v_thm)
    fin   K F                                  = pfin              (pfin_v_thm)
  The pause policy is pol_never (e1TypesProg's pol_never_v_thm).
*)
Theory proxyCerts
Ancestors
  proxyProg proxyFold proxyStepL moonshotProxy asyncM3World
Libs
  preamble

Theorem proxy_init_eq:
  pinit lfd b hw = pinitl lfd b hw
Proof
  simp[pinitl_pinit]
QED

Theorem proxy_step_eq:
  (λst rdy rs. pstep lfd b hw st (ssnap rdy rs)) = pstepl lfd b hw
Proof
  simp[FUN_EQ_THM, pstepl_ssnap]
QED

Theorem proxy_acts_eq:
  (λst. MAP SND st.last) = pacts_of
Proof
  simp[FUN_EQ_THM, pacts_of_def]
QED

Theorem proxy_fin_eq:
  (K F : pst -> bool) = pfin
Proof
  simp[FUN_EQ_THM, pfin_def]
QED

Theorem proxy_ifds_eq:
  pifds lfd b hw h = pifds_of lfd (FOLDL (pstep lfd b hw) (pinit lfd b hw) h)
Proof
  simp[pifds_def, pifds_of_def, pstate_def]
QED
