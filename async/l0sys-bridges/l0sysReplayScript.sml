(*
  B1's semantics: a program that, answered as recorded, makes the calls
  evs, makes them against any FFI state that answers them the same: its
  I/O, if it does not fail, extends evs.  Both runs follow the one
  interaction tree (alt_semantics), which does not depend on the FFI.
*)
Theory l0sysReplay
Ancestors
  itree ffi semantics alt_semantics itree_semantics itree_semanticsProps
  itree_semanticsEquiv ml_prog lprefix_lub l0sys
Libs
  preamble

(* An oracle, from state st, answers the calls of evs as recorded *)
Definition agrees_def:
  (agrees orc st [] ⇔ T) ∧
  (agrees orc st (IO_event n conf bl :: rest) ⇔
     ∃st'. orc n st conf (MAP FST bl) = Oracle_return st' (MAP SND bl) ∧ agrees orc st' rest)
End

Theorem cml_unfold:
  cml_itree_unfold_err f seed =
    case f seed of
    | Ret' r => Ret r
    | Div' => Div
    | Vis' e g =>
        Vis e (λa. case a of
                   | INL x => Ret (FinalFFI e x)
                   | INR y => if LENGTH (SND (SND e)) = LENGTH y
                              then cml_itree_unfold_err f (g y)
                              else Ret (FinalFFI e FFI_failed))
Proof
  simp[cml_itree_unfold_err_def, Once itreeTheory.itree_unfold_err] >>
  CASE_TAC >> simp[FUN_EQ_THM] >> rename1 ‘Vis' e g’ >> PairCases_on ‘e’ >>
  Cases >> simp[]
QED

Theorem trace_prefix_Ret_io[simp]:
  FST (trace_prefix n (orc, st) (Ret x)) = []
Proof
  Cases_on ‘n’ >> simp[trace_prefix_def]
QED

Theorem ZIP_MAP_FST_SND:
  ZIP (MAP FST l, MAP SND l) = l
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem replay_trace:
  ∀n evs seed (orc : 'b oracle) (st : 'b).
    agrees orc st evs ⇒
    FST (trace_prefix n (replay_oracle, evs) (cml_itree_unfold_err f seed)) ≼ evs ∧
    FST (trace_prefix n (replay_oracle, evs) (cml_itree_unfold_err f seed)) ≼
    FST (trace_prefix n (orc, st) (cml_itree_unfold_err f seed))
Proof
  Induct >> simp[trace_prefix_def] >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[cml_unfold] >>
  Cases_on ‘f seed’ >> simp[trace_prefix_def] >>
  rename1 ‘Vis' ev g’ >> PairCases_on ‘ev’ >> simp[trace_prefix_def] >>
  Cases_on ‘evs’ >- (Cases_on ‘ev0’ >> simp[replay_oracle_def]) >>
  rename1 ‘agrees orc st (h :: rest)’ >> Cases_on ‘h’ >> rename1 ‘IO_event nm conf bl’ >>
  Cases_on ‘ev0’ >> simp[replay_oracle_def] >> Cases_on ‘nm’ >> simp[replay_oracle_def] >>
  IF_CASES_TAC >> simp[] >> fs[agrees_def] >> rveq >>
  first_x_assum (qspecl_then [‘rest’, ‘g (MAP SND bl)’, ‘orc’, ‘st'’] mp_tac) >>
  simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[ZIP_MAP_FST_SND]
QED

Theorem prefix_FRONT:
  l' ≼ l ∧ l' ≠ l ⇒ l' ≼ TAKE (LENGTH l - 1) l
Proof
  rw[IS_PREFIX_APPEND] >> Cases_on ‘l''’ >> fs[] >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >> metis_tac[]
QED

(* A finite lub of finite lists is one of them *)
Theorem lub_fromList_mem:
  lprefix_lub ls (fromList l) ∧ x0 ∈ ls ∧ (∀x. x ∈ ls ⇒ ∃l'. x = fromList l') ⇒
  fromList l ∈ ls
Proof
  rw[lprefix_lub_def] >>
  ‘∀x. x ∈ ls ⇒ ∃l'. x = fromList l' ∧ l' ≼ l’
    by (rpt strip_tac >> res_tac >> rveq >> res_tac >> fs[LPREFIX_fromList, from_toList]) >>
  CCONTR_TAC >>
  ‘∀x. x ∈ ls ⇒ LPREFIX x (fromList (TAKE (LENGTH l - 1) l))’
    by (rpt strip_tac >> first_x_assum drule >> strip_tac >> rveq >>
        simp[LPREFIX_fromList, from_toList] >> irule prefix_FRONT >> simp[] >>
        strip_tac >> fs[]) >>
  ‘LPREFIX (fromList l) (fromList (TAKE (LENGTH l - 1) l))’ by metis_tac[] >>
  ‘x0 ∈ ls’ by simp[] >> res_tac >>
  fs[LPREFIX_fromList, from_toList] >>
  imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
  Cases_on ‘l’ >> fs[] >> rveq >> fs[]
QED

Theorem init_state_fields[simp]:
  (init_state f).eval_state = NONE ∧ (init_state f).ffi = f
Proof
  simp[init_state_def]
QED

(* The interaction tree does not depend on the FFI *)
Theorem itree_of_init_state:
  itree_of (init_state f1) env prog = itree_of (init_state f2) env prog
Proof
  simp[itree_of_def, dstate_of_def, init_state_def]
QED

Theorem itree_of_unfold:
  ∃F (seed : dstep_result). itree_of st env prog = cml_itree_unfold_err F seed
Proof
  simp[itree_of_def, interp_def] >>
  qmatch_goalsub_abbrev_tac ‘cml_itree_unfold_err G sd’ >> qexistsl_tac [‘G’, ‘sd’] >> simp[]
QED

Theorem replay_trace_itree:
  agrees orc st evs ⇒
  FST (trace_prefix n (replay_oracle, evs) (itree_of st0 env prog)) ≼
  FST (trace_prefix n (orc, st) (itree_of st0 env prog))
Proof
  strip_tac >>
  ‘∃F (seed : dstep_result). itree_of st0 env prog = cml_itree_unfold_err F seed’
    by simp[itree_of_unfold] >>
  simp[] >> irule (cj 2 (SPEC_ALL replay_trace)) >> simp[]
QED

(* The replay's run reaches the whole of evs *)
Theorem prog_makes_trace:
  prog_makes prog evs ⇒
  ∃n. FST (trace_prefix n (replay_oracle, evs)
             (itree_of (init_state (replay_ffi evs)) init_env prog)) = evs
Proof
  rw[prog_makes_def] >>
  Cases_on ‘b’ >> fs[] >> rveq >>
  qpat_x_assum ‘semantics_prog _ _ _ _’ mp_tac >>
  simp[alt_semanticsTheory.itree_semantics] >> strip_tac
  >- (qmatch_asmsub_abbrev_tac ‘lprefix_lub L _’ >>
      ‘fromList evs ∈ L’
        by (irule lub_fromList_mem >> simp[] >> conj_tac
            >- (simp[Abbr ‘L’, PULL_EXISTS]) >>
            qexists_tac ‘fromList []’ >> simp[Abbr ‘L’, replay_ffi_def] >>
            qexists_tac ‘0’ >> simp[trace_prefix_def]) >>
      fs[Abbr ‘L’, replay_ffi_def] >> qexists_tac ‘n’ >> simp[]) >>
  fs[replay_ffi_def] >> qexists_tac ‘n’ >> simp[]
QED

Theorem prefix_end:
  evs ≼ FST (trace_prefix n (orc, st) t) ∧ trace_prefix m (orc, st) t = (io, SOME res) ⇒
  evs ≼ io
Proof
  strip_tac >> Cases_on ‘trace_prefix n (orc, st) t’ >> fs[] >>
  Cases_on ‘n ≤ m’
  >- (drule_all trace_prefix_prefix >> metis_tac[IS_PREFIX_TRANS]) >>
  ‘m ≤ n’ by simp[] >> drule_all trace_prefix_SOME_mono >> fs[] >> rw[] >> fs[]
QED

Theorem prefix_div:
  evs ≼ FST (trace_prefix n (orc, st) t) ∧
  lprefix_lub {fromList ([] ++ io) | io | ∃n res. trace_prefix n (orc, st) t = (io, res)} l ⇒
  LPREFIX (fromList evs) l
Proof
  strip_tac >> Cases_on ‘trace_prefix n (orc, st) t’ >> fs[] >>
  irule LPREFIX_TRANS >> qexists_tac ‘fromList q’ >>
  conj_tac >- simp[LPREFIX_fromList, from_toList] >>
  fs[lprefix_lub_def] >> first_x_assum irule >> metis_tac[]
QED

(* MAIN: against an FFI state that answers evs as recorded, the program's
   I/O extends evs, unless it fails *)
Theorem replay_prefix:
  prog_makes prog evs ∧ agrees f.oracle f.ffi_state evs ∧ f.io_events = [] ∧
  semantics_prog (init_state f) init_env prog b ⇒
  (∀out io. b = Terminate out io ⇒ evs ≼ io) ∧
  (∀io. b = Diverge io ⇒ LPREFIX (fromList evs) io)
Proof
  strip_tac >>
  qabbrev_tac ‘T0 = itree_of (init_state f) init_env prog’ >>
  ‘itree_of (init_state (replay_ffi evs)) init_env prog = T0’
    by simp[Abbr ‘T0’, itree_of_init_state] >>
  drule prog_makes_trace >> simp[] >> strip_tac >>
  ‘evs ≼ FST (trace_prefix n (f.oracle, f.ffi_state) T0)’
    by (qpat_x_assum ‘FST _ = evs’ (SUBST1_TAC o SYM) >>
        qpat_x_assum ‘_ = T0’ (SUBST1_TAC o SYM) >> simp[Abbr ‘T0’] >>
        once_rewrite_tac[itree_of_init_state] >>
        irule replay_trace_itree >> simp[]) >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rveq >>
  qpat_x_assum ‘semantics_prog _ _ _ _’ mp_tac >>
  asm_simp_tac std_ss [alt_semanticsTheory.itree_semantics, init_state_fields] >>
  strip_tac
  >- (rveq >> asm_rewrite_tac[APPEND] >> metis_tac[prefix_end]) >>
  metis_tac[prefix_div]
QED
