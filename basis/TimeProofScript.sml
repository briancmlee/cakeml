(*
  Proof about the command-line module of the CakeML standard basis library.
*)
open preamble ml_translatorTheory ml_progLib ml_translatorLib cfLib
     TimeProgTheory tsFFITheory Word8ArrayProofTheory cfMonadLib
     Word8ProgTheory Word8ArrayProofTheory MarshallingProgTheory MarshallingTheory
     integerTheory int_arithTheory;

val _ = new_theory"TimeProof";

val _ = translation_extends"TimeProg";

Definition TIME_def:
  TIME ts ⇔ IOx ts_ffi_part ts
End

val set_thm =
  TIME_def
  |> SIMP_RULE(srw_ss())[
       cfHeapsBaseTheory.IOx_def,ts_ffi_part_def,
       cfHeapsBaseTheory.IO_def, set_sepTheory.one_def ]
  |> SIMP_RULE(srw_ss())[Once FUN_EQ_THM,
        set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,PULL_EXISTS]
  |> Q.SPEC`ts`
val set_tm = set_thm |> concl |> find_term(pred_setSyntax.is_insert);

Theorem TIME_precond:
  TIME ts ^set_tm
Proof
  rw[set_thm]
QED

Theorem TIME_FFI_part_hprop:
  FFI_part_hprop (TIME x)
Proof
  rw [TIME_def,cfHeapsBaseTheory.IO_def,cfMainTheory.FFI_part_hprop_def,
      cfHeapsBaseTheory.IOx_def,ts_ffi_part_def,
      set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
      set_sepTheory.cond_STAR]
  \\ fs[set_sepTheory.one_def]
QED

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm"
val eq_word8_v_thm = MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> cj 4) |> INST_TYPE [“:'a” |-> “:8”]


Theorem getNow_spec:
  ∀t ds d uv.
     ds 0 = SOME d ⇒
     t' = Num (int_max (&t + d) 0) ⇒
     UNIT_TYPE () uv ⇒
     t' ≤ 256**8 - 1 ⇒
     app (p:'ffi ffi_proj) Time_getNow_v [uv]
         (TIME <| latest_time := t; microseconds_elapsed := ds |>)
         (POSTv v. &NUM t' v *
          TIME <| latest_time := t'; microseconds_elapsed := ds o SUC |>)
Proof
  xcf_with_def "Time.getNow" Time_getNow_v_def \\
  xmatch \\
  gs[UNIT_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ simp[]) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  rename [‘W8ARRAY bv (REPLICATE 9 0w)’] \\
  xlet ‘POSTv uv. &UNIT_TYPE () uv * W8ARRAY bv (0w :: n2w8 t') *
        TIME <| latest_time := t'; microseconds_elapsed := ds o SUC |>’
  >- (qpat_abbrev_tac `Q = $POSTv _` >>
      simp [ts_ffi_part_def, TIME_def, IOx_def, IO_def] >>
      xpull >> qunabbrev_tac `Q` >>
      xffi \\ xsimpl \\
      simp[TIME_def,IOx_def,ts_ffi_part_def,mk_ffi_next_def,IO_def] \\
      qmatch_goalsub_abbrev_tac ‘FFI_part st f ns’ \\
      CONV_TAC(RESORT_EXISTS_CONV List.rev) \\
      map_every qexists_tac[‘events’, ‘ns’, ‘f’, ‘st’] \\
      simp[Abbr‘f’,Abbr‘st’,Abbr‘ns’,mk_ffi_next_def,ffi_now_def,getNow_def] \\ xsimpl \\
      qpat_abbrev_tac ‘new_events = events ++ _’ \\
      qexists ‘new_events’ \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- (xsimpl \\ map_every qexists_tac [‘t’, ‘d’] \\ fs[]) \\
  xlet ‘POSTv boolv. W8ARRAY bv (0w::n2w8 t') * TIME  <|latest_time := t'; microseconds_elapsed := ds o SUC |> * &BOOL T boolv’
  >- (xapp_spec eq_word8_v_thm \\ xsimpl \\ fs[BOOL_def] \\ metis_tac []) \\
  xif \\ qexists ‘T’ \\ fs[] \\
  xapp \\ xsimpl \\ fs[LENGTH_n2w8] \\
  qpat_abbrev_tac ‘new_latest_time = Num (int_max _ _)’ \\
  fs[n2w8_def] \\ qspec_then ‘new_latest_time’ mp_tac n2w8_def \\
  simp[] \\ DISCH_THEN (SUBST1_TAC o SYM) \\ simp[w82n_n2w8]
QED

Theorem now_spec:
  ∀t ds d uv.
  ds 0 = SOME d ⇒
  t' = Num (int_max (&t + d) 0) ⇒
  UNIT_TYPE () uv ⇒
  t' ≤ 256**8 - 1 ⇒
  app (p:'ffi ffi_proj) Time_now_v [uv]
      (TIME <| latest_time := t; microseconds_elapsed := ds |>)
      (POSTv v. &TIME_TYPE (Time &t') v *
       TIME <| latest_time := t'; microseconds_elapsed := ds o SUC |>)
Proof
  xcf_with_def "Time.now" Time_now_v_def \\
  xmatch \\
  gs[UNIT_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ simp[]) \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  xapp \\ xsimpl \\ fs[fromMicroseconds_def] \\ rw[] \\
  qabbrev_tac ‘t' = Num (int_max (&t + d) 0)’ \\
  qexists ‘&t'’ \\ rw[] \\ gs[NUM_def]
QED

val _ = export_theory();
