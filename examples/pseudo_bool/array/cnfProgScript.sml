(*
  CNF encoder and checker
*)
open preamble basis lpr_parsingTheory cnf_to_pbTheory npbc_parseProgTheory;
open cfLib basisFunctionsLib;

val _ = new_theory "cnfProg";

val _ = translation_extends "npbc_parseProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* TODO: COPIED from lpr_arrayFullProgScript.sml *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

val _ = translate lpr_parsingTheory.blanks_def;
val _ = translate lpr_parsingTheory.tokenize_def;

val blanks_1_v_thm = theorem "blanks_1_v_thm";
val tokenize_v_thm = theorem "tokenize_v_thm";

val _ = translate parse_header_line_def;

val parse_header_line_side = Q.prove(`
   ∀x. parse_header_line_side x= T`,
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC)
  |> update_precondition;

val _ = translate parse_clause_aux_def;
val _ = translate parse_clause_def;

val _ = translate lpr_parsingTheory.nocomment_line_def;

val format_dimacs_failure_def = Define`
  format_dimacs_failure (lno:num) s =
  strlit "c DIMACS parse failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val _ = translate format_dimacs_failure_def;

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`lpr_parsing$blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_1_v`
  |> Q.GEN `g` |> Q.ISPEC`lpr_parsing$tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_1_v_thm,tokenize_v_thm,blanks_def] ;

val parse_dimacs_body_arr = process_topdecs`
  fun parse_dimacs_body_arr lno maxvar fd acc =
  case TextIO.b_inputLineTokens fd blanks_1 tokenize of
    None => Inr (List.rev acc)
  | Some l =>
    if nocomment_line l then
      (case parse_clause maxvar l of
        None => Inl (format_dimacs_failure lno "failed to parse line")
      | Some cl => parse_dimacs_body_arr (lno+1) maxvar fd (cl::acc))
    else parse_dimacs_body_arr (lno+1) maxvar fd acc` |> append_prog;

Theorem parse_dimacs_body_arr_spec:
  !lines fd fdv fs maxvar maxvarv acc accv lno lnov.
  NUM lno lnov ∧
  NUM maxvar maxvarv ∧
  LIST_TYPE (LIST_TYPE INT) acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_dimacs_body_arr" (get_ml_prog_state()))
    [lnov; maxvarv; fdv; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (LIST_TYPE INT))
      (case parse_dimacs_body maxvar (FILTER lpr_parsing$nocomment_line (MAP lpr_parsing$toks lines)) acc of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ xcf "parse_dimacs_body_arr" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ simp[parse_dimacs_body_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl)
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (lpr_parsing$toks h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[lpr_parsingTheory.toks_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_autop
  \\ reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    asm_exists_tac>> simp[]>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    qexists_tac`acc`>>xsimpl>>
    rw[]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xif>> asm_exists_tac>>simp[]>>
  xlet_autop>>
  simp[parse_dimacs_body_def]>>
  Cases_on`parse_clause maxvar (lpr_parsing$toks h)`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`fd`>>
  qexists_tac`x::acc`>>
  xsimpl>>
  simp[LIST_TYPE_def]>>rw[]>>
  qexists_tac`k+x'`>>
  qexists_tac`x''`>>
  simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
  xsimpl>>
  metis_tac[]
QED

val parse_dimacs_toks_arr = process_topdecs`
  fun parse_dimacs_toks_arr lno fd =
  case TextIO.b_inputLineTokens fd blanks_1 tokenize of
    None => Inl (format_dimacs_failure lno "failed to find header")
  | Some l =>
    if nocomment_line l then
      (case parse_header_line l of
        None => Inl (format_dimacs_failure lno "failed to parse header")
      | Some res => case res of (vars,clauses) =>
        (case parse_dimacs_body_arr lno vars fd [] of
          Inl fail => Inl fail
        | Inr acc =>
          if List.length acc = clauses then
            Inr (vars,(clauses,acc))
          else
            Inl (format_dimacs_failure lno "incorrect number of clauses")))
    else parse_dimacs_toks_arr (lno+1) fd` |> append_prog;

Theorem parse_dimacs_toks_arr_spec:
  !lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_dimacs_toks_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM (LIST_TYPE (LIST_TYPE INT))))
      (case parse_dimacs_toks (MAP lpr_parsing$toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ xcf "parse_dimacs_toks_arr" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ simp[parse_dimacs_toks_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl
    \\ metis_tac[])
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (lpr_parsing$toks h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_autop
  \\ simp[parse_dimacs_toks_def]
  \\ reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    rw[]>>
    fs[parse_dimacs_toks_def]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xif>> asm_exists_tac>>simp[]>>
  xlet_autop>>
  Cases_on`parse_header_line (lpr_parsing$toks h)`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet `(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (LIST_TYPE INT))
      (case parse_dimacs_body q (FILTER lpr_parsing$nocomment_line (MAP lpr_parsing$toks lines)) [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`lines`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    qexists_tac`[]`>>simp[LIST_TYPE_def]>>
    rw[]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    rw[]>>fs[SUM_TYPE_def]>>
    xmatch>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>>qexists_tac`lines'`>>xsimpl>>
    metis_tac[])>>
  strip_tac>>fs[SUM_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  drule LENGTH_parse_dimacs_body>>
  strip_tac>>fs[]>>
  rw[]>> xif
  >- (
    asm_exists_tac>>simp[]>>
    xlet_autop>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,PAIR_TYPE_def]>>
    qexists_tac`k`>>qexists_tac`lines'`>>xsimpl)>>
  asm_exists_tac>>simp[]>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  qexists_tac`k`>>
  qexists_tac`lines'`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]>>
  xsimpl>>
  metis_tac[]
QED

(* parse_dimacs_toks with simple wrapper *)
val parse_dimacs_full = (append_prog o process_topdecs) `
  fun parse_dimacs_full fname =
  let
    val fd = TextIO.b_openIn fname
    val res = parse_dimacs_toks_arr 0 fd
    val close = TextIO.b_closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)`;

Theorem parse_dimacs_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_dimacs_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM (LIST_TYPE (LIST_TYPE INT))))
    (if inFS_fname fs f then
    (case parse_dimacs_toks (MAP lpr_parsing$toks (all_lines fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_dimacs_full"(get_ml_prog_state()) >>
  fs[validArg_def]>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >-
      (xlet_auto_spec (SOME b_openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME b_openIn_spec_lines) \\ xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES fdd fddv lines fss`>>
  xlet`(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM (LIST_TYPE (LIST_TYPE INT))))
      (case parse_dimacs_toks (MAP lpr_parsing$toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fss fdd k) * INSTREAM_LINES fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`lines`>>
    qexists_tac`fss`>>qexists_tac`fdd`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec b_closeIn_spec_lines >>
    qexists_tac `emp`>>
    qexists_tac `lines'` >>
    qexists_tac `forwardFD fss fdd k` >>
    qexists_tac `fdd` >>
    conj_tac THEN1
     (unabbrev_all_tac
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    xsimpl>>
    `validFileFD fdd (forwardFD fss fdd k).infds` by
      (unabbrev_all_tac>> simp[validFileFD_forwardFD]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`]>>
    xsimpl)>>
  xvar>>
  xsimpl>>
  metis_tac[]
QED

(* Translate the encoder *)
val _ = translate clause_to_pbc_def;
val _ = translate fml_to_pbf_def;

(* parse input from f1 and run encoder *)
val parse_and_enc = (append_prog o process_topdecs) `
  fun parse_and_enc f1 =
  case parse_dimacs_full f1 of
    Inl err => Inl err
  | Inr (a,(b,fml)) =>
    Inr (fml_to_pbf fml)`

Definition get_fml_def:
  get_fml fs f =
  if inFS_fname fs f then
    parse_dimacs (all_lines fs f)
  else NONE
End

Theorem parse_and_enc_spec:
  STRING_TYPE f1 f1v ∧
  validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_and_enc"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv v.
    STDIO fs *
    & ∃res.
       SUM_TYPE STRING_TYPE
         (LIST_TYPE constraint_TYPE) res v ∧
      case res of
        INL err =>
          get_fml fs f1 = NONE
      | INR pbf =>
        ∃fml.
        get_fml fs f1 = SOME fml ∧
        fml_to_pbf fml = pbf)
Proof
  rw[]>>
  xcf"parse_and_enc"(get_ml_prog_state())>>
  xlet_autop>>
  pop_assum mp_tac>>
  reverse IF_CASES_TAC
  >- (
    rw[SUM_TYPE_def]>>
    xmatch>>
    xcon>>
    xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]>>
    fs[get_fml_def])>>
  TOP_CASE_TAC
  >- (
    rw[SUM_TYPE_def]>>
    xmatch>>
    xcon>>
    xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]>>
    fs[get_fml_def,parse_dimacs_def])>>
  rw[SUM_TYPE_def]>>
  PairCases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  qexists_tac`INR (fml_to_pbf x2)`>>
  fs[SUM_TYPE_def,npbc_arrayProgTheory.constraint_TYPE_def]>>
  simp[get_fml_def,parse_dimacs_def]
QED

Definition success_string_def:
  success_string = strlit "s VERIFIED UNSAT\n"
End

val success_string_v_thm = translate success_string_def;

Definition plainVar_nf_def:
  plainVar_nf s (u:unit) =
  if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    case mlint$fromNatString (substring s 1 (strlen s - 1)) of
      NONE => NONE
    | SOME n => SOME (n,())
  else
    NONE
End

val r = translate plainVar_nf_def;

val plainvar_nf_side = Q.prove(`
   ∀x y. plainvar_nf_side x y = T`,
  EVAL_TAC>>
  rw[])
  |> update_precondition;

Definition plain_ns_def:
  plain_ns = (plainVar_nf,())
End

val plain_ns_v_thm = translate plain_ns_def;

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
    (case check_unsat_top plain_ns success_string fml f2 of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)`

Theorem success_string_not_nil:
  strlit "" ≠ success_string
Proof
  EVAL_TAC
QED

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  if out = success_string then
    ∃fml.
    get_fml fs f1 = SOME fml ∧
    unsatisfiable (interp fml)
  else out = strlit""
End

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_2_sem fs f1 out))
Proof
  rw[check_unsat_2_sem_def]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  Cases_on`res`
  >- (
    fs[SUM_TYPE_def]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>
    xsimpl>>rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  fs[SUM_TYPE_def]>>
  xmatch>>
  xlet`POSTv v.STDIO fs *
    SEP_EXISTS res.
    &(SUM_TYPE STRING_TYPE STRING_TYPE res v ∧
    (∀s. res = INR s ⇒
        (s = success_string ∧
        unsatisfiable (set (fml_to_pbf fml)))))`
  >- (
    assume_tac plain_ns_v_thm>>
    drule check_unsat_top_spec>>
    strip_tac>>
    xapp>>
    simp[success_string_v_thm ]>>
    fs[FILENAME_def,validArg_def]>>
    metis_tac[])>>
  Cases_on`res`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit ""`>>
    qexists_tac`x`>>
    xsimpl>>rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  xapp>>asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`success_string`>>simp[]>>
  qexists_tac`strlit ""`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  fs[get_fml_def]>>
  drule fml_to_pbf_parse_dimacs>>
  fs[npbcTheory.unsatisfiable_def,npbcTheory.satisfiable_def,satSemTheory.unsatisfiable_def,satSemTheory.satisfiable_def]
QED

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb_cnf <DIMACS formula file> <proof file>\n"
End

val r = translate usage_string_def;

val main = (append_prog o process_topdecs) `
  fun main u =
  case CommandLine.arguments () of
    [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
  else out = strlit ""
End

Theorem STDIO_refl:
  (STDIO A ==>> STDIO A) ∧
  (STDIO A ==>>
  STDIO A * GC)
Proof
  xsimpl
QED

Theorem main_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(main_sem fs cl out))
Proof
  rw[main_sem_def]>>
  xcf"main"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >>
    simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >>
    simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>fs[]>>
    rw[]>>
    fs[wfcl_def]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    rw[]>>
    metis_tac[STDIO_refl])>>
  xmatch>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `usage_string` >>
  simp [theorem "usage_string_v_thm"] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  metis_tac[STDIO_refl]
QED

Theorem main_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 main_v cl fs NONE
     (λfs'. ∃out err.
        fs' = add_stdout (add_stderr fs err) out ∧
        main_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`add_stdout (add_stderr fs x') x`
  \\ xsimpl
  \\ qexists_tac`x`
  \\ qexists_tac`x'`
  \\ xsimpl
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

local

val name = "main"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH main_whole_prog_spec2)
val main_prog_def = Define`main_prog = ^prog_tm`;

in

Theorem main_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM main_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end

val _ = export_theory();
