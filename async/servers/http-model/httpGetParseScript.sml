(*
  An incremental parser for HttpGetSpec's request subset, proved against the
  spec's printer.  Internal: it is not part of the trusted spec.

     parse_request s = Complete r rest   s starts with a complete valid
                                         request r, followed by rest
                     | Incomplete        s could still become one
                     | Invalid           no extension of s starts with one

  A handler keeps a buffer of what it has read and re-parses it after each
  read; parse_all s is the list of complete requests at the front of s.

  Main facts:
   - parse_print:      parse_request (print_request r ++ rest) = Complete r rest
   - parse_complete:   Complete r rest means s = print_request r ++ rest
   - parse_prefix:     a strict prefix of a printed request is Incomplete
   - parse_invalid:    Invalid means no extension of s is a printed request
                       followed by anything
   - parse_all_requests: parse_all of printed requests followed by a rest
                       that does not start with a request is the requests
*)
Theory httpGetParse
Ancestors
  HttpGetSpec list rich_list
Libs
  preamble

Datatype:
  parse_result = Complete request string | Incomplete | Invalid
End

(* The fixed parts of a request line, as constants (so that proofs treat
   them abstractly): "GET " before the path, " HTTP/1.0\r\n\r\n" after *)
Definition get_sp_def:
  get_sp = "GET "
End

Definition after_path_def:
  after_path = " HTTP/1.0\r\n\r\n"
End

Theorem LENGTH_get_sp[simp]:
  LENGTH get_sp = 4
Proof
  EVAL_TAC
QED

Theorem LENGTH_after_path[simp]:
  LENGTH after_path = 13
Proof
  EVAL_TAC
QED

Theorem after_path_space:
  ∃x. after_path = #" " :: x
Proof
  simp[after_path_def]
QED

Theorem print_request_Get:
  print_request (Get p) = get_sp ++ p ++ after_path
Proof
  simp[print_request_def, get_sp_def, after_path_def]
QED

(* split_path t = (p, u): p is t up to its first space, u the rest
   (starting with that space, or empty if there is none) *)
Definition split_path_def:
  split_path [] = ([], []) ∧
  split_path (c :: cs) =
    if c = #" " then ([], c :: cs)
    else (c :: FST (split_path cs), SND (split_path cs))
End

Definition parse_request_def:
  parse_request s =
    if ¬(get_sp ≼ s) then (if s ≼ get_sp then Incomplete else Invalid)
    else
      let t = DROP 4 s;
          p = FST (split_path t);
          u = SND (split_path t)
      in
        if EXISTS (λc. c = #"\r" ∨ c = #"\n") p then Invalid
        else if u = [] then Incomplete
        else if p = [] then Invalid
        else if after_path ≼ u then Complete (Get p) (DROP 13 u)
        else if u ≼ after_path then Incomplete
        else Invalid
End

(* ------------------------------------------------------------------------
   Small list facts
   ------------------------------------------------------------------------ *)

Theorem split_path_space[local]:
  ∀p x. EVERY (λc. c ≠ #" ") p ⇒ split_path (p ++ #" " :: x) = (p, #" " :: x)
Proof
  Induct >> simp[split_path_def]
QED

Theorem split_path_join[local]:
  ∀t. FST (split_path t) ++ SND (split_path t) = t
Proof
  Induct >> rw[split_path_def]
QED

Theorem split_path_every[local]:
  ∀t. EVERY (λc. c ≠ #" ") (FST (split_path t))
Proof
  Induct >> rw[split_path_def]
QED

Theorem prefix_append_cases[local]:
  ∀a s b. s ≼ a ++ b ⇔ s ≼ a ∨ ∃t. s = a ++ t ∧ t ≼ b
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘s’ >> simp[] >> metis_tac[]
QED

Theorem prefix_of_no_space[local]:
  ∀p t. t ≼ p ∧ EVERY (λc. c ≠ #" ") p ⇒ split_path t = (t, [])
Proof
  Induct >> simp[] >- simp[split_path_def] >>
  rpt gen_tac >> Cases_on ‘t’ >> simp[split_path_def] >> rw[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem valid_path_every[local]:
  valid_path p ⇒
  EVERY (λc. c ≠ #" ") p ∧ ¬EXISTS (λc. c = #"\r" ∨ c = #"\n") p ∧ p ≠ []
Proof
  rw[valid_path_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The parser against the printer
   ------------------------------------------------------------------------ *)

(* MAIN: a printed valid request, followed by anything, parses back *)
Theorem parse_print:
  valid_request r ⇒ parse_request (print_request r ++ rest) = Complete r rest
Proof
  Cases_on ‘r’ >> rw[valid_request_def, print_request_Get] >>
  drule valid_path_every >> strip_tac >>
  qabbrev_tac ‘q = s ++ after_path ++ rest’ >>
  ‘get_sp ++ s ++ after_path ++ rest = get_sp ++ q’ by simp[Abbr ‘q’] >>
  pop_assum SUBST1_TAC >>
  ‘DROP 4 (get_sp ++ q) = q’
    by (‘4 = LENGTH get_sp’ by simp[] >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  ‘split_path q = (s, after_path ++ rest)’
    by (strip_assume_tac after_path_space >> simp[Abbr ‘q’] >>
        REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[split_path_space]) >>
  ‘DROP 13 (after_path ++ rest) = rest’
    by (‘13 = LENGTH after_path’ by simp[] >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  ‘after_path ++ rest ≠ []’ by (strip_assume_tac after_path_space >> simp[]) >>
  simp[parse_request_def]
QED

Theorem parse_print_NIL:
  valid_request r ⇒ parse_request (print_request r) = Complete r []
Proof
  metis_tac[parse_print, APPEND_NIL]
QED

(* MAIN: Complete means a printed valid request followed by the rest *)
Theorem parse_complete:
  parse_request s = Complete r rest ⇒
  valid_request r ∧ s = print_request r ++ rest
Proof
  rw[parse_request_def, AllCaseEqs()] >>
  qabbrev_tac ‘t = DROP 4 s’ >>
  qabbrev_tac ‘p = FST (split_path t)’ >>
  qabbrev_tac ‘u = SND (split_path t)’ >>
  ‘EVERY (λc. c ≠ #" ") p’ by simp[Abbr ‘p’, split_path_every] >>
  ‘s = get_sp ++ t’
    by (fs[IS_PREFIX_APPEND] >> simp[Abbr ‘t’] >>
        ‘4 = LENGTH get_sp’ by simp[] >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  ‘t = p ++ u’ by simp[Abbr ‘p’, Abbr ‘u’, split_path_join] >>
  ‘u = after_path ++ DROP 13 u’
    by (fs[IS_PREFIX_APPEND] >>
        ‘13 = LENGTH after_path’ by simp[] >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  simp[valid_request_def, valid_path_def, print_request_Get] >>
  fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[APPEND_ASSOC]
QED

Theorem parse_complete_shorter:
  parse_request s = Complete r rest ⇒ LENGTH rest < LENGTH s
Proof
  strip_tac >> drule parse_complete >> Cases_on ‘r’ >>
  rw[print_request_Get]
QED

(* Complete is stable under extension *)
Theorem parse_extend:
  parse_request s = Complete r rest ⇒
  parse_request (s ++ x) = Complete r (rest ++ x)
Proof
  strip_tac >> drule parse_complete >> rw[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[parse_print]
QED

(* MAIN: a strict prefix of a printed valid request is Incomplete *)
Theorem parse_prefix:
  valid_request r ∧ s ≼ print_request r ∧ s ≠ print_request r ⇒
  parse_request s = Incomplete
Proof
  Cases_on ‘r’ >> rw[valid_request_def, print_request_Get] >>
  drule valid_path_every >> strip_tac >>
  rename1 ‘get_sp ++ p ++ after_path’ >>
  qpat_x_assum ‘s ≼ _’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
  simp[prefix_append_cases] >> strip_tac
  >- ((* s is a prefix of "GET " *)
      Cases_on ‘s = get_sp’
      >- simp[parse_request_def, DROP_LENGTH_TOO_LONG, split_path_def]
      >> ‘¬(get_sp ≼ s)’ by (strip_tac >> imp_res_tac IS_PREFIX_ANTISYM) >>
      simp[parse_request_def]) >>
  (* s = "GET " ++ t *)
  gvs[] >> rename1 ‘get_sp ++ t’ >>
  ‘DROP 4 (get_sp ++ t) = t’
    by (‘4 = LENGTH get_sp’ by simp[] >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  fs[prefix_append_cases]
  >- ((* t is a prefix of the path *)
      drule_all prefix_of_no_space >> strip_tac >>
      ‘¬EXISTS (λc. c = #"\r" ∨ c = #"\n") t’
        by (fs[IS_PREFIX_APPEND] >> gvs[EXISTS_APPEND]) >>
      simp[parse_request_def]) >>
  (* t = path ++ v, v a strict prefix of " HTTP/1.0\r\n\r\n" *)
  gvs[] >> qmatch_goalsub_rename_tac ‘get_sp ++ pa ++ v’ >>
  ‘get_sp ≼ get_sp ++ pa ++ v’
    by REWRITE_TAC[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3] >>
  ‘DROP 4 (get_sp ++ pa ++ v) = pa ++ v’
    by (REWRITE_TAC[GSYM APPEND_ASSOC] >>
        ‘4 = LENGTH get_sp’ by simp[] >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  Cases_on ‘v = []’
  >- (‘split_path pa = (pa, [])’ by metis_tac[prefix_of_no_space, IS_PREFIX_REFL] >>
      gvs[parse_request_def] >>
      ‘¬EXISTS (λc. c = #"\r" ∨ c = #"\n") pa’ by fs[NOT_EXISTS] >> simp[]) >>
  strip_assume_tac after_path_space >>
  ‘∃v'. v = #" " :: v'’
    by (‘v ≼ #" " :: x’ by metis_tac[] >> Cases_on ‘v’ >> fs[]) >>
  ‘split_path (pa ++ v) = (pa, v)’ by simp[split_path_space] >>
  ‘¬(after_path ≼ v)’ by (strip_tac >> imp_res_tac IS_PREFIX_ANTISYM >> fs[]) >>
  ‘¬EXISTS (λc. c = #"\r" ∨ c = #"\n") pa’ by fs[NOT_EXISTS] >>
  qpat_x_assum ‘v = _’ kall_tac >> qpat_x_assum ‘after_path = _’ kall_tac >>
  simp[parse_request_def]
QED

(* MAIN: Invalid input can never be extended into a printed valid request
   (followed by anything) *)
Theorem parse_invalid:
  parse_request s = Invalid ⇒
  ∀t r rest. valid_request r ⇒ s ++ t ≠ print_request r ++ rest
Proof
  rpt strip_tac >>
  ‘s ≼ print_request r ∨ print_request r ≼ s’
    by metis_tac[IS_PREFIX_APPEND, prefixes_is_prefix_total] >>
  fs[IS_PREFIX_APPEND] >> gvs[]
  >- (Cases_on ‘l = []’ >> gvs[parse_print, parse_print_NIL] >>
      ‘parse_request s = Incomplete’
        by (irule parse_prefix >> qexists_tac ‘r’ >> asm_rewrite_tac[] >>
            simp[IS_PREFIX_APPEND] >> Cases_on ‘l’ >> fs[]) >>
      fs[])
  >- gvs[parse_print]
QED

(* ------------------------------------------------------------------------
   All complete requests at the front of a buffer
   ------------------------------------------------------------------------ *)

Definition parse_all_def:
  parse_all s =
    case parse_request s of
    | Complete r rest => r :: parse_all rest
    | _ => []
Termination
  WF_REL_TAC ‘measure LENGTH’ >> metis_tac[parse_complete_shorter]
End

(* After parsing one request, the rest of the buffer *)
Theorem parse_all_Complete:
  parse_request s = Complete r rest ⇒ parse_all s = r :: parse_all rest
Proof
  simp[Once parse_all_def]
QED

(* MAIN: printed valid requests, followed by a rest that does not start
   with a printed valid request, parse to exactly those requests *)
Theorem parse_all_requests:
  ∀rs. EVERY valid_request rs ∧
       (∀r more. valid_request r ⇒ rest ≠ print_request r ++ more) ⇒
       parse_all (FLAT (MAP print_request rs) ++ rest) = rs
Proof
  Induct
  >- (rw[Once parse_all_def] >> CASE_TAC >> drule parse_complete >> rw[] >>
      metis_tac[])
  >> rw[] >>
  ‘parse_request (print_request h ++ (FLAT (MAP print_request rs) ++ rest)) =
   Complete h (FLAT (MAP print_request rs) ++ rest)’ by simp[parse_print] >>
  drule parse_all_Complete >> REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED
