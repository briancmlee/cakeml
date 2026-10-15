(*
  Safety of the chat server in the model.

  MAIN result (chat_server_safe): on every prefix U of the server's
  transcript (in a world that hands out distinct connections), what has
  been written to a connection d is a prefix of what d is owed: the lines
  completed after d's accept, in the order they were completed
  (owed_m, the model-level twin of ChatSpec's owed).

  The proof has three parts.
   1. The tap invariant (tap_inv): the hub's log, after any prefix of the
      inner transcript, is exactly lines_done of that prefix (outside the
      store); a connection's join position is lines_done before its
      accept.  Pure list reasoning: nothing about rounds or fibers.
   2. The writer (wloop_written, writer_written): whatever the log does,
      provided it only grows and the hub answers from it, a writer has
      written a prefix of the log from its join position.  Local to one
      handler.
   3. Gluing: cserver_with_isolates gives the handler's transcript inside
      the server's, tap_answers gives the hub's answers at their global
      positions, and the positions are monotone.
*)
Theory asyncChatSafe
Ancestors
  pair list rich_list arithmetic option pred_set string words alist
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncWithStore asyncWithTap asyncChatSW asyncChatModel
  sorting
Libs
  BasicProvers dep_rewrite

(* ------------------------------------------------------------------------
   Lines
   ------------------------------------------------------------------------ *)

Theorem wls_APPEND:
  wls (a ++ b) = if MEM #"\n" b then a ++ wls b else wls a
Proof
  rw[wls_def, REVERSE_APPEND]
  >- (‘EXISTS ($¬ ∘ (λc. c ≠ #"\n")) (REVERSE b)’
        by simp[EXISTS_MEM, MEM_REVERSE] >>
      simp[dropWhile_APPEND_EXISTS, REVERSE_APPEND])
  >> ‘EVERY (λc. c ≠ #"\n") (REVERSE b)’
       by (simp[EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
  simp[dropWhile_APPEND_EVERY]
QED

Theorem wls_no_newline:
  ¬MEM #"\n" s ⇒ wls s = ""
Proof
  rw[wls_def] >>
  ‘EVERY (λc. c ≠ #"\n") (REVERSE s)’ by (simp[EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
  simp[GSYM dropWhile_eq_nil] >> fs[dropWhile_eq_nil]
QED

Theorem wls_LENGTH:
  LENGTH (wls s) ≤ LENGTH s
Proof
  simp[wls_def] >> metis_tac[LENGTH_dropWhile_LESS_EQ, LENGTH_REVERSE]
QED

Theorem wls_sing[local]:
  wls [c] = if c = #"\n" then [c] else ""
Proof
  rw[wls_def]
QED

Theorem wls_prefix:
  ∀s. wls s ++ DROP (LENGTH (wls s)) s = s
Proof
  Induct_on ‘s’ using SNOC_INDUCT >- simp[wls_def] >>
  rw[SNOC_APPEND, wls_APPEND, wls_sing] >>
  ‘LENGTH (wls s) ≤ LENGTH s’ by simp[wls_LENGTH] >>
  simp[DROP_APPEND1] >> metis_tac[APPEND_ASSOC]
QED

Theorem wls_rest_no_newline:
  ∀s. ¬MEM #"\n" (DROP (LENGTH (wls s)) s)
Proof
  Induct_on ‘s’ using SNOC_INDUCT >- simp[wls_def] >>
  rw[SNOC_APPEND, wls_APPEND, wls_sing] >>
  ‘LENGTH (wls s) ≤ LENGTH s’ by simp[wls_LENGTH] >>
  simp[DROP_APPEND1, DROP_LENGTH_TOO_LONG]
QED

Theorem dropWhile_idem[local]:
  ∀l. dropWhile P (dropWhile P l) = dropWhile P l
Proof
  Induct >> rw[]
QED

Theorem wls_idem:
  wls (wls s) = wls s
Proof
  simp[wls_def, dropWhile_idem]
QED

Theorem DROP_LENGTH_APPEND_gen[local]:
  DROP (LENGTH (A ++ X)) (A ++ Y) = DROP (LENGTH X) Y
Proof
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem wls_buf_gen[local]:
  R = A ++ b ∧ wls A = A ∧ ¬MEM #"\n" b ⇒
  DROP (LENGTH A) (wls (R ++ s)) = wls (b ++ s) ∧
  DROP (LENGTH (wls (R ++ s))) (R ++ s) =
  DROP (LENGTH (wls (b ++ s))) (b ++ s)
Proof
  strip_tac >> gvs[] >> Cases_on ‘MEM #"\n" s’
  >- (‘wls (A ++ b ++ s) = A ++ b ++ wls s ∧ wls (b ++ s) = b ++ wls s’
        by (pop_assum mp_tac >> simp[wls_APPEND]) >>
      ASM_REWRITE_TAC[] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
      REWRITE_TAC[DROP_LENGTH_APPEND, DROP_LENGTH_APPEND_gen])
  >> ‘¬MEM #"\n" (b ++ s)’ by simp[] >>
  ‘wls (A ++ b ++ s) = A ∧ wls (b ++ s) = ""’
    by (‘wls (A ++ (b ++ s)) = wls A’ by (pop_assum mp_tac >> simp[wls_APPEND]) >>
        fs[wls_no_newline]) >>
  ASM_REWRITE_TAC[] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_NIL, DROP_LENGTH_APPEND, DROP_APPEND] >>
  ‘LENGTH A − (LENGTH A + LENGTH b) = 0’ by simp[] >> simp[]
QED

(* The new complete lines of R ++ s are those of its partial line ++ s *)
Theorem wls_buf:
  DROP (LENGTH (wls R)) (wls (R ++ s)) =
  wls (DROP (LENGTH (wls R)) R ++ s) ∧
  DROP (LENGTH (wls (R ++ s))) (R ++ s) =
  DROP (LENGTH (wls (DROP (LENGTH (wls R)) R ++ s)))
       (DROP (LENGTH (wls R)) R ++ s)
Proof
  irule wls_buf_gen >> simp[wls_prefix, wls_idem, wls_rest_no_newline]
QED

(* ------------------------------------------------------------------------
   Lines completed, on model transcripts
   ------------------------------------------------------------------------ *)

Theorem lines_done_SNOC:
  lines_done (tr ++ [p]) = lines_done tr ++ comp tr p
Proof
  simp[lines_done_def, GSYM ADD1, GENLIST, SNOC_APPEND, FLAT_SNOC] >>
  simp[EL_APPEND2, TAKE_LENGTH_APPEND] >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ] >> rw[] >>
  simp[EL_APPEND1, TAKE_APPEND1]
QED

Theorem lines_done_APPEND_prefix:
  ∀l tr. lines_done tr ≼ lines_done (tr ++ l)
Proof
  ho_match_mp_tac SNOC_INDUCT >> rw[SNOC_APPEND] >>
  ‘tr ++ (l ++ [x]) = (tr ++ l) ++ [x]’ by simp[] >>
  pop_assum SUBST1_TAC >> simp[lines_done_SNOC] >>
  metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS, APPEND_ASSOC]
QED

Theorem lines_done_mono:
  tr ≼ tr' ⇒ lines_done tr ≼ lines_done tr'
Proof
  strip_tac >> drule_then strip_assume_tac (iffLR IS_PREFIX_APPEND) >>
  simp[lines_done_APPEND_prefix]
QED

(* ------------------------------------------------------------------------
   1. The tap invariant
   ------------------------------------------------------------------------ *)

Definition acc_of_def:
  acc_of fd (p : action # response option) ⇔
    ∃l. p = (Accept l, SOME (Accepted fd))
End

(* What d is owed after the transcript U: the lines completed after its
   (first) accept *)
Definition owed_m_def:
  owed_m d U =
    case SPLITP (acc_of d) U of
      (U1, []) => ""
    | (U1, _) => DROP (LENGTH (lines_done U1)) (lines_done U)
End

Theorem read_SNOC[local]:
  read fd (tr ++ [p]) = read fd tr ++ read fd [p]
Proof
  simp[read_def]
QED

Theorem untag_SNOC_Sock[local]:
  untag [(Sock x, r)] =
    [(x, case r of SOME (SockR y) => SOME y | _ => NONE)] ∧
  untag [(Kv q, r)] = []
Proof
  simp[untag_def]
QED

Theorem tap_fold_SNOC[local]:
  tap_fold σ δ st (TR ++ [e]) = tap_fold σ δ (tap_fold σ δ st TR) [e]
Proof
  simp[tap_fold_APPEND]
QED

(* The connections read from and handed out in U fit in 64 bits (true in
   the socket world, whose fds are words) *)
Definition fds_ok_def:
  fds_ok (U : (action # response option) list) ⇔
    ∀p. MEM p U ⇒
        (∀fd. FST p = Read fd ⇒ fd < dimword (:64)) ∧
        (∀l fd. p = (Accept l, SOME (Accepted fd)) ⇒ fd < dimword (:64))
End

Theorem fds_ok_APPEND:
  fds_ok (U ++ V) ⇔ fds_ok U ∧ fds_ok V
Proof
  simp[fds_ok_def] >> metis_tac[]
QED

(* The hub's state st describes the (outer) transcript U *)
Definition hub_inv_def:
  hub_inv st U ⇔
    st.log = lines_done U ∧
    (∀fd. fd < dimword (:64) ⇒
          buf_of st (n2w fd) =
            DROP (LENGTH (wls (CONCAT (read fd U)))) (CONCAT (read fd U))) ∧
    (∀fd j. fd < dimword (:64) ∧ ALOOKUP st.joins (n2w fd) = SOME j ⇒
            ∃U1 U2. U = U1 ++ U2 ∧ U2 ≠ [] ∧ acc_of fd (HD U2) ∧
                    ¬MEM fd (accepted (TL U2)) ∧ j = LENGTH (lines_done U1))
End

Theorem hub_inv_joins_SNOC[local]:
  (∀fd j. fd < dimword (:64) ∧ ALOOKUP st.joins (n2w fd) = SOME j ⇒
          ∃U1 U2. U = U1 ++ U2 ∧ U2 ≠ [] ∧ acc_of fd (HD U2) ∧
                  ¬MEM fd (accepted (TL U2)) ∧ j = LENGTH (lines_done U1)) ∧
  fd < dimword (:64) ∧ ALOOKUP st.joins (n2w fd) = SOME j ∧
  (∀l. p ≠ (Accept l, SOME (Accepted fd))) ⇒
  ∃U1 U2. U ++ [p] = U1 ++ U2 ∧ U2 ≠ [] ∧ acc_of fd (HD U2) ∧
          ¬MEM fd (accepted (TL U2)) ∧ j = LENGTH (lines_done U1)
Proof
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexistsl [‘U1’, ‘U2 ++ [p]’] >> Cases_on ‘U2’ >> gvs[] >>
  simp[accepted_def] >> PairCases_on ‘p’ >> every_case_tac >> gvs[]
QED

Theorem hub_inv_none:
  hub_inv st U ⇒ hub_inv st (U ++ [(x, NONE)])
Proof
  rw[hub_inv_def, lines_done_SNOC, read_SNOC] >>
  TRY (Cases_on ‘x’ >> simp[comp_def] >> NO_TAC) >>
  TRY (simp[read_def] >> NO_TAC) >>
  irule hub_inv_joins_SNOC >> simp[] >> metis_tac[]
QED

Theorem n2w_11_lt[local]:
  a < dimword (:64) ∧ b < dimword (:64) ⇒ ((n2w a : word64) = n2w b ⇔ a = b)
Proof
  simp[wordsTheory.n2w_11]
QED

Theorem read_sing[local]:
  read fd' [(a, SOME r)] =
    case (a, r) of (Read fd, Data s) => if fd = fd' then [s] else [] | _ => []
Proof
  simp[read_def] >> every_case_tac >> simp[]
QED

Theorem hub_inv_other[local]:
  hub_inv st U ∧ (∀fd s. (x, y) ≠ (Read fd, Data s)) ⇒
  (∀l fd. (x, y) ≠ (Accept l, Accepted fd)) ⇒
  hub_inv st (U ++ [(x, SOME y)])
Proof
  rpt strip_tac >> fs[hub_inv_def, lines_done_SNOC, read_SNOC] >>
  ‘comp U (x, SOME y) = ""’
    by (Cases_on ‘x’ >> Cases_on ‘y’ >> gvs[comp_def]) >>
  ‘∀fd'. read fd' [(x, SOME y)] = []’
    by (Cases_on ‘x’ >> Cases_on ‘y’ >> gvs[read_sing]) >>
  simp[] >> rpt strip_tac >>
  irule hub_inv_joins_SNOC >> simp[] >> metis_tac[]
QED

Theorem ALOOKUP_FILTER_FST[local]:
  ∀l. ALOOKUP (FILTER (λp. FST p ≠ k) l) x = if x = k then NONE else ALOOKUP l x
Proof
  Induct >> simp[] >> PairCases >> rw[] >> gvs[]
QED

Theorem hub_inv_read[local]:
  hub_inv st U ∧ fd < dimword (:64) ⇒
  hub_inv (chat_tap st (Read fd) (Data s)) (U ++ [(Read fd, SOME (Data s))])
Proof
  rpt strip_tac >> fs[hub_inv_def] >>
  simp[chat_tap_def, lines_done_SNOC, read_SNOC, read_sing, comp_def] >>
  rpt conj_tac
  >- simp[CONJUNCT1 wls_buf]
  >- (rpt strip_tac >> Cases_on ‘fd' = fd’
      >- (gvs[] >> simp[Once buf_of_def] >> metis_tac[wls_buf])
      >> ‘(n2w fd' : word64) ≠ n2w fd’ by simp[n2w_11_lt] >>
      simp[Once buf_of_def, ALOOKUP_FILTER_FST] >>
      qpat_x_assum ‘∀fd'. fd' < _ ⇒ buf_of _ _ = _’ (qspec_then ‘fd'’ mp_tac) >>
      simp[buf_of_def])
  >> rpt strip_tac >> irule hub_inv_joins_SNOC >> simp[] >> metis_tac[]
QED

Theorem hub_inv_accept[local]:
  hub_inv st U ∧ fd < dimword (:64) ⇒
  hub_inv (chat_tap st (Accept l) (Accepted fd))
          (U ++ [(Accept l, SOME (Accepted fd))])
Proof
  rpt strip_tac >> fs[hub_inv_def] >>
  simp[chat_tap_def, lines_done_SNOC, read_SNOC, read_sing, comp_def] >>
  conj_tac >- fs[buf_of_def] >>
  rpt gen_tac >> strip_tac >>
  ‘fd' MOD 18446744073709551616 = fd'’ by simp[] >>
  Cases_on ‘fd = fd'’ >> gvs[]
  >- (qexistsl [‘U’, ‘[(Accept l, SOME (Accepted fd))]’] >>
      simp[acc_of_def, accepted_def])
  >> irule hub_inv_joins_SNOC >> simp[] >> metis_tac[]
QED

Theorem hub_inv_tap:
  hub_inv st U ∧ fds_ok [(x, SOME y)] ⇒
  hub_inv (chat_tap st x y) (U ++ [(x, SOME y)])
Proof
  rpt strip_tac >>
  Cases_on ‘∃fd s. x = Read fd ∧ y = Data s’
  >- (gvs[fds_ok_def] >> irule hub_inv_read >> simp[]) >>
  Cases_on ‘∃l fd. x = Accept l ∧ y = Accepted fd’
  >- (gvs[fds_ok_def] >> irule hub_inv_accept >> simp[]) >>
  ‘chat_tap st x y = st’
    by (Cases_on ‘x’ >> Cases_on ‘y’ >> gvs[chat_tap_def]) >>
  simp[] >> irule hub_inv_other >> simp[] >> metis_tac[]
QED

Theorem fds_ok_untag_SNOC[local]:
  fds_ok (untag (TR ++ [e])) ⇒ fds_ok (untag TR) ∧ fds_ok (untag [e])
Proof
  simp[fds_ok_def] >> metis_tac[]
QED

(* MAIN: after any part TR of the inner transcript, the hub's state
   describes the outer transcript untag TR *)
Theorem tap_inv:
  ∀TR. fds_ok (untag TR) ⇒
      hub_inv (tap_fold chat_tap chat_delta empty_store TR) (untag TR)
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- simp[tap_fold_def, hub_inv_def, empty_store_def, lines_done_def,
          buf_of_def, untag_def, read_def] >>
  rpt gen_tac >> simp[SNOC_APPEND] >> rpt strip_tac >>
  fs[fds_ok_APPEND] >>
  simp[tap_fold_SNOC] >>
  PairCases_on ‘x’ >> Cases_on ‘x0’ >> gvs[tap_fold_def, untag_SNOC_Sock] >>
  TRY (PairCases_on ‘q’ >> simp[chat_delta_def] >> every_case_tac >> gvs[] >> NO_TAC) >>
  Cases_on ‘x1’ >> TRY (rename1 ‘SOME rr’ >> Cases_on ‘rr’) >> gvs[] >>
  TRY (irule hub_inv_tap >> simp[] >> NO_TAC) >>
  irule hub_inv_none >> simp[]
QED

(* ------------------------------------------------------------------------
   2. The writer
   ------------------------------------------------------------------------ *)

(* What an inner transcript writes to fd *)
Definition wr_of_def:
  wr_of fd tr = CONCAT (written fd (untag tr))
End

(* The log only grows *)
Definition mono_log_def:
  mono_log (lg : num -> string) ⇔ ∀k k'. k ≤ k' ⇒ lg k ≼ lg k'
End

(* The hub's answers to fd's Fetch queries in tr come from the log lg
   (lg k is the log when the k-th entry is answered) *)
Definition fits_log_def:
  fits_log fd lg tr ⇔
    ∀k i a. k < LENGTH tr ∧ EL k tr = (Kv (fd, Fetch i), SOME (KvR a)) ⇒
            a = Lines (DROP i (lg k))
End

Theorem mono_log_shift:
  mono_log lg ⇒ mono_log (λk. lg (k + n))
Proof
  rw[mono_log_def]
QED

Theorem fits_log_APPEND:
  fits_log fd lg (l1 ++ l2) ⇒ fits_log fd (λk. lg (k + LENGTH l1)) l2
Proof
  rw[fits_log_def] >>
  first_x_assum (qspecl_then [‘k + LENGTH l1’, ‘i’] mp_tac) >> simp[EL_APPEND2]
QED

Theorem fits_log_CONS:
  fits_log fd lg (e :: tr) ⇒ fits_log fd (λk. lg (k + 1)) tr
Proof
  rw[fits_log_def] >>
  first_x_assum (qspecl_then [‘SUC k’, ‘i’] mp_tac) >> simp[ADD1]
QED

Theorem wr_of_simps:
  wr_of fd [] = "" ∧
  wr_of fd (l1 ++ l2) = wr_of fd l1 ++ wr_of fd l2 ∧
  wr_of fd ((Kv q, r) :: tr) = wr_of fd tr ∧
  wr_of fd ((Sock (Write fd' s), r) :: tr) =
    (if fd' = fd then s else "") ++ wr_of fd tr ∧
  wr_of fd ((Sock (Read fd'), r) :: tr) = wr_of fd tr ∧
  wr_of fd ((Sock (Accept l), r) :: tr) = wr_of fd tr
Proof
  simp[wr_of_def, untag_def, written_def] >> rw[]
QED

Theorem wr_of_CONS:
  wr_of fd (e :: tr) = wr_of fd [e] ++ wr_of fd tr
Proof
  simp[GSYM wr_of_simps]
QED

Theorem DROP_grow:
  s = DROP i x ∧ x ≼ y ∧ i ≤ LENGTH x ⇒ s ++ DROP (i + LENGTH s) y = DROP i y
Proof
  rw[IS_PREFIX_APPEND] >> simp[DROP_APPEND] >>
  ‘i + (LENGTH x − i) = LENGTH x ∧ i − LENGTH x = 0’ by simp[] >>
  simp[DROP_LENGTH_TOO_LONG, DROP_LENGTH_APPEND]
QED

Theorem DROP_prefix:
  x ≼ y ⇒ DROP n x ≼ DROP n y
Proof
  rw[IS_PREFIX_APPEND] >> simp[DROP_APPEND] >>
  Cases_on ‘n ≤ LENGTH x’ >> simp[DROP_LENGTH_TOO_LONG] >> metis_tac[]
QED

(* MAIN: the write loop from position i writes a prefix of the log from i *)
Theorem wloop_written:
  ∀R i lg.
    mono_log lg ∧ fits_log fd lg (trans (wloop (fd, i)) R) ∧
    i ≤ LENGTH (lg 0) ⇒
    ∀k. k < LENGTH (trans (wloop (fd, i)) R) ⇒
        wr_of fd (TAKE (SUC k) (trans (wloop (fd, i)) R)) ≼ DROP i (lg k)
Proof
  gen_tac >> measureInduct_on ‘LENGTH R’ >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘fits_log _ _ _’ mp_tac >>
  ONCE_REWRITE_TAC[wloop_unfold] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Fetch i))) K0) R’ >>
  qspecl_then [‘emit (Kv (fd, Fetch i))’, ‘K0’, ‘R’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit] >> rw[] >> simp[wr_of_simps]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >> strip_tac >>
  ‘K0 res = return () ∨ (∃s'. res = KvR (Lines s') ∧ s' = DROP i (lg 0))’
    by (qpat_x_assum ‘fits_log _ _ _’
          (qspecl_then [‘0’, ‘i’] mp_tac o REWRITE_RULE[fits_log_def]) >>
        simp[Abbr ‘K0’] >> Cases_on ‘res’ >> simp[] >>
        rename1 ‘KvR b’ >> Cases_on ‘b’ >> simp[])
  >- (pop_assum SUBST1_TAC >> simp[wr_of_simps]) >>
  gvs[Abbr ‘K0’] >>
  drule fits_log_CONS >> strip_tac >>
  ‘lg 0 ≼ lg 1’ by fs[mono_log_def] >>
  Cases_on ‘DROP i (lg 0) = ""’ >> gvs[]
  >- ((* nothing new: the same loop, one entry later *)
      first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >>
      disch_then (qspecl_then [‘i’, ‘λk. lg (k + 1)’] mp_tac) >>
      impl_tac
      >- (simp[mono_log_shift] >> imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
      strip_tac >> Cases >> simp[wr_of_simps] >>
      rw[] >> first_x_assum (qspec_then ‘n’ mp_tac) >> simp[ADD1] >>
      ONCE_REWRITE_TAC[wr_of_CONS] >> simp[wr_of_simps])
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit WR) K1) h2’ >>
  qspecl_then [‘emit WR’, ‘K1’, ‘h2’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit, Abbr ‘WR’] >> Cases >> simp[wr_of_simps] >>
      Cases_on ‘n’ >> simp[wr_of_simps, DROP_prefix])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘WR’, Abbr ‘K1’] >>
  qpat_x_assum ‘fits_log _ (λk. _) (_ :: _)’ (assume_tac o MATCH_MP fits_log_CONS) >>
  fs[] >>
  first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
  disch_then (qspecl_then [‘i + LENGTH (DROP i (lg 0))’, ‘λk. lg (k + 1 + 1)’] mp_tac) >>
  impl_tac
  >- (simp[mono_log_shift |> Q.GEN ‘n’ |> Q.SPEC ‘2’ |> SIMP_RULE arith_ss []] >>
      ‘lg 0 ≼ lg 2’ by fs[mono_log_def] >>
      imp_res_tac IS_PREFIX_LENGTH >> simp[] >>
      fs[mono_log_def] >> rw[] >> first_x_assum irule >> simp[]) >>
  strip_tac >>
  Cases >> simp[wr_of_simps] >> Cases_on ‘n’ >> simp[wr_of_simps]
  >- simp[DROP_prefix]
  >> rw[] >> rename1 ‘SUC (SUC n)’ >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
  ‘lg 0 ≼ lg (n + 2)’ by fs[mono_log_def] >>
  ‘SUC (SUC n) = n + 2’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘DROP i (lg 0) ++ DROP (LENGTH (lg 0)) (lg (n + 2)) = DROP i (lg (n + 2))’
    by (‘LENGTH (lg 0) = i + LENGTH (DROP i (lg 0))’ by simp[] >>
        pop_assum SUBST1_TAC >> irule DROP_grow >> qexists ‘lg 0’ >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

(* MAIN: a writer told that it joined at j0 (no later than the log's end)
   writes a prefix of the log from j0 *)
Theorem writer_written:
  mono_log lg ∧ fits_log fd lg (trans (writer fd) R) ∧
  (∀j. trans (writer fd) R ≠ [] ∧
       SND (HD (trans (writer fd) R)) = SOME (KvR (Pos j)) ⇒
       j = j0 ∧ j0 ≤ LENGTH (lg 0)) ⇒
  ∀k. k < LENGTH (trans (writer fd) R) ⇒
      wr_of fd (TAKE (SUC k) (trans (writer fd) R)) ≼ DROP j0 (lg k)
Proof
  strip_tac >> qpat_x_assum ‘fits_log _ _ _’ mp_tac >>
  qpat_x_assum ‘∀j. _’ mp_tac >>
  simp[writer_def] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Start))) K0) R’ >>
  qspecl_then [‘emit (Kv (fd, Start))’, ‘K0’, ‘R’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit] >> rw[] >> simp[wr_of_simps]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >> rpt strip_tac >>
  ‘(∃j. res = KvR (Pos j)) ∨ K0 res = return ()’
    by (simp[Abbr ‘K0’] >> every_case_tac >> simp[])
  >- (gvs[Abbr ‘K0’] >>
      drule fits_log_CONS >> strip_tac >>
      qspecl_then [‘h2’, ‘j’, ‘λk. lg (k + 1)’] mp_tac wloop_written >>
      impl_tac
      >- (simp[mono_log_shift] >> ‘lg 0 ≼ lg 1’ by fs[mono_log_def] >>
          imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
      strip_tac >> Cases_on ‘k’ >> simp[wr_of_simps] >>
      first_x_assum (qspec_then ‘n’ mp_tac) >> simp[ADD1])
  >> gvs[wr_of_simps] >> TRY (Cases_on ‘k’ >> gvs[wr_of_simps])
QED

(* ------------------------------------------------------------------------
   3. Gluing
   ------------------------------------------------------------------------ *)

Theorem untag_mono:
  x ≼ y ⇒ untag x ≼ untag y
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem log_at:
  fds_ok (untag TR) ⇒
  (tap_fold chat_tap chat_delta empty_store TR).log = lines_done (untag TR)
Proof
  strip_tac >> drule tap_inv >> simp[hub_inv_def]
QED

(* Each entry of TR, with the hub's state just before it *)
Definition with_state_def:
  with_state TR =
    GENLIST (λp. (EL p TR, tap_fold chat_tap chat_delta empty_store (TAKE p TR)))
            (LENGTH TR)
End

Theorem MAP_FST_FILTER_FST:
  ∀l. MAP FST (FILTER (P ∘ FST) l) = FILTER P (MAP FST l)
Proof
  Induct >> rw[]
QED

Theorem MAP_FST_with_state:
  MAP FST (with_state TR) = TR
Proof
  simp[with_state_def, MAP_GENLIST, combinTheory.o_DEF, LIST_EQ_REWRITE]
QED

Theorem TAKE_with_state:
  TAKE n (with_state TR) = with_state (TAKE n TR)
Proof
  Cases_on ‘n ≤ LENGTH TR’
  >- (simp[with_state_def, TAKE_GENLIST, MIN_DEF] >> rw[] >>
      TRY (‘n = LENGTH TR’ by simp[] >> gvs[]) >>
      simp[GENLIST_FUN_EQ, EL_TAKE, TAKE_TAKE_MIN, MIN_DEF])
  >> simp[TAKE_LENGTH_TOO_LONG, with_state_def]
QED

Theorem MEM_with_state:
  MEM (e, st) (with_state TR) ⇔
  ∃p. p < LENGTH TR ∧ e = EL p TR ∧
      st = tap_fold chat_tap chat_delta empty_store (TAKE p TR)
Proof
  simp[with_state_def, MEM_GENLIST] >> metis_tac[]
QED

(* The logs along with_state only grow *)
Theorem fds_ok_prefix:
  fds_ok U ∧ U' ≼ U ⇒ fds_ok U'
Proof
  rw[fds_ok_def, IS_PREFIX_APPEND] >> metis_tac[MEM_APPEND]
QED

Theorem fds_ok_TAKE:
  fds_ok (untag TR) ⇒ fds_ok (untag (TAKE n TR))
Proof
  strip_tac >> irule fds_ok_prefix >> qexists ‘untag TR’ >> simp[] >>
  ‘TR = TAKE n TR ++ DROP n TR’ by simp[] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[]
QED

Theorem with_state_sorted:
  fds_ok (untag TR) ⇒
  SORTED (λx y. (SND x).log ≼ (SND y).log) (with_state TR)
Proof
  strip_tac >> simp[SORTED_EL_SUC, with_state_def] >> rpt strip_tac >>
  ‘fds_ok (untag (TAKE n TR)) ∧ fds_ok (untag (TAKE (SUC n) TR))’
    by metis_tac[fds_ok_TAKE] >>
  simp[log_at] >> irule lines_done_mono >> irule untag_mono >>
  simp[IS_PREFIX_EQ_TAKE] >> qexists ‘n’ >> simp[TAKE_TAKE_MIN, MIN_DEF]
QED

Theorem untag_CONS_sing[local]:
  untag (h :: l) = untag [h] ++ untag l
Proof
  simp[untag_def]
QED

Theorem untag_prefix:
  ∀TR U. U ≼ untag TR ⇒ ∃TR'. TR' ≼ TR ∧ untag TR' = U
Proof
  Induct >- (rw[untag_def] >> qexists ‘[]’ >> simp[untag_def]) >>
  rpt strip_tac >>
  Cases_on ‘U’ >- (qexists ‘[]’ >> simp[untag_def]) >>
  ‘untag [h] = [] ∨ ∃x. untag [h] = [x]’
    by (PairCases_on ‘h’ >> Cases_on ‘h0’ >> simp[untag_def])
  >- (qpat_x_assum ‘_ ≼ untag (h :: TR)’ mp_tac >>
      ONCE_REWRITE_TAC[untag_CONS_sing] >> ASM_REWRITE_TAC[APPEND] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      qexists ‘h :: TR'’ >> simp[] >> ONCE_REWRITE_TAC[untag_CONS_sing] >>
      ASM_REWRITE_TAC[APPEND])
  >> qpat_x_assum ‘_ ≼ untag (h :: TR)’ mp_tac >>
  ONCE_REWRITE_TAC[untag_CONS_sing] >> ASM_REWRITE_TAC[APPEND, isPREFIX_THM] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists ‘h :: TR'’ >> simp[] >> ONCE_REWRITE_TAC[untag_CONS_sing] >>
  ASM_REWRITE_TAC[APPEND]
QED

(* The writer's entries of fd: its writes and its queries *)
Definition wq_def:
  wq fd (p : (action, num # cquery) kact # (canswer, response) kres option) ⇔
    (∃s. FST p = Sock (Write fd s)) ∨ (∃q. FST p = Kv (fd, q))
End

Theorem wr_of_FILTER_wq:
  ∀tr. wr_of fd (FILTER (wq fd) tr) = wr_of fd tr
Proof
  Induct >> simp[wr_of_simps] >> PairCases >> Cases_on ‘h0’ >>
  TRY (rename1 ‘Sock a’ >> Cases_on ‘a’) >>
  rw[wq_def] >> gvs[wr_of_simps] >>
  TRY (PairCases_on ‘q’) >> gvs[wr_of_simps]
QED

Theorem reader_entries:
  ∀hh. EVERY (λp. FST p = Sock (Read fd)) (trans (reader fd) hh)
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >>
  ONCE_REWRITE_TAC[reader_unfold] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) hh’ >>
  qspecl_then [‘readable fd’, ‘K0’, ‘hh’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[] >>
  drule first_done_wait_nonempty >> strip_tac >> simp[Abbr ‘K0’] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Sock (Read fd))) K1) h2’ >>
  qspecl_then [‘emit (Sock (Read fd))’, ‘K1’, ‘h2’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac >- simp[trans_emit] >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K1’] >>
  ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[]) >>
  every_case_tac >> simp[]
QED

Theorem wloop_entries:
  ∀hh i. EVERY (wq fd) (trans (wloop (fd, i)) hh)
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[wloop_unfold] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Fetch i))) K0) hh’ >>
  qspecl_then [‘emit (Kv (fd, Fetch i))’, ‘K0’, ‘hh’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac >- simp[trans_emit, wq_def] >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K0’, wq_def] >>
  every_case_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit WR) K1) h2’ >>
  qspecl_then [‘emit WR’, ‘K1’, ‘h2’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac >- simp[trans_emit, Abbr ‘WR’, wq_def] >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K1’, Abbr ‘WR’, wq_def] >>
  simp[]
QED

Theorem writer_entries:
  EVERY (wq fd) (trans (writer fd) hh)
Proof
  simp[writer_def] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Start))) K0) hh’ >>
  qspecl_then [‘emit (Kv (fd, Start))’, ‘K0’, ‘hh’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac >- simp[trans_emit, wq_def] >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K0’, wq_def] >>
  every_case_tac >> simp[wloop_entries]
QED

Theorem EVERY_trans_both[local]:
  (∀h. EVERY P (trans m1 h)) ∧ (∀h. EVERY P (trans m2 h)) ⇒
  EVERY P (trans (both m1 m2) h)
Proof
  rpt strip_tac >>
  ‘FILTER (λx. ¬P x) (trans (both m1 m2) h) = []’
    by (DEP_REWRITE_TAC[trans_both_filter_left] >> simp[FILTER_EQ_NIL] >>
        fs[EVERY_MEM] >> metis_tac[]) >>
  fs[FILTER_EQ_NIL] >> ‘(λx. P x) = P’ by simp[FUN_EQ_THM] >> fs[]
QED

(* MAIN: a handler's entries are all about its own connection *)
Theorem chat_handler_on_fdc:
  ∀fd hh. EVERY (on_fdc fd) (trans (chat_handler fd) hh)
Proof
  rw[chat_handler_def] >> irule EVERY_trans_both >> conj_tac >> gen_tac
  >- (irule EVERY_MONOTONIC >> qexists ‘λp. FST p = Sock (Read fd)’ >>
      simp[reader_entries] >> simp[on_fdc_def, on_fd_def])
  >> irule EVERY_MONOTONIC >> qexists ‘wq fd’ >> simp[writer_entries] >>
  rw[wq_def, on_fdc_def, on_fd_def] >> simp[]
QED

(* The writer's part of a handler's transcript *)
Theorem writer_filter:
  FILTER (wq fd) (trans (writer fd) hh) = trans (writer fd) hh
Proof
  simp[FILTER_EQ_ID, writer_entries]
QED

Theorem chat_handler_writer:
  ∃(R : (event, (canswer, response) kres) snapshot list).
    FILTER (wq fd) (trans (chat_handler fd) L) = trans (writer fd) R
Proof
  simp[chat_handler_def] >>
  DEP_REWRITE_TAC[trans_both_filter_right] >> conj_tac
  >- (simp[FILTER_EQ_NIL] >>
      irule EVERY_MONOTONIC >> qexists ‘λp. FST p = Sock (Read fd)’ >>
      simp[reader_entries, wq_def])
  >> simp[writer_filter] >> metis_tac[]
QED

Theorem FILTER_prefix[local]:
  x ≼ y ⇒ FILTER P x ≼ FILTER P y
Proof
  rw[IS_PREFIX_APPEND] >> simp[FILTER_APPEND]
QED

Theorem prefix_TAKE_LENGTH:
  x ≼ y ⇒ x = TAKE (LENGTH x) y
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_LENGTH_APPEND]
QED



(* fd was accepted at the start of U2, and never in U1 or after *)
Theorem accepted_APPEND[local]:
  accepted (a ++ b) = accepted a ++ accepted b ∧
  accepted (h :: t) = accepted [h] ++ accepted t
Proof
  simp[accepted_def]
QED

Theorem acc_of_accepted:
  ∀U. EXISTS (acc_of d) U ⇒ MEM d (accepted U)
Proof
  Induct >> rw[] >> ONCE_REWRITE_TAC[accepted_APPEND] >> gvs[acc_of_def] >>
  simp[accepted_def]
QED

Theorem SPLITP_acc_of:
  ALL_DISTINCT (accepted (U1 ++ U2 ++ U3)) ∧ U2 ≠ [] ∧ acc_of d (HD U2) ⇒
  SPLITP (acc_of d) (U1 ++ U2 ++ U3) = (U1, U2 ++ U3)
Proof
  rpt strip_tac >> Cases_on ‘U2’ >> fs[] >>
  ‘accepted [h] = [d]’ by gvs[acc_of_def, accepted_def] >>
  ‘¬EXISTS (acc_of d) U1’
    by (strip_tac >> imp_res_tac acc_of_accepted >>
        qpat_x_assum ‘ALL_DISTINCT _’ mp_tac >>
        ONCE_REWRITE_TAC[accepted_APPEND] >> simp[] >>
        ONCE_REWRITE_TAC[accepted_APPEND] >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘SPLITP (acc_of d) U1 = (U1, [])’
    by (irule SPLITP_EVERY >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  simp[SPLITP_APPEND, rich_listTheory.SPLITP]
QED

Theorem writer_HD:
  trans (writer fd) R ≠ [] ⇒ FST (HD (trans (writer fd) R)) = Kv (fd, Start)
Proof
  simp[writer_def] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Start))) K0) R’ >>
  qspecl_then [‘emit (Kv (fd, Start))’, ‘K0’, ‘R’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac >> simp[trans_emit]
QED

Theorem MEM_accepted_acc:
  MEM d (accepted U) ⇔ ∃l. MEM (Accept l, SOME (Accepted d)) U
Proof
  simp[accepted_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> eq_tac >> rw[]
  >- (PairCases_on ‘p’ >> Cases_on ‘p0’ >> Cases_on ‘p1’ >> gvs[] >>
      TRY (Cases_on ‘x’) >> gvs[] >> metis_tac[])
  >> qexists ‘(Accept l, SOME (Accepted d))’ >> simp[]
QED

Theorem TAKE_prefix[local]:
  TAKE n l ≼ l
Proof
  simp[IS_PREFIX_EQ_TAKE'] >> metis_tac[]
QED

Theorem with_state_FILTER_pos:
  TR' ≼ TR ∧ k < LENGTH (FILTER P TR') ⇒
  ∃p. p < LENGTH TR' ∧
      EL k (FILTER (P ∘ FST) (with_state TR)) =
        (EL p TR, tap_fold chat_tap chat_delta empty_store (TAKE p TR))
Proof
  strip_tac >>
  ‘TR' = TAKE (LENGTH TR') TR’ by metis_tac[prefix_TAKE_LENGTH] >>
  ‘with_state TR' ≼ with_state TR’
    by (qpat_x_assum ‘TR' = _’ (fn th => ONCE_REWRITE_TAC[th]) >>
        simp[GSYM TAKE_with_state, TAKE_prefix]) >>
  ‘∀p. p < LENGTH TR' ⇒ EL p TR' = EL p TR ∧ TAKE p TR' = TAKE p TR’
    by (rpt strip_tac >> qpat_x_assum ‘TR' = _’ (fn th => ONCE_REWRITE_TAC[th]) >>
        simp[EL_TAKE, TAKE_TAKE_MIN, MIN_DEF]) >>
  qpat_x_assum ‘TR' = _’ kall_tac >>
  qabbrev_tac ‘W' = FILTER (P ∘ FST) (with_state TR')’ >>
  ‘W' ≼ FILTER (P ∘ FST) (with_state TR)’
    by (simp[Abbr ‘W'’] >> irule FILTER_prefix >> simp[]) >>
  ‘LENGTH W' = LENGTH (FILTER P TR')’
    by (simp[Abbr ‘W'’] >>
        metis_tac[LENGTH_MAP, MAP_FST_FILTER_FST, MAP_FST_with_state]) >>
  ‘k < LENGTH W'’ by simp[] >>
  ‘EL k (FILTER (P ∘ FST) (with_state TR)) = EL k W'’
    by (irule (GSYM is_prefix_el) >> simp[] >>
        imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
  ‘MEM (EL k W') (with_state TR')’
    by (simp[Abbr ‘W'’] >> metis_tac[EL_MEM, MEM_FILTER]) >>
  Cases_on ‘EL k W'’ >> fs[MEM_with_state] >>
  qexists ‘p’ >> simp[]
QED

(* MAIN (model-level safety, on the inner server): if the world hands out
   distinct connections and the hub answers by the tap's fold, then on
   every prefix U of the outer transcript, what is written to d is a
   prefix of what d is owed. *)
Theorem chat_inner_safe:
  answers_ok chat_tap chat_delta empty_store (trans (chat_inner lfd) hh) ∧
  fresh (untag (trans (chat_inner lfd) hh)) ∧
  fds_ok (untag (trans (chat_inner lfd) hh)) ∧
  U ≼ untag (trans (chat_inner lfd) hh) ⇒
  CONCAT (written d U) ≼ owed_m d U
Proof
  qabbrev_tac ‘TR = trans (chat_inner lfd) hh’ >> strip_tac >>
  drule untag_prefix >> strip_tac >> gvs[] >>
  rename1 ‘TR' ≼ TR’ >>
  ‘CONCAT (written d (untag TR')) = wr_of d (FILTER (wq d) TR')’
    by simp[wr_of_FILTER_wq, wr_of_def] >>
  simp[] >>
  (* the handler of d *)
  ‘freshc TR’ by simp[freshc_untag] >>
  ‘FILTER (on_fdc d) TR = [] ∨ ∃L. FILTER (on_fdc d) TR = trans (chat_handler d) L’
    by (qspecl_then [‘chat_handler’, ‘lfd’] mp_tac
          (Q.GENL [‘h’, ‘lfd’] cserver_with_isolates) >>
        simp[chat_handler_on_fdc] >> disch_then (qspec_then ‘hh’ mp_tac) >>
        fs[Abbr ‘TR’, chat_inner_def]) >>
  ‘FILTER (wq d) TR = FILTER (wq d) (FILTER (on_fdc d) TR)’
    by (simp[FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
        simp[FUN_EQ_THM] >> gen_tac >> simp[wq_def, on_fdc_def, on_fd_def] >>
        Cases_on ‘FST x’ >> simp[] >> metis_tac[PAIR, FST]) >>
  ‘FILTER (wq d) TR' ≼ FILTER (wq d) TR’ by simp[FILTER_prefix]
  >- (‘FILTER (wq d) TR = []’
        by (qpat_x_assum ‘FILTER (wq d) TR = _’ SUBST1_TAC >>
            qpat_x_assum ‘FILTER (on_fdc d) TR = _’ SUBST1_TAC >> simp[]) >>
      ‘FILTER (wq d) TR' = []’ by metis_tac[IS_PREFIX_NIL] >>
      simp[wr_of_simps])
  >> ‘∃(R : (event, (canswer, response) kres) snapshot list).
         FILTER (wq d) TR = trans (writer d) R’
       by (qpat_x_assum ‘FILTER (wq d) TR = _’ SUBST1_TAC >>
           qpat_x_assum ‘FILTER (on_fdc d) TR = _’ SUBST1_TAC >>
           metis_tac[chat_handler_writer]) >>
  qpat_x_assum ‘FILTER (wq d) TR = FILTER _ (FILTER _ _)’ kall_tac >>
  qabbrev_tac ‘WR = trans (writer d) R’ >>
  (* the writer's entries, each with the hub's state before it *)
  qabbrev_tac ‘Wl = FILTER (wq d ∘ FST) (with_state TR)’ >>
  ‘MAP FST Wl = WR’
    by simp[Abbr ‘Wl’, MAP_FST_FILTER_FST, MAP_FST_with_state] >>
  ‘LENGTH Wl = LENGTH WR’ by metis_tac[LENGTH_MAP] >>
  ‘∀k. k < LENGTH Wl ⇒
       ∃p. p < LENGTH TR ∧ FST (EL k Wl) = EL p TR ∧
           SND (EL k Wl) = tap_fold chat_tap chat_delta empty_store (TAKE p TR)’
    by (rpt strip_tac >> ‘MEM (EL k Wl) (with_state TR)’
          by metis_tac[EL_MEM, MEM_FILTER] >>
        Cases_on ‘EL k Wl’ >> gvs[MEM_with_state] >> metis_tac[]) >>
  qabbrev_tac ‘lg = λk. if k < LENGTH Wl then (SND (EL k Wl)).log
                        else lines_done (untag TR)’ >>
  ‘transitive (λ(x : ((action, num # cquery) kact # (canswer, response) kres option) # cstore) y. (SND x).log ≼ (SND y).log)’
    by (simp[relationTheory.transitive_def] >> metis_tac[IS_PREFIX_TRANS]) >>
  ‘SORTED (λx y. (SND x).log ≼ (SND y).log) Wl’
    by (qunabbrev_tac ‘Wl’ >> irule SORTED_FILTER >> conj_tac
        >- (simp[relationTheory.transitive_def] >> metis_tac[IS_PREFIX_TRANS])
        >> irule with_state_sorted >> first_assum ACCEPT_TAC) >>
  ‘∀m n. m < n ∧ n < LENGTH Wl ⇒ (SND (EL m Wl)).log ≼ (SND (EL n Wl)).log’
    by (qpat_x_assum ‘transitive _’ (assume_tac o MATCH_MP SORTED_EL_LESS) >>
        pop_assum (qspec_then ‘Wl’ mp_tac) >> ASM_REWRITE_TAC[] >>
        BETA_TAC >> metis_tac[]) >>
  ‘∀m. m < LENGTH Wl ⇒ (SND (EL m Wl)).log ≼ lines_done (untag TR)’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀k. k < LENGTH Wl ⇒ ∃p. _’ (drule_then strip_assume_tac) >>
        ASM_REWRITE_TAC[] >>
        ‘fds_ok (untag (TAKE p TR))’ by metis_tac[fds_ok_TAKE] >>
        simp[log_at] >> irule lines_done_mono >> irule untag_mono >>
        simp[IS_PREFIX_EQ_TAKE] >> qexists ‘p’ >> simp[]) >>
  ‘mono_log lg’
    by (simp[mono_log_def, Abbr ‘lg’] >> rpt strip_tac >>
        Cases_on ‘k < LENGTH Wl’ >> Cases_on ‘k' < LENGTH Wl’ >> simp[] >>
        TRY (Cases_on ‘k = k'’ >> gvs[] >> NO_TAC) >>
        TRY (metis_tac[]) >> ‘k < k'’ by simp[] >> metis_tac[])
  >> ‘fits_log d lg WR’
    by (simp[fits_log_def] >> rpt strip_tac >>
        ‘k < LENGTH Wl’ by simp[] >>
        qpat_assum ‘∀k. k < LENGTH Wl ⇒ ∃p. _’ (drule_then strip_assume_tac) >>
        ‘EL k WR = FST (EL k Wl)’ by metis_tac[EL_MAP] >>
        ‘EL p TR = (Kv (d, Fetch i), SOME (KvR a))’ by metis_tac[] >>
        qpat_assum ‘answers_ok _ _ _ _’
          (mp_tac o Q.SPECL [‘p’] o REWRITE_RULE[answers_ok_def]) >>
        disch_then (drule_then assume_tac) >>
        ‘fds_ok (untag (TAKE p TR))’ by metis_tac[fds_ok_TAKE] >>
        qunabbrev_tac ‘lg’ >> BETA_TAC >> ASM_REWRITE_TAC[] >>
        gvs[chat_delta_def, log_at])
  (* the entries of the writer within TR' *)
  >> qabbrev_tac ‘n = LENGTH (FILTER (wq d) TR')’ >>
  ‘FILTER (wq d) TR' = TAKE n WR’
    by (simp[Abbr ‘n’] >> metis_tac[prefix_TAKE_LENGTH]) >>
  ‘n ≤ LENGTH WR’ by (imp_res_tac IS_PREFIX_LENGTH >> gvs[]) >>
  ‘∀k. k < n ⇒
       ∃p. p < LENGTH TR' ∧ FST (EL k Wl) = EL p TR ∧
           SND (EL k Wl) = tap_fold chat_tap chat_delta empty_store (TAKE p TR)’
    by (rpt strip_tac >>
        qspecl_then [‘TR'’, ‘TR’, ‘k’, ‘wq d’] mp_tac
          (Q.GENL [‘TR'’, ‘TR’, ‘k’, ‘P’] with_state_FILTER_pos) >>
        impl_tac >- (qunabbrev_tac ‘n’ >> simp[]) >>
        strip_tac >> qexists ‘p’ >> qunabbrev_tac ‘Wl’ >> simp[]) >>
  Cases_on ‘n = 0’
  >- (qpat_x_assum ‘FILTER (wq d) TR' = _’ SUBST1_TAC >>
      pop_assum SUBST1_TAC >> simp[wr_of_simps]) >>
  ‘0 < LENGTH Wl ∧ n - 1 < LENGTH Wl’ by simp[] >>
  (* the Start entry *)
  qpat_assum ‘∀k. k < n ⇒ _’ (qspec_then ‘0’ mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> rename1 ‘FST (EL 0 Wl) = EL p0 TR’ >>
  ‘HD WR = EL p0 TR’ by (‘HD WR = EL 0 WR’ by simp[EL] >> metis_tac[EL_MAP]) >>
  (* the last writer entry in TR' *)
  qpat_assum ‘∀k. k < n ⇒ _’ (qspec_then ‘n - 1’ mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> rename1 ‘FST (EL (n - 1) Wl) = EL p1 TR’ >>
  ‘TR' = TAKE (LENGTH TR') TR’ by metis_tac[prefix_TAKE_LENGTH] >>
  ‘p0 < LENGTH TR ∧ p1 < LENGTH TR’ by (imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
  ‘LENGTH TR' ≤ LENGTH TR’ by (imp_res_tac IS_PREFIX_LENGTH) >>
  ‘∀p. p < LENGTH TR' ⇒ untag (TAKE p TR) ≼ untag TR'’
    by (rpt strip_tac >> irule untag_mono >>
        qpat_x_assum ‘TR' = _’ (fn th => ONCE_REWRITE_TAC[th]) >>
        simp[IS_PREFIX_EQ_TAKE] >> qexists ‘p’ >>
        qpat_x_assum ‘p < LENGTH TR'’ mp_tac >>
        qpat_x_assum ‘LENGTH TR' ≤ _’ mp_tac >>
        simp[TAKE_TAKE_MIN, MIN_DEF, LENGTH_TAKE_EQ]) >>
  qpat_x_assum ‘TR' = TAKE _ _’ kall_tac >>
  ‘lg (n - 1) ≼ lines_done (untag TR')’
    by (‘lg (n - 1) = (tap_fold chat_tap chat_delta empty_store (TAKE p1 TR)).log’
          by (qunabbrev_tac ‘lg’ >> BETA_TAC >> ASM_REWRITE_TAC[]) >>
        ‘fds_ok (untag (TAKE p1 TR))’ by metis_tac[fds_ok_TAKE] >>
        ASM_REWRITE_TAC[] >> simp[log_at] >> irule lines_done_mono >>
        metis_tac[]) >>
  Cases_on ‘∃j. SND (HD WR) = SOME (KvR (Pos j))’
  >- (pop_assum strip_assume_tac >>
      (* d's join position, from the hub *)
      ‘FST (HD WR) = Kv (d, Start)’
        by (qunabbrev_tac ‘WR’ >> irule writer_HD >> simp[] >>
            strip_tac >> fs[]) >>
      ‘EL p0 TR = (Kv (d, Start), SOME (KvR (Pos j)))’
        by metis_tac[PAIR, FST, SND] >>
      qabbrev_tac ‘st0 = tap_fold chat_tap chat_delta empty_store (TAKE p0 TR)’ >>
      ‘ALOOKUP st0.joins (n2w d) = SOME j’
        by (qpat_assum ‘answers_ok _ _ _ _’
              (mp_tac o Q.SPECL [‘p0’, ‘(d, Start)’, ‘KvR (Pos j)’] o
               REWRITE_RULE[answers_ok_def]) >>
            ASM_REWRITE_TAC[] >> simp[chat_delta_def, Abbr ‘st0’] >>
            every_case_tac >> simp[]) >>
      (* d < 2 ** 64: it was accepted *)
      ‘d < dimword (:64)’
        by (‘MEM (EL p0 TR) TR’ by metis_tac[EL_MEM] >>
            ‘EXISTS (on_fdc d) TR’
              by (simp[EXISTS_MEM] >> qexists ‘EL p0 TR’ >>
                  simp[on_fdc_def]) >>
            ‘MEM d (acceptedc TR)’
              by (qspecl_then [‘chat_handler’, ‘lfd’] mp_tac
                    (Q.GENL [‘h’, ‘lfd’] cserver_with_isolates) >>
                  simp[chat_handler_on_fdc] >> disch_then (qspec_then ‘hh’ mp_tac) >>
                  impl_tac >- fs[Abbr ‘TR’, chat_inner_def] >>
                  fs[Abbr ‘TR’, chat_inner_def]) >>
            fs[acceptedc_untag, fds_ok_def, MEM_accepted_acc] >>
            metis_tac[]) >>
      ‘fds_ok (untag (TAKE p0 TR))’ by metis_tac[fds_ok_TAKE] >>
      ‘hub_inv st0 (untag (TAKE p0 TR))’
        by (qunabbrev_tac ‘st0’ >> irule tap_inv >> first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘hub_inv _ _’ (strip_assume_tac o REWRITE_RULE[hub_inv_def]) >>
      first_x_assum (qspecl_then [‘d’, ‘j’] mp_tac) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      ‘lg 0 = lines_done (U1 ++ U2)’
        by (‘lg 0 = st0.log’ by (qunabbrev_tac ‘lg’ >> BETA_TAC >> ASM_REWRITE_TAC[]) >>
            ASM_REWRITE_TAC[]) >>
      qspecl_then [‘lg’, ‘d’, ‘R’, ‘j’] mp_tac
        (Q.GENL [‘lg’, ‘fd’, ‘R’, ‘j0’] writer_written) >>
      ‘trans (writer d) R = WR’ by simp[Abbr ‘WR’] >>
      pop_assum (fn th => REWRITE_TAC[th]) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac
          >- (qpat_x_assum ‘SND (HD WR) = SOME (KvR (Pos j'))’ mp_tac >>
              qpat_x_assum ‘SND (HD WR) = SOME (KvR (Pos j))’
                (fn th => REWRITE_TAC[th]) >> simp[])
          >> qpat_x_assum ‘lg 0 = _’ SUBST1_TAC >>
          qpat_x_assum ‘j = _’ SUBST1_TAC >>
          irule IS_PREFIX_LENGTH >> simp[lines_done_APPEND_prefix]) >>
      disch_then (qspec_then ‘n - 1’ mp_tac) >>
      impl_tac >- (qpat_x_assum ‘n ≤ _’ mp_tac >> qpat_x_assum ‘n ≠ 0’ mp_tac >>
                   simp[]) >>
      ‘SUC (n - 1) = n’ by simp[] >> pop_assum SUBST1_TAC >>
      qpat_x_assum ‘FILTER (wq d) TR' = _’ (SUBST1_TAC o SYM) >> strip_tac >>
      (* what d is owed *)
      ‘untag (TAKE p0 TR) ≼ untag TR'’ by metis_tac[] >>
      ‘∃U3. untag TR' = U1 ++ U2 ++ U3’ by metis_tac[IS_PREFIX_APPEND] >>
      ‘ALL_DISTINCT (accepted (untag TR'))’
        by (qpat_assum ‘untag TR' ≼ untag TR’
              (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
            qpat_assum ‘fresh _’ (mp_tac o REWRITE_RULE[fresh_def]) >>
            qpat_x_assum ‘untag TR = _’ SUBST1_TAC >>
            REWRITE_TAC[CONJUNCT1 accepted_APPEND, ALL_DISTINCT_APPEND] >>
            metis_tac[]) >>
      ‘owed_m d (untag TR') = DROP (LENGTH (lines_done U1)) (lines_done (untag TR'))’
        by (simp[owed_m_def] >>
            ‘SPLITP (acc_of d) (U1 ++ U2 ++ U3) = (U1, U2 ++ U3)’
              by (irule SPLITP_acc_of >> metis_tac[]) >>
            qpat_x_assum ‘untag TR' = _’ SUBST1_TAC >> simp[] >>
            Cases_on ‘U2’ >> fs[]) >>
      qpat_x_assum ‘owed_m _ _ = _’ SUBST1_TAC >>
      qpat_x_assum ‘CONCAT _ = _’ SUBST1_TAC >>
      irule IS_PREFIX_TRANS >> qexists ‘DROP j (lg (n - 1))’ >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘j = _’ SUBST1_TAC >> irule DROP_prefix >>
      first_assum ACCEPT_TAC)
  >> (* the writer was never told where d joined: it writes nothing *)
  qspecl_then [‘lg’, ‘d’, ‘R’, ‘LENGTH (lg (n - 1))’] mp_tac
    (Q.GENL [‘lg’, ‘fd’, ‘R’, ‘j0’] writer_written) >>
  ‘trans (writer d) R = WR’ by simp[Abbr ‘WR’] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      metis_tac[]) >>
  disch_then (qspec_then ‘n - 1’ mp_tac) >>
  impl_tac >- (qpat_x_assum ‘n ≤ _’ mp_tac >> qpat_x_assum ‘n ≠ 0’ mp_tac >>
               simp[]) >>
  ‘SUC (n - 1) = n’ by simp[] >> pop_assum SUBST1_TAC >>
  qpat_x_assum ‘FILTER (wq d) TR' = _’ (SUBST1_TAC o SYM) >>
  simp[DROP_LENGTH_NIL]
QED

(* MAIN: safety of the chat server in the model.  In any history in which
   the connections handed out are distinct, on every prefix U of the
   server's transcript, what has been written to d is a prefix of what d
   is owed: the lines completed after d was accepted, in order. *)
Theorem chat_server_safe:
  fresh (trans (chat_server lfd) hh) ∧ fds_ok (trans (chat_server lfd) hh) ∧
  U ≼ trans (chat_server lfd) hh ⇒
  CONCAT (written d U) ≼ owed_m d U
Proof
  simp[chat_server_def, trans_with_tap, wf_chat_inner] >> strip_tac >>
  irule chat_inner_safe >> simp[] >>
  qexistsl [‘tap_hist chat_tap chat_delta empty_store (chat_inner lfd) hh’, ‘lfd’] >>
  simp[tap_answers, wf_chat_inner]
QED
