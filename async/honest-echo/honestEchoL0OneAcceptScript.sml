(*
  The echo server accepts at most once per round (for cf-actions: with
  honestEchoL0NoGuard's echo_guard_stop, a failed D25 guard shows on the
  trace as 2^64 − 1 accepted connections).

  server_one_accept: if every action is answered in the next snapshot
  (prompt), the server's new actions in any round hold at most one
  Accept: it waits for the listener before each accept, and after an
  accept it waits for the answer (a later snapshot) before accepting again;
  the handlers it starts never accept.
  echo_one_accept: the same for the relabelled server on the loop's run.
  echo_guard_stop_accepted: the loop's guard fails only after
  2^64 − 1 accepts.
*)
Theory honestEchoL0OneAccept
Ancestors
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncProgress
  asyncM4RelabelDist asyncM4Relabel asyncM4SockModel asyncM3World
  honestL1PFModel honestL1PFSpec honestEchoL0Spec honestEchoL0Run honestEchoL0NoGuard
Libs
  preamble

(* Accepts on any listener *)
Overload nacc = “asyncProgress$count (λa. ∃l. a = asyncServer$Accept l)”

Theorem nacc_APPEND[local]:
  nacc (xs ++ ys) = nacc xs + nacc ys
Proof
  simp[asyncProgressTheory.count_def, FILTER_APPEND_DISTRIB]
QED

(* Before the listener is first readable, the server has done nothing *)
Theorem server_idle:
  (∀n. n ≤ LENGTH h ⇒
       (readable lfd (TAKE n h) : (asyncServer$action, unit option) asyncCore$outcome).result =
       NONE) ⇒
  (server lfd h).actions = []
Proof
  strip_tac >> ONCE_REWRITE_TAC[server_steps] >>
  ‘bind (readable lfd) (λu. bind (emit (Accept lfd)) (after_accept lfd)) h =
   <| actions := (readable lfd h).actions; result := NONE |>’
    by (irule asyncLevel1Theory.bind_running >> first_assum ACCEPT_TAC) >>
  simp[asyncServerTheory.readable_def, asyncLevel1Theory.wait_def]
QED

Theorem server_nil:
  (server lfd []).actions = []
Proof
  irule server_idle >> simp[asyncServerTheory.readable_def, asyncLevel1Theory.wait_def, first_some_def]
QED

(* As asyncProgress's after_accept_view, for accepts on any listener *)
Theorem after_accept_view_any:
  prompt (after_accept lfd r) q ⇒
  ∃V. LENGTH V = LENGTH q ∧ prompt (server lfd) V ∧
      ∀j. nacc (after_accept lfd r (TAKE j q)).actions = nacc (server lfd (TAKE j V)).actions
Proof
  Cases_on ‘∃c. r = Accepted c’
  >- (gvs[after_accept_def] >> strip_tac
      >> qexists_tac ‘right_view (handler c) (server lfd) q’
      >> drule prompt_both >> simp[views_ready, asyncLevel1Theory.map_def] >> rpt strip_tac
      >> qspecl_then [‘handler c’, ‘server lfd’, ‘λa. ∃l. a = Accept l’, ‘TAKE j q’] mp_tac
           (Q.GENL [‘m1’, ‘m2’, ‘P’, ‘h’] count_both)
      >> simp[wf_handler, wf_server, views_TAKE, asyncProgressTheory.count_def, asyncLevel1Theory.map_def]
      >> strip_tac
      >> qmatch_asmsub_abbrev_tac ‘LENGTH (FILTER _ (handler c HV).actions)’
      >> ‘FILTER (λa. ∃l. a = Accept l) (handler c HV).actions = []’
           by (rw[FILTER_EQ_NIL, EVERY_MEM] >> strip_tac >> drule handler_actions_own >> simp[])
      >> fs[])
  >> ‘after_accept lfd r = server lfd’ by (Cases_on ‘r’ >> gvs[after_accept_def])
  >> rw[] >> qexists_tac ‘q’ >> simp[]
QED

(* MAIN (the core): one more snapshot adds at most one accept *)
Theorem server_accept_step:
  ∀h s. prompt (server lfd) (h ++ [s]) ⇒
        nacc (server lfd (h ++ [s])).actions ≤ nacc (server lfd h).actions + 1
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt strip_tac >>
  qspecl_then [‘readable lfd : (asyncServer$event, asyncServer$response) snapshot list ->
                                (asyncServer$action, unit option) asyncCore$outcome’, ‘h ++ [s]’]
    strip_assume_tac asyncLevel1Theory.history_split
  >- (‘(server lfd (h ++ [s])).actions = []’
        by (irule server_idle >> metis_tac[]) >>
      simp[asyncProgressTheory.count_def]) >>
  ‘x = ()’ by simp[oneTheory.one] >> gvs[] >>
  ‘first_readable lfd h1’ by simp[first_readable_def] >>
  Cases_on ‘h2’
  >- ((* the first readable snapshot is the new one *)
      gvs[] >>
      ‘(server lfd (h ++ [s])).actions = [Accept lfd]’
        by (drule_then (qspec_then ‘[]’ mp_tac) server_accepts >> simp[bind_emit_NIL]) >>
      ‘(server lfd h).actions = []’
        by (qspecl_then [‘lfd’, ‘h ++ [s]’, ‘LENGTH h’] mp_tac
              (Q.GENL [‘lfd’, ‘h1’, ‘n’] server_waiting_actions) >>
            simp[TAKE_APPEND1]) >>
      simp[asyncProgressTheory.count_def]) >>
  rename1 ‘h1 ++ s1 :: h3’ >>
  ‘h ++ [s] = h1 ++ [s1] ++ h3’ by simp[] >>
  ‘prompt (server lfd) (h1 ++ [s1] ++ h3)’ by metis_tac[] >>
  drule_all prompt_accept_answered >> strip_tac >>
  drule_all prompt_after_accept >> strip_tac >>
  drule after_accept_view_any >> strip_tac >>
  ‘∀q. q ≼ h3 ⇒
       nacc (server lfd (h1 ++ [s1] ++ q)).actions =
       1 + nacc (server lfd (TAKE (LENGTH q) V)).actions’
    by (rpt strip_tac >>
        qspecl_then [‘lfd’, ‘h1’, ‘s1’, ‘r’, ‘q’] mp_tac
          (Q.GENL [‘lfd’, ‘h1’, ‘s’, ‘r’, ‘q’] server_after_accept) >>
        simp[] >> strip_tac >>
        first_x_assum (qspec_then ‘LENGTH q’ mp_tac) >>
        ‘TAKE (LENGTH q) h3 = q’ by gvs[IS_PREFIX_APPEND, TAKE_LENGTH_APPEND] >>
        simp[asyncProgressTheory.count_def]) >>
  Cases_on ‘h3 = []’
  >- ((* the accept's answer is the new snapshot *)
      gvs[] >>
      first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[] >> strip_tac >>
      fs[server_nil, asyncProgressTheory.count_def]) >>
  (* later: by induction on the view *)
  ‘∃h3'. h3 = h3' ++ [s]’
    by (Cases_on ‘h3’ using SNOC_CASES >> gvs[SNOC_APPEND] >>
        qpat_x_assum ‘h ++ [s] = _’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
        simp[]) >>
  gvs[] >>
  ‘nacc (server lfd (h1 ++ [s1] ++ h3' ++ [s])).actions = nacc (server lfd V).actions + 1’
    by (qpat_assum ‘∀q. q ≼ _ ⇒ _’ (qspec_then ‘h3' ++ [s]’ mp_tac) >>
        impl_tac >- simp[] >>
        ‘TAKE (LENGTH (h3' ++ [s])) V = V’ by simp[TAKE_LENGTH_TOO_LONG] >>
        pop_assum (fn th => REWRITE_TAC[th]) >>
        metis_tac[APPEND_ASSOC]) >>
  ‘nacc (server lfd (h1 ++ [s1] ++ h3')).actions =
   nacc (server lfd (TAKE (LENGTH h3') V)).actions + 1’
    by (qpat_assum ‘∀q. q ≼ _ ⇒ _’ (qspec_then ‘h3'’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> fs[]) >>
  ‘TAKE (LENGTH h3') V ++ [EL (LENGTH h3') V] = V’
    by (‘LENGTH h3' < LENGTH V’ by simp[] >>
        simp[GSYM SNOC_APPEND, SNOC_EL_TAKE] >>
        simp[TAKE_LENGTH_TOO_LONG, GSYM ADD1, TAKE_SUC_BY_TAKE] >>
        metis_tac[SNOC_EL_TAKE, SNOC_APPEND, TAKE_LENGTH_TOO_LONG, ADD1, LESS_EQ_REFL]) >>
  qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘TAKE (LENGTH h3') V’ mp_tac) >>
  simp[] >> disch_then (qspec_then ‘EL (LENGTH h3') V’ mp_tac) >>
  qpat_x_assum ‘_ ++ [_] = V’ (fn th => REWRITE_TAC[th]) >>
  simp[] >> strip_tac >>
  qpat_x_assum ‘nacc (server lfd (_ ++ [_] ++ _ ++ [_])).actions = _’
    (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  fs[]
QED

(* MAIN: in every round, the server's new actions hold at most one accept *)
Theorem server_one_accept:
  prompt (server lfd) h ⇒ nacc (new_actions (log_of (server lfd)) h) ≤ 1
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, server_nil, asyncProgressTheory.count_def] >>
  rename1 ‘SNOC s h’ >> simp[SNOC_APPEND] >> strip_tac >>
  ‘(server lfd (h ++ [s])).actions =
   (server lfd h).actions ++ new_actions (log_of (server lfd)) (h ++ [s])’
    by (qspecl_then [‘log_of (server lfd)’, ‘h’, ‘s’] mp_tac
          (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix) >>
        simp[log_of_def, wf_SNOC_actions, wf_server]) >>
  drule server_accept_step >> simp[nacc_APPEND]
QED

(* ------------------------------------------------------------------------
   On the loop's run
   ------------------------------------------------------------------------ *)

(* Answering every action of a round in the next snapshot is prompt *)
Theorem relabel_prompt:
  (∀i. i < LENGTH h ⇒
       LENGTH (EL i h).results = LENGTH (new_actions (log_of (srelabel (server k))) (TAKE i h))) ⇒
  prompt (server k) (MAP sfs h)
Proof
  rw[prompt_def, responses_at_def, EL_MAP, snap_map_def] >>
  first_x_assum drule >> simp[new_actions_relabel, MAP_TAKE]
QED

(* MAIN: the loop's server accepts at most once per round *)
Theorem echo_one_accept:
  ri lfd (srelabel (server k)) (h, (w, ps), evs) ⇒
  honestL1PFModel$naccepts (new_actions (log_of (srelabel (server k))) h) ≤ 1
Proof
  rw[ri_def] >>
  ‘prompt (server k) (MAP sfs h)’ by (irule relabel_prompt >> simp[]) >>
  drule server_one_accept >>
  simp[new_actions_relabel, honestL1PFModelTheory.naccepts_def, rich_listTheory.FILTER_MAP,
       asyncProgressTheory.count_def] >>
  ‘(λa. ∃l. a = Accept l) o sfa = (λa. ∃l. a = asyncServer$Accept l)’
    by (simp[FUN_EQ_THM] >> Cases >> simp[sfa_def]) >>
  simp[]
QED

(* MAIN (for cf-actions): the echo loop's guard fails only after
   2^64 − 1 accepts *)
Theorem echo_guard_stop_accepted:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  prounds_t lfd hw ifds (srelabel (server k)) ws0 n = SOME (h, (w, ps), evs, logs) ∧
  ¬hdl_room lfd ps (honestL1PFModel$naccepts (new_actions (log_of (srelabel (server k))) h)) ⇒
  2 ** 64 − 1 ≤ LENGTH (l0_accepted evs)
Proof
  strip_tac >> drule_all echo_guard_stop >> strip_tac >>
  drule_all ri_echo >> strip_tac >>
  drule echo_one_accept >> strip_tac >> fs[]
QED
