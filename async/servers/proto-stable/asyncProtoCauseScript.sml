(*
  What makes the generic protocol handler act (model; option C, design/33
  §2.5 (c)).  The converse of its liveness: proto_handler P resp emits a
  new action with a new snapshot s only if its fd is readable in s, or s
  brings a response to one of its actions (the read's Data or EOF, or the
  write's answer).  Nothing else wakes it up.  As asyncEchoCause's
  handler_cause, for every protocol (no hypothesis on P).

  MAIN: proto_cause.
*)
Theory asyncProtoCause
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncProgress asyncEchoCause asyncProto asyncProtoServer
Libs
  preamble

(* The wait for fd, at the server's types *)
Overload rdy = “λfd. readable fd : (event, asyncServer$response) snapshot list ->
                                    (asyncServer$action, unit option) asyncCore$outcome”

(* After the wait for fd has finished, bind (readable fd) g is g () *)
Theorem readable_continues:
  first_readable fd h1 ⇒
  (bind (rdy fd) g (h1 ++ q)).actions = (g () q).actions
Proof
  rw[first_readable_def] >>
  drule_then (fn th => REWRITE_TAC[th]) bind_continues_actions >>
  ‘new_actions (log_of (rdy fd)) h1 = [] ∧ (rdy fd h1).actions = []’
    by simp[new_actions_def, log_of_def, readable_def, wait_def] >>
  ASM_REWRITE_TAC[LENGTH, skip_results_0, APPEND]
QED

(* An emit changes its actions with s only if s answers it, or it was
   answered earlier and its continuation changes *)
Theorem emit_cause:
  (bind (emit (a : asyncServer$action))
     (f : asyncServer$response -> (event, asyncServer$response) snapshot list ->
          (asyncServer$action, unit option) asyncCore$outcome)
     (q ++ [s : (event, asyncServer$response) snapshot])).actions ≠
  (bind (emit a) f q).actions ⇒
  IS_SOME (oHD s.results) ∨
  ∃s1 q' r. q = s1 :: q' ∧ oHD s1.results = SOME r ∧
            (f r (q' ++ [s])).actions ≠ (f r q').actions
Proof
  Cases_on ‘q’ >> simp[]
  >- (Cases_on ‘oHD s.results’ >> simp[] >>
      simp[bind_emit_unanswered, bind_emit_NIL])
  >> Cases_on ‘oHD h.results’
  >- simp[bind_emit_unanswered]
  >> qspecl_then [‘h’, ‘x’, ‘a’, ‘f’, ‘t ++ [s]’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS) >>
  qspecl_then [‘h’, ‘x’, ‘a’, ‘f’, ‘t’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS) >>
  simp[]
QED

(* A wait for fd changes its actions with s only if fd is readable in s,
   or the wait finished earlier and its continuation changes *)
Theorem readable_cause:
  (bind (rdy fd)
     (g : unit -> (event, asyncServer$response) snapshot list ->
          (asyncServer$action, unit option) asyncCore$outcome) (q ++ [s])).actions ≠
  (bind (rdy fd) g q).actions ⇒
  Readable fd ∈ s.ready ∨
  ∃h1 q2. q = h1 ++ q2 ∧ first_readable fd h1 ∧
          (g () (q2 ++ [s])).actions ≠ (g () q2).actions
Proof
  strip_tac >>
  qspecl_then [‘rdy fd’, ‘q ++ [s]’]
    strip_assume_tac history_split
  (* still waiting after s: no actions either way *)
  >- (‘∀h. h ≼ q ++ [s] ⇒ (bind (rdy fd) g h).actions = []’
        by (rpt strip_tac >>
            ‘bind (rdy fd) g h =
             <| actions := (rdy fd h).actions; result := NONE |>’
              by (irule bind_running >> rpt strip_tac >>
                  gvs[IS_PREFIX_EQ_TAKE] >>
                  first_x_assum (qspec_then ‘MIN n n'’ mp_tac) >>
                  simp[TAKE_TAKE_MIN]) >>
            simp[readable_def, wait_def]) >>
      ‘q ≼ q ++ [s]’ by simp[] >> metis_tac[IS_PREFIX_REFL])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[] >>
  ‘first_readable fd h1’ by simp[first_readable_def] >>
  Cases_on ‘h2’ using SNOC_CASES
  (* the wait finished at s itself *)
  >- (disj1_tac >> gvs[] >> metis_tac[first_readable_last])
  >> ‘s = x ∧ q = h1 ++ l’
       by (‘SNOC s q = SNOC x (h1 ++ l)’ by gvs[SNOC_APPEND] >> fs[SNOC_11])
  >> gvs[] >> disj2_tac >> qexistsl [‘h1’, ‘l’] >> simp[] >>
  qpat_x_assum ‘_ ≠ _’ mp_tac >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  qspecl_then [‘fd’, ‘h1’, ‘g’, ‘l ++ [s]’] mp_tac
    (Q.GENL [‘fd’, ‘h1’, ‘g’, ‘q’] readable_continues) >>
  qspecl_then [‘fd’, ‘h1’, ‘g’, ‘l’] mp_tac
    (Q.GENL [‘fd’, ‘h1’, ‘g’, ‘q’] readable_continues) >>
  simp[]
QED

(* MAIN: the handler's actions change with a new snapshot s only if its fd
   is readable in s, or s brings a response *)
Theorem proto_cause:
  ∀q s buf.
    (proto_handler P resp (fd, buf) (q ++ [s])).actions ≠
    (proto_handler P resp (fd, buf) q).actions ⇒
    Readable fd ∈ s.ready ∨ IS_SOME (oHD s.results)
Proof
  gen_tac >> completeInduct_on ‘LENGTH q’ >> rpt strip_tac >> gvs[PULL_FORALL] >>
  qpat_x_assum ‘_ ≠ _’ mp_tac >> ONCE_REWRITE_TAC[proto_handler_unfold] >>
  Cases_on ‘P.parse buf’ >> simp[return_def]
  (* a complete request: the write, then the handler on the rest *)
  >- (rename1 ‘PComplete req rest’ >>
      strip_tac >> drule emit_cause >> strip_tac >> simp[] >>
      gvs[] >> first_x_assum (qspecl_then [‘q'’, ‘s’, ‘rest’] mp_tac) >> simp[])
  (* incomplete: wait for fd, read, continue *)
  >> strip_tac >> drule readable_cause >> strip_tac >> simp[] >> gvs[] >>
  drule emit_cause >> strip_tac >> simp[] >> gvs[] >>
  ‘0 < LENGTH h1’ by (drule first_readable_nonempty >> Cases_on ‘h1’ >> simp[]) >>
  Cases_on ‘r’ >> gvs[return_def] >>
  TRY (rename1 ‘Data d’ >>
       first_x_assum (qspecl_then [‘q'’, ‘s’, ‘buf ++ d’] mp_tac) >> simp[] >> NO_TAC) >>
  first_x_assum (qspecl_then [‘q'’, ‘s’, ‘buf’] mp_tac) >> simp[]
QED
