(*
  The server skeleton, parametric in its action vocabulary (design/34,
  the principled version of KV liveness).

  A vocabulary V says how the socket actions and their responses sit inside
  a larger action type 'a and response type 'r:
     acc l, rd fd, wr fd d : 'a     the socket actions Accept, Read, Write;
     qry q : 'a                     a query (e.g. to a store), if any;
     sact : 'a → action option      the socket action an action is, if any;
     rinj : response → 'r           the world's responses, inside 'r;
     sres : 'r → response option    the world response a response is, if any;
     kans : 'r → 'k option          the answer to a query a response is, if any;
     owner : 'a → num option        the connection an action belongs to.
  server_v V h lfd is server_with with Accept and Accepted read through V.

  Instances:
   - idV, the identity vocabulary: server_v idV = server_with
     (server_with_eq_v), so every result proved for server_v holds for
     server_with with the same statement;
   - the Sock/Kv vocabulary of with_store (asyncServerWithK's server_with_k)
     is another instance (in a later file, with the KV theories).

  sproj V: the socket part of a transcript over V (untag, for Sock/Kv; the
  identity, for idV).
*)
Theory skeletonV
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript echoServer
  echoServerSafety skeleton
Libs
  BasicProvers

Datatype:
  vocab = <| acc : num -> 'a ; rd : num -> 'a ; wr : num -> string -> 'a ;
             qry : 'q -> 'a ;
             sact : 'a -> echoServer$action option ;
             rinj : echoServer$response -> 'r ;
             sres : 'r -> echoServer$response option ;
             kans : 'r -> 'k option ;
             owner : 'a -> num option |>
End

(* The socket actions and responses are embedded faithfully, and Read and
   Write belong to their fd, Accept to no connection *)
Definition vocab_ok_def:
  vocab_ok V ⇔
    (∀l. V.sact (V.acc l) = SOME (Accept l)) ∧
    (∀fd. V.sact (V.rd fd) = SOME (Read fd)) ∧
    (∀fd d. V.sact (V.wr fd d) = SOME (Write fd d)) ∧
    (∀a x. V.sact a = SOME x ⇒
           (∀l. x = Accept l ⇒ a = V.acc l) ∧ (∀fd. x = Read fd ⇒ a = V.rd fd) ∧
           (∀fd d. x = Write fd d ⇒ a = V.wr fd d)) ∧
    (∀r. V.sres (V.rinj r) = SOME r) ∧
    (∀r x. V.sres r = SOME x ⇒ r = V.rinj x) ∧
    (∀r. V.kans (V.rinj r) = NONE) ∧
    (∀fd. V.owner (V.rd fd) = SOME fd) ∧ (∀fd d. V.owner (V.wr fd d) = SOME fd) ∧
    (∀l. V.owner (V.acc l) = NONE)
End

(* Queries are not socket actions *)
Definition vocab_qok_def:
  vocab_qok V ⇔ ∀q. V.sact (V.qry q) = NONE
End

(* The fd the server is handed, if a response is Accepted fd *)
Definition vaccd_def:
  vaccd V r = case V.sres r of SOME (Accepted fd) => SOME fd | _ => NONE
End

(* The identity vocabulary *)
Definition idV_def:
  idV : (echoServer$action, 'k, 'q, echoServer$response) vocab =
    <| acc := Accept ; rd := Read ; wr := Write ; qry := (λq. Accept 0) ;
       sact := SOME ; rinj := I ; sres := SOME ; kans := K NONE ;
       owner := (λa. case a of Read fd => SOME fd | Write fd d => SOME fd
                             | Accept l => NONE) |>
End

Theorem vocab_ok_idV:
  vocab_ok idV
Proof
  rw[vocab_ok_def, idV_def]
QED

(* ------------------------------------------------------------------------
   The skeleton
   ------------------------------------------------------------------------ *)

Definition server_v_body_def:
  server_v_body V h r lfd =
    bind (readable lfd) (λu.
    bind (emit (V.acc lfd)) (λres.
      case vaccd V res of
        SOME fd => map (λp. ()) (both (h fd) (r lfd))
      | NONE => r lfd))
End

Theorem server_v_body_contractive:
  contractive (server_v_body V h)
Proof
  rw[contractive_def, server_v_body_def]
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> gen_tac >> CASE_TAC >> simp[nonexpansive_call]
  >> ho_match_mp_tac nonexpansive_map >> ho_match_mp_tac nonexpansive_both
  >> simp[nonexpansive_const, nonexpansive_call]
QED

Definition server_v_def:
  server_v V h = fix (server_v_body V h)
End

(* MAIN: the skeleton satisfies its recursive equation *)
Theorem server_v_unfold:
  server_v V h lfd =
    bind (readable lfd) (λu.
    bind (emit (V.acc lfd)) (λres.
      case vaccd V res of
        SOME fd => map (λp. ()) (both (h fd) (server_v V h lfd))
      | NONE => server_v V h lfd))
Proof
  simp[server_v_def, Once (MATCH_MP fix_unfold server_v_body_contractive)]
  >> simp[server_v_body_def]
QED

Theorem wf_server_v:
  (∀fd. wf (h fd)) ⇒ wf (server_v V h lfd)
Proof
  strip_tac >> simp[server_v_def] >> irule wf_fix
  >> simp[server_v_body_contractive]
  >> rw[server_v_body_def]
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> gen_tac >> CASE_TAC >> simp[]
  >> irule wf_map >> irule wf_both >> simp[]
QED

Theorem settled_server_v:
  (∀fd. wf (h fd) ∧ settled (h fd)) ⇒ settled (server_v V h lfd)
Proof
  strip_tac >> simp[server_v_def] >> irule settled_fix
  >> simp[server_v_body_contractive]
  >> rw[server_v_body_def]
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> gen_tac >> CASE_TAC >> simp[]
  >> irule settled_map >> irule settled_both >> simp[]
QED

(* MAIN: server_with is the skeleton for the identity vocabulary *)
Theorem server_with_eq_v:
  server_with h = server_v idV h
Proof
  simp[server_with_def, server_v_def] >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, server_with_body_def, server_v_body_def, idV_def] >> rpt gen_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> rpt gen_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> Cases >> simp[vaccd_def]
QED

(* ------------------------------------------------------------------------
   The socket part of a transcript
   ------------------------------------------------------------------------ *)

Definition sproj_def:
  sproj V (tr : ('a # 'r option) list) =
    FLAT (MAP (λ(a, r). case V.sact a of
                          SOME x => [(x, OPTION_BIND r V.sres)]
                        | NONE => []) tr)
End

Theorem sproj_APPEND[simp]:
  sproj V (l1 ++ l2) = sproj V l1 ++ sproj V l2
Proof
  simp[sproj_def]
QED

Theorem sproj_idV[simp]:
  ∀tr. sproj idV tr = tr
Proof
  Induct >> simp[sproj_def] >> PairCases >> simp[idV_def] >>
  Cases_on ‘h1’ >> simp[GSYM sproj_def] >> fs[sproj_def, idV_def]
QED

(* The entries of a transcript that belong to connection fd *)
Definition on_fd_v_def:
  on_fd_v V fd (p : 'a # 'r option) ⇔ V.owner (FST p) = SOME fd
End

Theorem on_fd_v_idV:
  on_fd_v idV fd = on_fd fd
Proof
  simp[FUN_EQ_THM, on_fd_v_def, on_fd_def, idV_def] >> PairCases >> simp[] >>
  Cases_on ‘x0’ >> simp[]
QED
