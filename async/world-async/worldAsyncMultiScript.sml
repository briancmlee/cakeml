(*
  Experiment (design/12-world-as-async.md §8): the concurrent echo server
  in a closed system with any number of clients, each an async program.

  The network kernel now has
   - a pending-connection queue (filled by the clients' Connect, emptied by
     the server's Accept) and a counter handing out fresh connection
     numbers, all above the listener lfd;
   - per connection g, an upward queue (client to server) and a downward
     queue (server to client).
  Clients name their connection in every action (Send g d, Recv g), so
  client1 and client2 can run side by side as  both client1 client2 : the
  kernel answers the combined batch positionally and `both` routes the
  responses back.

  run lfd m c n polls the server m and the client program c (e.g. a `both`
  of several clients) side by side for n rounds, as in worldAsyncNet.

  Results:
   - multi_conservation: for ANY server and ANY clients, on every
     connection, the network neither creates nor drops a string; and the
     connections handed out are exactly those connected, in order
     (fresh_kernel: so they are distinct; `fresh` is a kernel fact here).
   - (MAIN) closed_echo: the echo server `server lfd` against ANY client
     program: on every connection, everything sent is received, queued
     downwards, being written back this round, or queued upwards.
   - (MAIN) every_client_receives_what_it_sent: on every connection, the
     strings received are a prefix of the strings sent, in order.
   - example_*: EVAL of two clients connected at once.
*)
Theory worldAsyncMulti
Ancestors
  pair list rich_list arithmetic option pred_set string combin
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer
  asyncServerSafety worldAsyncCtrans
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The clients' vocabulary
   ------------------------------------------------------------------------ *)

Datatype:
  cevent = CReadable num
End

Datatype:
  caction = Connect | Send num string | Recv num
End

Datatype:
  cresponse = Connected num | Sent | Got string | Empty
End

(* The strings sent / received on connection g, in a client transcript *)
Definition sent_def:
  sent g tr =
    FLAT (MAP (λp. case FST p of Send g' d => if g' = g then [d] else []
                               | _ => []) tr)
End

Definition got_def:
  got g tr =
    FLAT (MAP (λp. case p of (Recv g', SOME (Got d)) => if g' = g then [d] else []
                           | _ => []) tr)
End

Theorem sent_APPEND[simp]:
  sent g (t1 ++ t2) = sent g t1 ++ sent g t2
Proof
  simp[sent_def]
QED

Theorem got_APPEND[simp]:
  got g (t1 ++ t2) = got g t1 ++ got g t2
Proof
  simp[got_def]
QED

Theorem sent_NIL[simp]: sent g [] = []
Proof
  simp[sent_def]
QED

Theorem got_NIL[simp]: got g [] = []
Proof
  simp[got_def]
QED

(* ------------------------------------------------------------------------
   The network kernel
   ------------------------------------------------------------------------ *)

Datatype:
  knet = <| pending : num list ; next : num ;
            up : num -> string list ; down : num -> string list |>
End

(* Connection numbers start above the listener *)
Definition net0_def:
  net0 lfd = <| pending := []; next := SUC lfd; up := K []; down := K [] |>
End

(* The connections handed out so far *)
Definition conns_def:
  conns lfd k = GENLIST (λi. SUC lfd + i) (k.next - SUC lfd)
End

Definition sact_def:
  sact k (Read g) =
    (case k.up g of
       [] => (k, WouldBlock)
     | d :: r => (k with up := k.up⦇g ↦ r⦈, Data d)) ∧
  sact k (Write g d) = (k with down := k.down⦇g ↦ k.down g ++ [d]⦈, Written) ∧
  sact k (Accept l) =
    case k.pending of
      [] => (k, NoConn)
    | g :: r => (k with pending := r, Accepted g)
End

Definition cact_def:
  cact k Connect =
    (k with <| next := SUC k.next; pending := k.pending ++ [k.next] |>,
     Connected k.next) ∧
  cact k (Send g d) = (k with up := k.up⦇g ↦ k.up g ++ [d]⦈, Sent) ∧
  cact k (Recv g) =
    case k.down g of
      [] => (k, Empty)
    | d :: r => (k with down := k.down⦇g ↦ r⦈, Got d)
End

Definition sacts_def:
  sacts k [] = (k, []) ∧
  sacts k (a :: as) =
    let (k1, r) = sact k a; (k2, rs) = sacts k1 as in (k2, r :: rs)
End

Definition cacts_def:
  cacts k [] = (k, []) ∧
  cacts k (a :: as) =
    let (k1, r) = cact k a; (k2, rs) = cacts k1 as in (k2, r :: rs)
End

(* Readiness, from the kernel state: the listener when a connection is
   pending; a connection when it has data for the reader *)
Definition ssnap_def:
  ssnap lfd k n rs =
    <| ready := set ((if k.pending ≠ [] then [Readable lfd] else []) ++
                     MAP Readable (FILTER (λg. k.up g ≠ []) (conns lfd k)));
       now := n; results := rs |>
End

Definition csnap_def:
  csnap lfd k n rs =
    <| ready := set (MAP CReadable (FILTER (λg. k.down g ≠ []) (conns lfd k)));
       now := n; results := rs |>
End

(* ------------------------------------------------------------------------
   Connecting the server to the clients
   ------------------------------------------------------------------------ *)

Definition world_step_def:
  world_step lfd c (k, hc) as =
    let (k1, rs) = sacts k as;
        (k2, rc) = cacts k1 (new_actions (log_of c) hc);
        n = SUC (LENGTH hc)
    in (ssnap lfd k2 n rs, (k2, hc ++ [csnap lfd k2 n rc]))
End

Definition run_def:
  run lfd m c 0 = ([], (net0 lfd, [])) ∧
  run lfd m c (SUC n) =
    let (hs, w) = run lfd m c n;
        (s, w') = world_step lfd c w (new_actions (log_of m) hs)
    in (hs ++ [s], w')
End

(* ------------------------------------------------------------------------
   The kernel moves strings and connections; it never creates or drops
   them
   ------------------------------------------------------------------------ *)

Theorem sacts_moves:
  ∀as k k' rs.
    sacts k as = (k', rs) ⇒
    (∀g. read g (zipr as rs) ++ k'.up g = k.up g ∧
         k'.down g = k.down g ++ written g (zipr as rs)) ∧
    accepted (zipr as rs) ++ k'.pending = k.pending ∧
    k'.next = k.next
Proof
  Induct >- simp[sacts_def, zipr_def, read_def, written_def, accepted_def]
  >> rpt gen_tac >> simp[sacts_def] >> rename1 ‘sact k a’
  >> Cases_on ‘sact k a’ >> rename1 ‘_ = (k1, r)’
  >> Cases_on ‘sacts k1 as’ >> simp[sacts_def] >> strip_tac >> gvs[]
  >> first_x_assum drule >> strip_tac
  >> Cases_on ‘a’ >> gvs[sact_def, AllCaseEqs(), zipr_def]
  >> rw[] >> TRY (first_x_assum (qspec_then ‘g’ mp_tac))
  >> rw[APPLY_UPDATE_THM] >> gvs[]
QED

Theorem cacts_moves:
  ∀as k k' rs.
    cacts k as = (k', rs) ⇒
    (∀g. k'.up g = k.up g ++ sent g (zipr as rs) ∧
         got g (zipr as rs) ++ k'.down g = k.down g) ∧
    k'.pending = k.pending ++ GENLIST (λi. k.next + i) (k'.next - k.next) ∧
    k.next ≤ k'.next
Proof
  Induct >- simp[cacts_def, zipr_def]
  >> rpt gen_tac >> simp[cacts_def] >> rename1 ‘cact k a’
  >> Cases_on ‘cact k a’ >> rename1 ‘_ = (k1, r)’
  >> Cases_on ‘cacts k1 as’ >> simp[cacts_def] >> strip_tac >> gvs[]
  >> first_x_assum drule >> strip_tac
  >> Cases_on ‘a’ >> gvs[cact_def, AllCaseEqs(), zipr_def]
  >> rw[] >> TRY (first_x_assum (qspec_then ‘g’ mp_tac))
  >> rw[APPLY_UPDATE_THM] >> gvs[sent_def, got_def]
  (* Connect: one more connection, k.next, in front of the later ones *)
  >> ‘k'.next - k.next = SUC (k'.next - SUC k.next)’ by simp[]
  >> pop_assum SUBST1_TAC >> simp[GENLIST_CONS, o_DEF, ADD_CLAUSES]
QED

Theorem conns_extend:
  SUC lfd ≤ n1 ∧ n1 ≤ n2 ⇒
  GENLIST (λi. SUC lfd + i) (n1 - SUC lfd) ++ GENLIST (λi. n1 + i) (n2 - n1) =
  GENLIST (λi. SUC lfd + i) (n2 - SUC lfd)
Proof
  strip_tac
  >> qabbrev_tac ‘a = n1 - SUC lfd’ >> qabbrev_tac ‘b = n2 - n1’
  >> ‘n2 - SUC lfd = b + a’ by simp[Abbr ‘a’, Abbr ‘b’]
  >> pop_assum SUBST1_TAC >> REWRITE_TAC[GENLIST_APPEND] >> AP_TERM_TAC
  >> simp[GENLIST_FUN_EQ, Abbr ‘a’]
QED

(* For ANY server m and ANY client program c: on every connection, the
   network neither creates nor drops a string; and the server is handed
   exactly the connections that were made, in order *)
Theorem multi_conservation:
  ∀n hs k hc.
    run lfd m c n = (hs, (k, hc)) ⇒
    (∀g. read g (ctrans m hs) ++ k.up g = sent g (ctrans c hc) ∧
         got g (ctrans c hc) ++ k.down g = written g (ctrans m hs)) ∧
    accepted (ctrans m hs) ++ k.pending = conns lfd k ∧
    SUC lfd ≤ k.next
Proof
  Induct
  >- simp[run_def, net0_def, conns_def, read_def, written_def, accepted_def]
  >> simp[run_def] >> rpt gen_tac >> Cases_on ‘run lfd m c n’
  >> rename1 ‘_ = (hs0, w0)’
  >> PairCases_on ‘w0’ >> simp[world_step_def]
  >> Cases_on ‘sacts w00 (new_actions (log_of m) hs0)’
  >> Cases_on ‘cacts q (new_actions (log_of c) w01)’
  >> simp[] >> strip_tac >> gvs[ctrans_SNOC, ssnap_def, csnap_def]
  >> drule sacts_moves >> strip_tac >> drule cacts_moves >> strip_tac
  >> rpt conj_tac
  (* strings, per connection *)
  >- (gen_tac
      >> qpat_x_assum ‘∀g. k.up g = _ ∧ _’ (qspec_then ‘g’ strip_assume_tac)
      >> qpat_x_assum ‘∀g. read _ (zipr _ _) ++ _ = _ ∧ _’
           (qspec_then ‘g’ strip_assume_tac)
      >> qpat_x_assum ‘∀g. read _ (ctrans _ _) ++ _ = _ ∧ _’
           (qspec_then ‘g’ strip_assume_tac)
      >> simp[] >> conj_tac >> metis_tac[APPEND_ASSOC])
  (* connections *)
  >- (qpat_x_assum ‘k.pending = _’ SUBST1_TAC
      >> ‘accepted (ctrans m hs0) ++ accepted (zipr (new_actions (log_of m) hs0) r) ++
          q.pending = conns lfd w00’ by metis_tac[APPEND_ASSOC]
      >> REWRITE_TAC[APPEND_ASSOC] >> pop_assum SUBST1_TAC
      >> mp_tac (Q.INST [‘n1’ |-> ‘w00.next’, ‘n2’ |-> ‘k.next’] conns_extend)
      >> simp[conns_def])
  >> simp[]
QED

(* The connections handed out are distinct: `fresh` holds of every server
   run in this world, for any clients *)
Theorem fresh_kernel:
  run lfd m c n = (hs, (k, hc)) ⇒ fresh (trans m hs)
Proof
  strip_tac >> drule multi_conservation >> strip_tac
  >> simp[fresh_def, trans_ctrans, zipr_NIL_accepted]
  >> ‘ALL_DISTINCT (conns lfd k)’ by simp[conns_def, ALL_DISTINCT_GENLIST]
  >> metis_tac[ALL_DISTINCT_APPEND]
QED

(* ------------------------------------------------------------------------
   The echo server against any clients
   ------------------------------------------------------------------------ *)

(* MAIN: on every connection, everything the clients sent is accounted for,
   in order: received, queued downwards, being written back by the server
   this round, or queued upwards *)
Theorem closed_echo:
  run lfd (server lfd) c n = (hs, (k, hc)) ⇒
  ∀g. sent g (ctrans c hc) =
        got g (ctrans c hc) ++ k.down g ++
        written g (zipr (new_actions (log_of (server lfd)) hs) ([] : response list)) ++
        k.up g
Proof
  strip_tac >> gen_tac
  >> drule fresh_kernel >> strip_tac
  >> drule multi_conservation >> strip_tac
  >> drule echo_server_safety >> disch_then (qspec_then ‘g’ mp_tac)
  >> simp[trans_ctrans, zipr_NIL_read] >> strip_tac
  >> first_x_assum (qspec_then ‘g’ strip_assume_tac)
  >> qpat_x_assum ‘read _ _ ++ _ = _’ (SUBST1_TAC o SYM)
  >> qpat_x_assum ‘_ = read _ _’ (SUBST1_TAC o SYM)
  >> qpat_x_assum ‘got _ _ ++ _ = _’ (SUBST1_TAC o SYM)
  >> REWRITE_TAC[APPEND_ASSOC]
QED

(* MAIN: for any number of clients, written as one async program (e.g. a
   `both` of them): on every connection, what is received is exactly a
   prefix of what was sent, in order *)
Theorem every_client_receives_what_it_sent:
  run lfd (server lfd) c n = (hs, (k, hc)) ⇒
  ∀g. got g (ctrans c hc) ≼ sent g (ctrans c hc)
Proof
  strip_tac >> gen_tac >> drule closed_echo
  >> disch_then (qspec_then ‘g’ SUBST1_TAC)
  >> metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]
QED

(* ------------------------------------------------------------------------
   Echo clients, written with the library
   ------------------------------------------------------------------------ *)

Definition send_all_def:
  send_all g [] = return () ∧
  send_all g (l :: ls) = bind (emit (Send g l)) (λu. send_all g ls)
End

Definition creadable_def:
  creadable g = wait (λs. if CReadable g ∈ s.ready then SOME () else NONE)
End

(* Receive n strings on g; retry when nothing has arrived *)
Definition recv_n_body_def:
  recv_n_body r (g, n) =
    if n = 0 then return []
    else bind (creadable g) (λu.
         bind (emit (Recv g)) (λres.
           case res of
             Got d => map (CONS d) (r (g, n - 1))
           | _ => r (g, n)))
End

Theorem recv_n_body_contractive:
  contractive recv_n_body
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[recv_n_body_def]
  >> Cases_on ‘p1 = 0’ >> simp[guarded_const]
  >> ho_match_mp_tac guarded_bind
  >> simp[creadable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call]
  >> ho_match_mp_tac nonexpansive_map >> simp[nonexpansive_call]
QED

Definition recv_n_def:
  recv_n = fix recv_n_body
End

Theorem recv_n_unfold:
  recv_n p = recv_n_body recv_n p
Proof
  simp[recv_n_def, Once (MATCH_MP fix_unfold recv_n_body_contractive)]
QED

(* Connect, send the lines, then read the replies *)
Definition client_def:
  client ls =
    bind (emit Connect) (λr.
      case r of
        Connected g => bind (send_all g ls) (λu. recv_n (g, LENGTH ls))
      | _ => return [])
End

(* ------------------------------------------------------------------------
   Concrete run: two clients at once
   ------------------------------------------------------------------------ *)

Definition two_def:
  two = both (client ["hi"; "there"]) (client ["yo"])
End

(* Client 1 connects, sends "hi", "there"; client 2 connects, sends "yo".
   Both get their own lines back.  (EVAL takes ~12s: the model recomputes
   each computation from its whole history every round.) *)
Theorem example_two_clients:
  let (hs, (k, hc)) = run 0 (server 0) two 10 in
    (two hc).result = SOME (["hi"; "there"], ["yo"]) ∧
    (server 0 hs).actions =
      [Accept 0; Read 1; Accept 0; Write 1 "hi"; Read 2; Read 1;
       Write 2 "yo"; Write 1 "there"]
Proof
  EVAL_TAC
QED
