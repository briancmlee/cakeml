(*
  The Sock/Kv vocabulary and the store wrapper, as instances of the library
  (skeletonVLive), against withStore's definitions alone.

   - sockV: the vocabulary of with_store's inner computations: socket
     actions are Sock x, queries are Kv (fd, q) (owned by fd), the world's
     responses are SockR r, the store's answers KvR b.  vocab_ok sockV.
     Its socket part is with_store's: sproj sockV = untag, sacts sockV =
     socks.
   - wrap_ok_with_store: with_store δ s0 is a wrapper for sockV, with inner
     history inner_hist δ s0.
   - with_store_v_live (MAIN): server_v_live for with_store δ s0
     (server_v sockV hf lfd).  With server_with_k = server_v sockV (next,
     on the KV base), this is KV liveness from the KV handler's
     handler_live_v.
*)
Theory skeletonVKv
Ancestors
  pair list rich_list arithmetic option words string
  asyncCore asyncLevel1 asyncTranscript echoProgress echoServer
  echoServerSafety echoSockModel loopRounds echoLiveDrain withStore
  skeletonV skeletonVProgress skeletonVLive HttpGetSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   The vocabulary
   ------------------------------------------------------------------------ *)

(* The owner of an inner action: Read and Write their fd, a query the fd it
   is tagged with *)
Definition sock_owner_def:
  sock_owner (Sock (Read fd)) = SOME fd ∧
  sock_owner (Sock (Write fd d)) = SOME fd ∧
  sock_owner (Sock (Accept l)) = NONE ∧
  sock_owner (Kv (fd, q)) = SOME (fd : num)
End

Definition sockV_def:
  sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
           ('b, echoServer$response) kres) vocab =
    <| acc := (λl. Sock (Accept l)) ; rd := (λfd. Sock (Read fd)) ;
       wr := (λfd d. Sock (Write fd d)) ; qry := Kv ;
       sact := (λa. case a of Sock x => SOME x | Kv q => NONE) ;
       rinj := SockR ;
       sres := (λr. case r of SockR y => SOME y | KvR b => NONE) ;
       kans := (λr. case r of KvR b => SOME b | SockR y => NONE) ;
       owner := sock_owner |>
End

Theorem vocab_ok_sockV:
  vocab_ok sockV
Proof
  rw[vocab_ok_def, sockV_def, sock_owner_def] >>
  every_case_tac >> gvs[]
QED

(* Queries are not socket actions *)
Theorem vocab_qok_sockV:
  vocab_qok sockV
Proof
  simp[vocab_qok_def, sockV_def]
QED

(* An entry belongs to fd if its action does (any answer type) *)
Theorem on_fd_v_sockV:
  on_fd_v sockV fd = (λp. sock_owner (FST p) = SOME fd)
Proof
  simp[FUN_EQ_THM, on_fd_v_def, sockV_def]
QED

(* The socket part through sockV is with_store's *)
Theorem sproj_sockV:
  ∀tr. sproj sockV tr = untag tr
Proof
  Induct >> simp[untag_def] >> PairCases >> Cases_on ‘h0’ >>
  simp[sockV_def] >> fs[untag_def, sockV_def] >>
  Cases_on ‘h1’ >> simp[] >> Cases_on ‘x’ >> simp[]
QED

Theorem sacts_sockV:
  ∀acts. sacts sockV acts = socks acts
Proof
  Induct >> simp[socks_def] >> Cases >> simp[sockV_def] >> fs[socks_def]
QED

(* ------------------------------------------------------------------------
   The wrapper
   ------------------------------------------------------------------------ *)

Theorem LENGTH_merge_full[local]:
  ∀acts rs ans.
    LENGTH (socks acts) ≤ LENGTH rs ∧ LENGTH (queries acts) ≤ LENGTH ans ⇒
    LENGTH acts ≤ LENGTH (merge acts rs ans)
Proof
  Induct >> simp[merge_def] >> Cases >> rpt gen_tac >> simp[merge_def]
  >- (Cases_on ‘rs’ >> simp[])
  >> Cases_on ‘ans’ >> simp[]
QED

(* If the world answers with_store δ s0 m promptly, m is answered promptly
   on the inner history: the world answers its socket actions, the store
   its queries.  (withStoreStep's prompt_with_store; restated here
   because that file does not build on the current KV tip.) *)
Theorem prompt_inner_hist:
  wf m ∧ prompt (with_store δ s0 m) h ⇒ prompt m (inner_hist δ s0 m h)
Proof
  rw[prompt_def] >> first_x_assum drule >>
  simp[new_actions_with_store, inner_hist_TAKE, responses_at_def] >>
  simp[EL_inner_hist] >> strip_tac >>
  ‘∃old. (m (TAKE i (inner_hist δ s0 m h))).actions =
         old ++ new_actions (log_of m) (TAKE i (inner_hist δ s0 m h))’
    by simp[log_new_actions] >>
  pop_assum SUBST1_TAC >>
  irule LENGTH_merge_full >> simp[LENGTH_store_answers]
QED

(* The inner history has the outer one's ready sets *)
Theorem inner_hist_ready:
  ∀h i. i < LENGTH h ⇒ (EL i (inner_hist δ s0 m h)).ready = (EL i h).ready
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, inner_hist_SNOC] >>
  rpt strip_tac >> Cases_on ‘i < LENGTH h’
  >- simp[EL_APPEND1]
  >> ‘i = LENGTH h’ by simp[] >> simp[EL_APPEND2]
QED

(* MAIN: with_store δ s0 is a wrapper for sockV *)
Theorem wrap_ok_with_store:
  wrap_ok sockV (with_store δ s0) (inner_hist δ s0)
Proof
  rw[wrap_ok_def]
  >- simp[wf_with_store]
  >- simp[with_store_def, sacts_sockV]
  >- simp[trans_with_store, sproj_sockV]
  >- metis_tac[prompt_inner_hist]
  >- simp[inner_hist_ready]
  >> simp[inner_hist_TAKE]
QED

(* ------------------------------------------------------------------------
   Liveness
   ------------------------------------------------------------------------ *)

(* MAIN: the skeleton over the Sock/Kv vocabulary, run with a store: if
   every handler meets handler_live_v sockV, every connection's owed output
   is eventually written (server_v_live for sockV and with_store) *)
Theorem with_store_v_live:
  hokv sockV (hf : num -> ((echoServer$action, num # 'kq) kact,
                           ('kb, echoServer$response) kres, 'kz) vmach) ∧
  handler_live_v sockV hf out B ∧ FLAT (out "") = "" ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ HttpGetSpec$bytes D ≼ sent_upto c n s0 ⇒
  ∃N. HttpGetSpec$bytes (FLAT (out D)) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (EI lfdn)
                          (srelabel (with_store δ st0 (server_v sockV hf lfdn))) s0) N))
Proof
  strip_tac >>
  qspecl_then [‘sockV’, ‘with_store δ st0’, ‘inner_hist δ st0’, ‘hf’, ‘out’, ‘B’, ‘D’,
               ‘s0’, ‘lfdn’, ‘c’, ‘n’] mp_tac
    (Q.GENL [‘V’, ‘Wr’, ‘inner’, ‘hf’, ‘out’, ‘B’, ‘D’, ‘s0’, ‘lfdn’, ‘c’, ‘n’]
       server_v_live) >>
  impl_tac
  >- (simp[vocab_ok_sockV, wrap_ok_with_store] >>
      (* the two sockV instances differ only in the (unused) answer type *)
      qpat_x_assum ‘hokv _ _’ mp_tac >> simp[hokv_def, on_fd_v_sockV]) >>
  simp[]
QED
