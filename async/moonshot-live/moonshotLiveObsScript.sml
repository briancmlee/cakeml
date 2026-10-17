(*
  Moonshot liveness: the per-program OBLIGATIONS, in system form, and the
  composition (STATEMENTS ONLY, for review).

  moonshot_served_of_obs_claim: on an infinite l0sys run of the three
  programs (client 0, proxy 1, KV 2), fair in the kernel's observed form,
  with no strangers on ports a and b, if the programs meet their
  obligations (moonshot_obs) then, unless X, every logical connection
  i < N is served (client_served, the approved conclusion).  X is any
  excuse; the headline takes X = sys_excuse.

  What is new here over chain_served (moonshotLiveServed), the data chain
  of one connection:
   - THE SETUP CHAIN.  The client names its episodes ep i (connects to a).
     The channel of an episode is the run's ghost map (run_css, the one
     behind B2's sinv).  A connect end to a port of `isolated` is
     eventually ended or paired with a process that listens on the port
     (connect_pairs_claim: kernel fairness (C), isolated); only the proxy
     listens on a and only KV on b (topology_ob).  The proxy names, for each
     front, its backend (bk: front channel -> backend channel), which is
     then paired with KV the same way.
   - THE ESCAPES.  A real client finishes: once its connection is done it
     stops asking and closes.  So each clause holds unless X or the
     connection is done (done_by: all requests sent, complete replies
     read), or unless one of the program's own chain ends is lost; and the
     joint [R3] obligation closes_ob says no chain end is lost before the
     connection is done, unless X.  The proof instantiates chain_served's X
     with X ∨ done.

  Obligations, by owner (README §6):
   - client (close-v2): client_open (episodes ep i, injective, connected to
     a) and client_conn_ob per episode (asks, sends, sends no more than
     rq, reads what arrives);
   - proxy (honest-ffi): proxy_ob (per front on a: a backend on b and the
     four relay clauses);
   - KV: kv_ob (per end accepted on b: asks once its outbox drains; answers);
   - all: topology_ob (who listens on a and b) and closes_ob ([R3]).
  Each is a fact of the run; the per-program lifts (from each program's
  own L0-trace claim, as l0sys_proj_drains does for `drains`) are separate.
*)
Theory moonshotLiveObs
Ancestors
  moonshotLiveServed moonshotLiveChain moonshotLiveStmts l0sysStep l0sysFair l0sys
  l0sysEpisodes
Libs
  preamble

(* ------------------------------------------------------------------------
   Episodes and their channels
   ------------------------------------------------------------------------ *)

(* The run's ghost: for each process, the channel of each of its episodes
   (B2's step_css, along the run) *)
Definition run_css_def:
  run_css (ss : num -> sysstate) rs 0 = (K [] : num -> num list) ∧
  run_css ss rs (SUC n) = step_css (ss n) (rs n) (run_css ss rs n)
End

(* Episode jep of process k has channel c *)
Definition ep_chan_def:
  ep_chan ss rs k jep c ⇔
    ∃n. jep < LENGTH (run_css ss rs n k) ∧ EL jep (run_css ss rs n k) = c
End

(* End e exists and has ended at n: lost (broken or closed), or it has
   seen its peer's EOF (frozen).  A program stops asking on an end it
   has read the EOF of; in the chain, every EOF follows the client's
   half-close after it is done, so closes_ob covers EOFs as well.  (lost
   alone reads a channel slot that need not exist yet: hence is_end) *)
Definition ended_def:
  ended ss e n ⇔ is_end (ss n) e ∧ frozen (sys_chan (ss n) e)
End

(* Process k has a listener on port p *)
Definition listens_on_def:
  listens_on (s : sysstate) k p ⇔ ∃l q. MEM (l, p, q) (EL k s.procs).listeners
End

(* TO PROVE (the kernel's part of the setup chain): a connect end to a port
   of `isolated`, where only k0 ever listens, is eventually lost (broken,
   e.g. by ConnFail, or closed) or paired with an end of k0 *)
Definition connect_pairs_claim_def:
  connect_pairs_claim ⇔
    ∀S ss rs ports n e p k0.
      l0sys_irun S ss rs ∧ kernel_fair_obs ss rs ∧ isolated ports ss rs ∧
      (∀n k. k < LENGTH S ∧ listens_on (ss n) k p ⇒ k = k0) ∧
      is_end (ss n) e ∧ (ss n).target e = SOME p ∧ MEM p ports ⇒
      (∃n'. ended ss e n') ∨ ∃n' j'. (ss n').peer e = SOME (k0, j')
End

(* ------------------------------------------------------------------------
   The obligations (client 0, proxy 1, KV 2)
   ------------------------------------------------------------------------ *)

(* The client's episode jep is done at n: it has sent exactly the requests
   rq and read complete replies to them *)
Definition done_by_def:
  done_by rs jep (rq : brequest list) n ⇔
    l0_ep_sent jep (ptr rs 0 n) = brequests rq ∧ served_by rs 0 jep rq n
End

Definition conn_done_def:
  conn_done X rs jep rq ⇔ X ∨ ∃n. done_by rs jep rq n
End

(* The client, per episode jep for the requests rq, on the episode's
   channel jc: it asks for input infinitely often, until done; under
   drains it sends all of rq, and never more; it reads what arrives *)
Definition client_conn_ob_def:
  client_conn_ob X ss rs jep rq ⇔
    ∀jc. ep_chan ss rs 0 jep jc ⇒
      (conn_done X rs jep rq ∨ io (asks_in ss rs 0 jc)) ∧
      (sys_drains ss (0, jc) ⇒
       conn_done X rs jep rq ∨ ∃n. brequests rq ≼ l0_ep_sent jep (ptr rs 0 n)) ∧
      (∀n. l0_ep_sent jep (ptr rs 0 n) ≼ brequests rq) ∧
      (∀m. is_end (ss m) (0, jc) ⇒
           conn_done X rs jep rq ∨ ev_ext m (dlv_at ss (0, jc)) (λn. l0_ep_recvd jep (ptr rs 0 n)))
End

(* The client opens one episode per logical connection, each a connect to
   the proxy's port a, unless X *)
Definition client_open_def:
  client_open X a N rs (ep : num -> num) ⇔
    X ∨ (∀i i'. i < N ∧ i' < N ∧ ep i = ep i' ⇒ i = i') ∧
        ∀i. i < N ⇒ ∃n. l0_ep_role (ep i) (ptr rs 0 n) = SOME (Connected a)
End

(* The proxy, per front ja with backend jb: as moonshot_chain_drains and
   chain_served ask, unless X or one of the two ends is lost *)
Definition proxy_pair_ob_def:
  proxy_pair_ob X ss rs ja jb ⇔
    let L = (X ∨ ∃n. ended ss (1, ja) n ∨ ended ss (1, jb) n) in
      (sys_drains ss (1, ja) ⇒ L ∨ io (asks_in ss rs 1 jb)) ∧
      (sys_drains ss (1, jb) ⇒ L ∨ io (asks_in ss rs 1 ja)) ∧
      ∀m. is_end (ss m) (1, ja) ∧ is_end (ss m) (1, jb) ⇒
          (sys_drains ss (1, jb) ⇒ L ∨ ev_ext m (dlv_at ss (1, ja)) (sent_at ss (1, jb))) ∧
          (sys_drains ss (1, ja) ⇒ L ∨ ev_ext m (dlv_at ss (1, jb)) (sent_at ss (1, ja)))
End

(* Every front of the proxy (an end paired with a connect to a) gets a
   backend bk ja, a connect to b, unless X or the front is lost *)
Definition proxy_ob_def:
  proxy_ob X a b ss rs (bk : num -> num option) ⇔
    ∀ja m e. (ss m).peer (1, ja) = SOME e ∧ (ss m).target e = SOME a ⇒
      X ∨ (∃n. ended ss (1, ja) n) ∨
      ∃jb. bk ja = SOME jb ∧ (∃n. is_end (ss n) (1, jb) ∧ (ss n).target (1, jb) = SOME b) ∧
           proxy_pair_ob X ss rs ja jb
End

(* KV, per end jk paired with a connect to b: asks once jk drains, and
   answers every complete request list that arrives, unless X or jk is
   lost *)
Definition kv_ob_def:
  kv_ob X b ss rs ⇔
    ∀jk m e. (ss m).peer (2, jk) = SOME e ∧ (ss m).target e = SOME b ⇒
      let L = (X ∨ ∃n. ended ss (2, jk) n) in
        (sys_drains ss (2, jk) ⇒ L ∨ io (asks_in ss rs 2 jk)) ∧
        ∀m'. is_end (ss m') (2, jk) ⇒ sys_drains ss (2, jk) ⇒ kv_answers m' L ss (2, jk)
End

(* Only the proxy listens on a, only KV on b (from the programs: each
   listens only on its own port) *)
Definition topology_ob_def:
  topology_ob a b (ss : num -> sysstate) ⇔
    ∀n k. k < 3 ⇒ (listens_on (ss n) k a ⇒ k = 1) ∧ (listens_on (ss n) k b ⇒ k = 2)
End

(* [R3], joint (OWED, pending close/shutdown): no end of episode jep's
   chain (its channel jc, the front paired with it, the front's backend
   bk ja, the backend's peer) is lost before the episode is done, unless X *)
Definition closes_ob_def:
  closes_ob X ss rs (bk : num -> num option) jep rq ⇔
    ∀jc n e. ep_chan ss rs 0 jep jc ∧
             (e = (0, jc) ∨
              ∃m ja. (ss m).peer (0, jc) = SOME (1, ja) ∧
                     (e = (1, ja) ∨
                      ∃jb. bk ja = SOME jb ∧ (e = (1, jb) ∨ ∃m'. (ss m').peer (1, jb) = SOME e))) ∧
             ended ss e n ∧ ¬done_by rs jep rq n ⇒ X
End

Definition moonshot_obs_def:
  moonshot_obs X a b N rqs ss rs ⇔
    X ∨ ∃ep bk. client_open X a N rs ep ∧ topology_ob a b ss ∧
                proxy_ob X a b ss rs bk ∧ kv_ob X b ss rs ∧
                ∀i. i < N ⇒ client_conn_ob X ss rs (ep i) (rqs i) ∧
                            closes_ob X ss rs bk (ep i) (rqs i)
End

(* ------------------------------------------------------------------------
   The composition (TO PROVE)
   ------------------------------------------------------------------------ *)

Definition moonshot_served_of_obs_claim_def:
  moonshot_served_of_obs_claim ⇔
    ∀S ss rs X a b N rqs.
      l0sys_irun S ss rs ∧ LENGTH S = 3 ∧ kernel_fair_obs ss rs ∧ isolated [a; b] ss rs ∧
      (∀i. EVERY valid_brequest (rqs i)) ∧ moonshot_obs X a b N rqs ss rs ⇒
      X ∨ client_served 0 a N rqs rs
End

(* The headline from the obligations: with the termination obligation
   ([R3], owed) as an explicit hypothesis *)
Definition moonshot_live_of_obs_claim_def:
  moonshot_live_of_obs_claim ⇔
    ∀K cprog pprog kprog.
      (∀a b c N rqs ss rs.
         moonshot_live_hyps a b c N rqs (moonshot_sys cprog pprog kprog a b c N rqs) ss rs ⇒
         moonshot_obs (sys_excuse K (moonshot_sys cprog pprog kprog a b c N rqs) ss rs)
                      a b N rqs ss rs ∧
         (sys_excuse K (moonshot_sys cprog pprog kprog a b c N rqs) ss rs ∨
          client_exits (moonshot_sys cprog pprog kprog a b c N rqs) rs 0)) ⇒
      moonshot_live K cprog pprog kprog
End
