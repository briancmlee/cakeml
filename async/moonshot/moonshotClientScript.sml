(*
  The moonshot's client (design/45 §2.5, step 10), as a computation on the
  endpoint handle layer, and its proof (client_hl_claim).

  N logical connections to address a.  Connection i:
   - CIdle: connect (unless the client has used cbound handles);
   - CPend hd: its connect is pending; when the layer reports hd ready
     (the settle report), read it: refused (ERefused): back to CIdle, to
     retry; otherwise up: CUp, with all of rqs i to send;
   - CUp hd rest: write rest (the world takes what it takes), and read hd
     whenever it is ready (the client is a sink); EOF: CDone (a break
     reads as an EOF: not retried, bytes may have been sent);
   - CDone.
  A connect with no socket (EConnected NONE): back to CIdle.  The client
  finishes when every connection is CDone.

  The computation is a fold over the history: each snapshot's results
  update the state (paired with the previous round's actions), and the
  state and the snapshot's ready handles give the next round's actions.
*)
Theory moonshotClient
Ancestors
  moonshotClientSpec endpointHLModel endpointWorld HttpSpec HttpSpecBodies
  asyncLevel1 asyncCore asyncHLModel socketV2FFI honestL1Steps
Libs
  preamble

Datatype:
  cconn = CIdle | CPend word64 | CUp word64 (word8 list) | CDone
End

Datatype:
  cst = <| cs : cconn list               (* connection i's state *)
         ; last : (num # eact) list       (* the last round's actions, with their connection *)
         ; nh : num                       (* handles received so far *)
         ; hlc : (word64 # num) list |>   (* each handle's connection *)
End

Definition cread_def:
  cread = 4096n
End

(* Connection c's round actions, with nh handles used and the ready
   handles rdy *)
Definition cact1_def:
  cact1 a nh c (rdy : word64 set) =
    case c of
    | CIdle => if nh < cbound then [EConnect a] else []
    | CPend hd => if hd ∈ rdy then [ERead hd cread] else []
    | CUp hd rest =>
        (if rest ≠ [] then [EWrite hd rest] else []) ++
        (if hd ∈ rdy then [ERead hd cread] else [])
    | CDone => []
End

(* Round actions from state st, with the ready handles rdy, each with its
   connection *)
Definition cacts_def:
  cacts a st (rdy : word64 set) =
    FLAT (GENLIST (λi. MAP (λx. (i, x)) (cact1 a st.nh (EL i st.cs) rdy)) (LENGTH st.cs))
End

(* One result r of action x, for a connection in state c with requests b *)
Definition cres_def:
  cres (b : word8 list) c x r =
    case (x, r) of
    | (EConnect _, EConnected NONE) => CIdle
    | (EConnect _, EConnected (SOME hd)) => CPend hd
    | (ERead _ _, ERefused) => CIdle
    | (ERead _ _, EGot (SOME [])) => CDone
    | (ERead hd _, EGot _) => (case c of CPend _ => CUp hd b | _ => c)
    | (EWrite _ _, EWrote k) => (case c of CUp hd rest => CUp hd (DROP k rest) | _ => c)
    | _ => c
End

Definition new_hd_def:
  new_hd (EConnected (SOME hd)) = SOME hd ∧
  new_hd _ = NONE
End

(* The results of the last round's actions, in order *)
Definition cupd_def:
  cupd rqs st [] rs = st ∧
  cupd rqs st _ [] = st ∧
  cupd rqs st ((i, x) :: xs) (r :: rs) =
    cupd rqs (st with <| cs := LUPDATE (cres (brequests (rqs i)) (EL i st.cs) x r) i st.cs;
                         nh := st.nh + (if new_hd r = NONE then 0 else 1);
                         hlc := (case new_hd r of SOME hd => [(hd, i)] | NONE => []) ++ st.hlc |>)
         xs rs
End

Definition cinit_def:
  cinit a N =
    let st = <| cs := REPLICATE N CIdle; last := []; nh := 0; hlc := [] |> in
      st with last := cacts a st ∅
End

Definition cstep_def:
  cstep a rqs st (s : (word64, eresp) snapshot) =
    let st1 = cupd rqs st st.last s.results in st1 with last := cacts a st1 s.ready
End

Definition cstate_def:
  cstate a N rqs h = FOLDL (cstep a rqs) (cinit a N) h
End

Definition call_done_def:
  call_done st ⇔ EVERY (λc. c = CDone) st.cs
End

(* The computation: every round's actions so far; finished when all done *)
Definition cprog_def:
  cprog a N rqs (h : (word64, eresp) snapshot list) =
    <| actions := FLAT (GENLIST (λk. MAP SND (cstate a N rqs (TAKE k h)).last) (SUC (LENGTH h)));
       result := if call_done (cstate a N rqs h) then SOME () else NONE |>
End

(* The interest: the open handles *)
Definition chd_def:
  chd (CPend hd) = [hd] ∧
  chd (CUp hd rest) = [hd] ∧
  chd _ = []
End

Definition cifds_def:
  cifds a N rqs h = FLAT (MAP chd (cstate a N rqs h).cs)
End

(* ------------------------------------------------------------------------
   The computation's rounds
   ------------------------------------------------------------------------ *)

Theorem cstate_SNOC:
  cstate a N rqs (h ++ [s]) = cstep a rqs (cstate a N rqs h) s
Proof
  simp[cstate_def, FOLDL_APPEND]
QED

Theorem cprog_actions_SNOC:
  (cprog a N rqs (h ++ [s])).actions =
  (cprog a N rqs h).actions ++ MAP SND (cstate a N rqs (h ++ [s])).last
Proof
  simp[cprog_def] >>
  ‘SUC (LENGTH h + 1) = SUC (SUC (LENGTH h))’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC [GENLIST] >>
  ‘GENLIST (λk. MAP SND (cstate a N rqs (TAKE k (h ++ [s]))).last) (LENGTH h) =
   GENLIST (λk. MAP SND (cstate a N rqs (TAKE k h)).last) (LENGTH h)’
    by (irule GENLIST_CONG >> rw[] >> simp[TAKE_APPEND1]) >>
  pop_assum SUBST1_TAC >>
  simp[SNOC_APPEND, FLAT_APPEND, TAKE_LENGTH_ID_rwt, TAKE_APPEND1]
QED

(* The round polled with h emits the state's last actions *)
Theorem cprog_new_actions:
  new_actions (log_of (cprog a N rqs)) h = MAP SND (cstate a N rqs h).last
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_def, log_of_def, cprog_def, cstate_def] >>
  simp[new_actions_def, log_of_def, SNOC_APPEND, FRONT_APPEND, cprog_actions_SNOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

(* ------------------------------------------------------------------------
   The handle layer's operations on an open handle
   ------------------------------------------------------------------------ *)

(* w' is w but for channel j (and maybe the open fds) *)
Definition wframe_def:
  wframe j (w : eworld) w' ⇔
    LENGTH w'.chans = LENGTH w.chans ∧ (∀j'. j' ≠ j ⇒ EL j' w'.chans = EL j' w.chans) ∧
    w'.listening = w.listening ∧ w'.reserved = w.reserved ∧ w'.alloc = w.alloc ∧
    w'.takes = w.takes ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist ∧
    w'.nosock = w.nosock ∧ w'.nconnects = w.nconnects ∧ w'.calls = w.calls
End

Theorem ehdo_read:
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
  0 < n ∧ n < 256 ** 8 ⇒
  ∃r w' hs'. ehdo lfd (w, hs) (ERead hd n) = SOME (r, (w', hs')) ∧ wframe j w w' ∧
   ((EL j w.chans).status = Refused ∧ r = ERefused ∧ hs' = eh_del hd hs ∧
    w'.open_fds = ADELKEY f w.open_fds ∧ (EL j w'.chans).status = Failed ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox ≠ [] ∧
    r = EGot (SOME (TAKE n (EL j w.chans).inbox)) ∧ hs' = hs ∧ w'.open_fds = w.open_fds ∧
    EL j w'.chans = EL j w.chans with inbox := DROP n (EL j w.chans).inbox ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox = [] ∧
    ((EL j w.chans).peer_eof ∨ (EL j w.chans).status = Failed) ∧
    r = EGot (SOME []) ∧ hs' = eh_del hd hs ∧ w'.open_fds = ADELKEY f w.open_fds ∧
    (EL j w'.chans).status = (EL j w.chans).status ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox = [] ∧
    ¬(EL j w.chans).peer_eof ∧ (EL j w.chans).status ≠ Failed ∧
    r = EGot NONE ∧ hs' = hs ∧ w' = w)
Proof
  strip_tac >>
  simp[ehdo_def, ep_conn_err_def, ep_read_def, ep_chan_of_def, ep_close_def, upd_chan_def] >>
  rw[] >>
  TRY (‘∃t ts. TAKE n (EL j w.chans).inbox = t :: ts’
         by (Cases_on ‘(EL j w.chans).inbox’ >> gvs[] >> Cases_on ‘n’ >> gvs[]) >>
       pop_assum (fn th => simp[th] >> assume_tac th)) >>
  simp[wframe_def, EL_LUPDATE] >> rw[] >> gvs[ALOOKUP_ADELKEY]
QED

Theorem ehdo_write_up:
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
  (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧ w.takes = (λj b n. n) ⇒
  ehdo lfd (w, hs) (EWrite hd bs) =
    SOME (EWrote (LENGTH bs),
          (upd_chan j (λc. c with <| sent := c.sent ++ bs; inflight := c.inflight + LENGTH bs |>) w,
           hs))
Proof
  strip_tac >> simp[ehdo_def, chan_status_def, ep_chan_of_def, ep_send_def]
QED

Theorem ehdo_connect:
  ehdo lfd (w, hs) (EConnect a) =
    if w.nosock w.nconnects ∨ ¬(LENGTH (ep_used w) < dimword (:64)) then
      SOME (EConnected NONE, (w with nconnects := w.nconnects + 1, hs))
    else if hdln (w2n lfd) hs.nxt < dimword (:64) then
      SOME (EConnected (SOME (hdl lfd hs.nxt)),
            (w with <| chans := w.chans ++ [new_chan (SOME a) Connecting];
                       open_fds := (w.alloc (LENGTH w.chans) (ep_used w), LENGTH w.chans) :: w.open_fds;
                       nconnects := w.nconnects + 1 |>,
             eh_new lfd (w.alloc (LENGTH w.chans) (ep_used w)) hs with
               settling := hdl lfd hs.nxt :: hs.settling))
    else NONE
Proof
  simp[ehdo_def, ep_connect_def, ep_alloc_def] >>
  ‘∀X n. ep_used (w with <| chans := X; nconnects := n |>) = ep_used w’ by simp[ep_used_def] >>
  rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The history's pairs, round by round
   ------------------------------------------------------------------------ *)

Theorem hl_pairs_SNOC:
  hl_pairs m (h ++ [s]) = hl_pairs m h ++ ZIP (new_actions (log_of m) h, s.results)
Proof
  simp[hl_pairs_def] >>
  ‘LENGTH h + 1 = SUC (LENGTH h)’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC [GENLIST] >>
  ‘GENLIST (λk. ZIP (new_actions (log_of m) (TAKE k (h ++ [s])), (EL k (h ++ [s])).results))
           (LENGTH h) =
   GENLIST (λk. ZIP (new_actions (log_of m) (TAKE k h), (EL k h).results)) (LENGTH h)’
    by (irule GENLIST_CONG >> rw[] >> simp[TAKE_APPEND1, EL_APPEND1]) >>
  pop_assum SUBST1_TAC >>
  simp[SNOC_APPEND, FLAT_APPEND, TAKE_LENGTH_APPEND, EL_APPEND2]
QED

Theorem hl_APPEND[simp]:
  hl_sent hd (ps1 ++ ps2) = hl_sent hd ps1 ++ hl_sent hd ps2 ∧
  hl_read hd (ps1 ++ ps2) = hl_read hd ps1 ++ hl_read hd ps2 ∧
  hl_connects (ps1 ++ ps2) = hl_connects ps1 ++ hl_connects ps2 ∧
  hl_conn_handles (ps1 ++ ps2) = hl_conn_handles ps1 ++ hl_conn_handles ps2 ∧
  (hl_eof hd (ps1 ++ ps2) ⇔ hl_eof hd ps1 ∨ hl_eof hd ps2) ∧
  (hl_refused hd (ps1 ++ ps2) ⇔ hl_refused hd ps1 ∨ hl_refused hd ps2)
Proof
  simp[hl_sent_def, hl_read_def, hl_connects_def, hl_conn_handles_def, hl_eof_def,
       hl_refused_def] >> metis_tac[]
QED

Theorem hl_NIL[simp]:
  hl_sent hd [] = [] ∧ hl_read hd [] = [] ∧ hl_connects [] = [] ∧
  hl_conn_handles [] = [] ∧ ¬hl_eof hd [] ∧ ¬hl_refused hd []
Proof
  simp[hl_sent_def, hl_read_def, hl_connects_def, hl_conn_handles_def, hl_eof_def,
       hl_refused_def]
QED

(* ------------------------------------------------------------------------
   The client's state and the layer's: the relation
   ------------------------------------------------------------------------ *)

(* Connection i in state c, its channel ch; sett: its connect is unreported
   (settling); rd: reported ready, to be read this round; sent: the bytes
   the history says it wrote *)
Definition cok_def:
  cok (b : word8 list) c (ch : chan) sett rd sent ⇔
    case c of
    | CPend hd =>
        ch.sent = [] ∧ sent = [] ∧ ¬ch.shut ∧
        (ch.status = Connecting ∧ ch.inbox = [] ∧ ¬ch.peer_eof ∧ sett ∧ ¬rd ∨
         (ch.status = Up ∨ ch.status = Refused) ∧ (sett ∨ rd))
    | CUp hd rest => ch.status = Up ∧ ¬ch.shut ∧ ch.sent ++ rest = b ∧ sent = ch.sent
    | _ => T
End

(* rdyf i: the ready handles connection i's next actions see *)
Definition crel_def:
  crel a N rqs lfd st (rdyf : num -> word64 set) ps (w : eworld) hs ⇔
    LENGTH st.cs = N ∧ st.nh = hs.nxt ∧
    w.takes = (λj b n. n) ∧ alloc_ok w.alloc ∧
    LENGTH w.reserved + LENGTH w.listening ≤ 1 ∧
    ALL_DISTINCT (MAP FST hs.tbl) ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧
    ALL_DISTINCT (MAP FST w.open_fds) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
    EVERY (λj. j < LENGTH w.chans) (MAP SND w.open_fds) ∧
    (∀f. MEM f (MAP FST w.open_fds) ⇒ ¬MEM f (MAP FST w.listening)) ∧
    (∀f. MEM f (MAP FST w.open_fds) ⇔ MEM f (MAP SND hs.tbl)) ∧
    (* the open handles: the connections', one each *)
    (∀hd. MEM hd (MAP FST hs.tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i st.cs))) ∧
    (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 st.cs)) ∧ MEM hd (chd (EL i2 st.cs)) ⇒
                i1 = i2) ∧
    (∀i hd. i < N ∧ MEM hd (chd (EL i st.cs)) ⇒
            ∃f j. ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧
                  ALOOKUP st.hlc hd = SOME i ∧
                  cok (brequests (rqs i)) (EL i st.cs) (EL j w.chans) (MEM hd hs.settling)
                      (hd ∈ rdyf i) (hl_sent hd ps)) ∧
    (* every handle issued is a connect handle of the history, below nxt *)
    (∀hd. MEM hd (MAP FST st.hlc) ⇔ MEM hd (hl_conn_handles ps)) ∧
    ALL_DISTINCT (MAP FST st.hlc) ∧
    (∀hd. MEM hd (MAP FST st.hlc) ⇒ ∃k. k < hs.nxt ∧ hd = hdl lfd k) ∧
    LENGTH st.hlc = hs.nxt ∧
    (* what was sent, per handle *)
    (∀hd. hl_sent hd ps ≠ [] ⇒ MEM hd (MAP FST st.hlc)) ∧
    (∀hd i. ALOOKUP st.hlc hd = SOME i ⇒ i < N ∧ hl_sent hd ps ≼ brequests (rqs i)) ∧
    (∀hd hd' i. ALOOKUP st.hlc hd = SOME i ∧ ALOOKUP st.hlc hd' = SOME i ∧
                hl_sent hd ps ≠ [] ∧ hl_sent hd' ps ≠ [] ⇒ hd = hd') ∧
    (∀i hd'. i < N ∧ (EL i st.cs = CIdle ∨ ∃hd. EL i st.cs = CPend hd) ∧
             ALOOKUP st.hlc hd' = SOME i ⇒ hl_sent hd' ps = []) ∧
    (∀i hd rest hd'. i < N ∧ EL i st.cs = CUp hd rest ∧ ALOOKUP st.hlc hd' = SOME i ∧
                     hl_sent hd' ps ≠ [] ⇒ hd' = hd) ∧
    (* a refused or ended handle is closed for good *)
    (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST st.hlc)) ∧
    (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ¬MEM hd (MAP FST hs.tbl)) ∧
    (∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps)) ∧
    (∀hd. (hl_refused hd ps ∨ hl_eof hd ps) ⇒ ∀i. i < N ⇒ ¬MEM hd (chd (EL i st.cs)))
End

(* ------------------------------------------------------------------------
   One connection's actions keep the relation
   ------------------------------------------------------------------------ *)

(* What an action leaves of the world *)
Definition wkeep_def:
  wkeep (w : eworld) w' ⇔
    w'.listening = w.listening ∧ w'.reserved = w.reserved ∧ w'.alloc = w.alloc ∧
    w'.takes = w.takes ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist ∧
    w'.nosock = w.nosock ∧ w'.calls = w.calls ∧ LENGTH w.chans ≤ LENGTH w'.chans ∧
    ∀j. j < LENGTH w.chans ⇒ (EL j w'.chans).status = (EL j w.chans).status ∨
                             (EL j w.chans).status = Refused ∧ (EL j w'.chans).status = Failed
End

Theorem wkeep_refl[simp]:
  wkeep w w
Proof
  simp[wkeep_def]
QED

Theorem cupd_one[simp]:
  cupd rqs st [(k, x)] [r] =
    st with <| cs := LUPDATE (cres (brequests (rqs k)) (EL k st.cs) x r) k st.cs;
               nh := st.nh + (if new_hd r = NONE then 0 else 1);
               hlc := (case new_hd r of SOME hd => [(hd, k)] | NONE => []) ++ st.hlc |>
Proof
  simp[cupd_def]
QED

Theorem chd_LUPDATE:
  i < LENGTH cs ⇒ (MEM hd (chd (EL i (LUPDATE c k cs))) ⇔
                   if i = k then MEM hd (chd c) else MEM hd (chd (EL i cs)))
Proof
  rw[EL_LUPDATE]
QED

Theorem hl_one[simp]:
  hl_sent hd [(x, r)] =
    (case (x, r) of (EWrite h' bs, EWrote k) => if h' = hd then TAKE k bs else [] | _ => []) ∧
  hl_read hd [(x, r)] =
    (case (x, r) of (ERead h' n, EGot (SOME d)) => if h' = hd then d else [] | _ => []) ∧
  hl_conn_handles [(x, r)] =
    (case x of EConnect p => (case r of EConnected (SOME h') => [h'] | _ => []) | _ => []) ∧
  (hl_eof hd [(x, r)] ⇔ ∃n. x = ERead hd n ∧ r = EGot (SOME [])) ∧
  (hl_refused hd [(x, r)] ⇔ ∃n. x = ERead hd n ∧ r = ERefused)
Proof
  simp[hl_sent_def, hl_read_def, hl_conn_handles_def, hl_connects_def, hl_eof_def,
       hl_refused_def] >>
  Cases_on ‘x’ >> Cases_on ‘r’ >> simp[] >> TRY (rename1 ‘EConnected oh’ >> Cases_on ‘oh’) >>
  simp[] >> metis_tac[]
QED

(* The ready sets matter only for the open handles *)
Theorem crel_rdyf:
  crel a N rqs lfd st rdyf ps w hs ∧
  (∀i hd. i < N ∧ MEM hd (chd (EL i st.cs)) ⇒ (hd ∈ rdyf' i ⇔ hd ∈ rdyf i)) ⇒
  crel a N rqs lfd st rdyf' ps w hs
Proof
  simp[crel_def] >> rpt strip_tac >> fs[] >> TRY (metis_tac[] >> NO_TAC) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd _ ⇒ ∃f j. _’ drule_all >> strip_tac >>
  qexistsl_tac [‘f’, ‘j’] >> simp[] >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd _ ⇒ (_ ⇔ _)’ drule_all >> simp[]
QED

(* A connect that got no socket changes nothing the relation sees *)
Theorem crel_nosock:
  crel a N rqs lfd st rdyf ps w hs ⇒
  crel a N rqs lfd st rdyf (ps ++ [(EConnect p, EConnected NONE)]) (w with nconnects := n) hs
Proof
  simp[crel_def] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem crel_connect:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CIdle ∧
  hs.nxt + 2 < dimword (:64) ∧ N < dimword (:64) ⇒
  ∃r w1 hs1. ehdo lfd (w, hs) (EConnect a) = SOME (r, (w1, hs1)) ∧
     crel a N rqs lfd (cupd rqs st [(k, EConnect a)] [r]) ((k =+ ∅) rdyf) (ps ++ [(EConnect a, r)])
       w1 hs1 ∧
     wkeep w w1
Proof
  strip_tac >> ‘LENGTH st.cs = N’ by fs[crel_def] >> simp[ehdo_connect] >>
  IF_CASES_TAC
  >- (simp[cres_def, new_hd_def] >>
      ‘LUPDATE CIdle k st.cs = st.cs’
        by (qpat_x_assum ‘EL k st.cs = CIdle’ (SUBST1_TAC o SYM) >> irule LUPDATE_SAME >> simp[]) >>
      simp[wkeep_def] >>
      ‘st with <| cs := st.cs; nh := st.nh; hlc := st.hlc |> = st’
        by simp[theorem "cst_component_equality"] >>
      simp[] >> irule crel_rdyf >> qexists_tac ‘rdyf’ >>
      conj_tac >> TRY (irule crel_nosock >> first_assum ACCEPT_TAC >> NO_TAC) >>
      rw[combinTheory.APPLY_UPDATE_THM] >> gvs[chd_def]) >>
  ‘hdln (w2n lfd) hs.nxt < 18446744073709551616’
    by (‘hdln (w2n lfd) hs.nxt ≤ hs.nxt + 1’ by rw[hdln_def] >> fs[]) >>
  ‘hdln (w2n lfd) hs.nxt < dimword (:64)’ by simp[] >>
  qpat_assum ‘hdln _ _ < 18446744073709551616’
    (fn th => simp[th, cres_def, new_hd_def, eh_new_def]) >>
  qabbrev_tac ‘f = w.alloc (LENGTH w.chans) (ep_used w)’ >>
  qabbrev_tac ‘hd = hdl lfd hs.nxt’ >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  ‘¬MEM f (ep_used w)’ by (fs[alloc_ok_def, Abbr ‘f’]) >>
  ‘¬MEM f (MAP FST w.open_fds) ∧ ¬MEM f (MAP FST w.listening)’ by fs[ep_used_def] >>
  ‘¬MEM f (MAP SND hs.tbl)’
    by (qpat_x_assum ‘∀f. MEM f (MAP FST w.open_fds) ⇔ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
  ‘∀k'. k' < hs.nxt ⇒ hdl lfd k' ≠ hd’
    by (rw[Abbr ‘hd’] >> irule hdl_fresh >> simp[]) >>
  ‘¬MEM hd (MAP FST st.hlc)’
    by (strip_tac >> qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇒ ∃k. _’ drule >>
        strip_tac >> qpat_x_assum ‘∀k'. k' < hs.nxt ⇒ _’ drule >> simp[]) >>
  ‘∀i. i < N ⇒ ¬MEM hd (chd (EL i st.cs))’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ _’ drule_all >> strip_tac >>
        imp_res_tac ALOOKUP_MEM >>
        ‘MEM hd (MAP FST st.hlc)’
          by (qpat_x_assum ‘ALOOKUP st.hlc hd = SOME i’ mp_tac >> rpt (pop_assum kall_tac) >>
              rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
        qpat_x_assum ‘¬MEM hd (MAP FST st.hlc)’ mp_tac >>
        pop_assum (fn th => REWRITE_TAC [th])) >>
  ‘¬MEM hd (MAP FST hs.tbl)’
    by (qpat_x_assum ‘∀hd. MEM hd (MAP FST hs.tbl) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘∀i. i < N ⇒ ¬MEM hd _’ mp_tac >> rpt (pop_assum kall_tac) >>
        metis_tac[]) >>
  reverse conj_tac
  >- (simp[wkeep_def, EL_APPEND1]) >>
  ‘hl_sent hd ps = []’
    by (CCONTR_TAC >> qpat_x_assum ‘∀hd. hl_sent hd ps ≠ [] ⇒ _’ drule >>
        qpat_x_assum ‘¬MEM hd (MAP FST st.hlc)’ mp_tac >> simp[]) >>
  ‘¬hl_refused hd ps ∧ ¬hl_eof hd ps’
    by (conj_tac >> strip_tac >>
        qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST st.hlc)’
          (qspec_then ‘hd’ mp_tac) >>
        qpat_x_assum ‘¬MEM hd (MAP FST st.hlc)’ mp_tac >> simp[]) >>
  ‘∀x. hl_refused x ps ∨ hl_eof x ps ⇒ x ≠ hd’
    by (rpt strip_tac >> qpat_x_assum ‘x = hd’ SUBST_ALL_TAC >> fs[]) >>
  simp[crel_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC)
  (* 1 the new channel's index is new *)
  >- (strip_tac >>
      qpat_x_assum ‘EVERY _ (MAP SND w.open_fds)’ (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> simp[])
  (* 2 *)
  >- (qpat_x_assum ‘EVERY _ (MAP SND w.open_fds)’ mp_tac >> simp[EVERY_MEM] >>
      rpt strip_tac >> first_x_assum drule >> simp[])
  (* 2b no listener's fd *)
  >- (rpt strip_tac >> gvs[] >> res_tac)
  (* 3 the open handles *)
  >- (gen_tac >> simp[EL_LUPDATE] >> eq_tac
      >- (strip_tac
          >- (qexists_tac ‘k’ >> simp[chd_def]) >>
          qexists_tac ‘i’ >> Cases_on ‘i = k’ >> gvs[chd_def]) >>
      strip_tac >> Cases_on ‘i = k’ >> gvs[chd_def] >> disj2_tac >>
      qexists_tac ‘i’ >> simp[])
  (* 4 one owner *)
  >- (rpt gen_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[chd_def] >>
      TRY (qpat_x_assum ‘∀i. i < N ⇒ ¬MEM hd _’ drule >> simp[] >> NO_TAC) >>
      qpat_x_assum ‘∀i1 i2 hd. _ ⇒ i1 = i2’ irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac ‘hd'’ >>
      conj_tac >> first_assum ACCEPT_TAC)
  (* 5 each connection's handle *)
  >- (rpt gen_tac >> strip_tac >> Cases_on ‘i = k’
      >- (gvs[EL_LUPDATE, chd_def] >>
          simp[cok_def, EL_LENGTH_APPEND, new_chan_def, combinTheory.APPLY_UPDATE_THM]) >>
      gvs[EL_LUPDATE, combinTheory.APPLY_UPDATE_THM] >>
      ‘hd' ≠ hd’ by (strip_tac >> gvs[] >> qpat_x_assum ‘∀i. i < N ⇒ ¬MEM hd _’ drule >> simp[]) >>
      qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
      ‘f' ≠ f’ by (strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
                   qpat_x_assum ‘¬MEM f (MAP SND hs.tbl)’ mp_tac >> simp[MEM_MAP, EXISTS_PROD] >>
                   metis_tac[]) >>
      ‘j < LENGTH w.chans’ by (imp_res_tac ALOOKUP_MEM >>
                               qpat_x_assum ‘EVERY _ (MAP SND w.open_fds)’ mp_tac >>
                               simp[EVERY_MEM, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      simp[EL_APPEND1])
  (* 6 *)
  >- (gen_tac >> eq_tac >> rw[] >> simp[])
  (* 7 issued below nxt *)
  >- (rw[] >- (qexists_tac ‘hs.nxt’ >> simp[]) >>
      qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇒ ∃k. _’ (qspec_then ‘hd'’ mp_tac) >>
      simp[] >> strip_tac >> qexists_tac ‘k'’ >> simp[])
  (* 8 prefixes *)
  >- (rpt gen_tac >> IF_CASES_TAC >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀hd i. ALOOKUP st.hlc hd = SOME i ⇒ _’ drule >> simp[])
  (* 9 one sending handle per connection *)
  >- (rpt gen_tac >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀hd hd' i. _ ⇒ hd = hd'’ irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac ‘i’ >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  (* 10 idle or pending: nothing sent *)
  >- (rpt gen_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀i hd'. i < N ∧ (_ ∨ _) ∧ _ ⇒ _’ irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac ‘i’ >> simp[])
  (* 11 up: only its handle sent *)
  >- (rpt gen_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀i hd rest hd'. _ ⇒ hd' = hd’ irule >> simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexistsl_tac [‘i’, ‘rest’] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  (* 12 refused or ended: a connect handle *)
  >- (gen_tac >> disch_tac >> disj2_tac >>
      qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇔ _’ (fn th => REWRITE_TAC [GSYM th]) >>
      qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST st.hlc)’ irule >>
      first_assum ACCEPT_TAC)
  (* 13 refused or ended: not open *)
  >- (gen_tac >> disch_tac >> conj_tac
      >- (qpat_x_assum ‘∀x. _ ⇒ x ≠ hd’ irule >> first_assum ACCEPT_TAC) >>
      gen_tac >> Cases_on ‘i < N’ >> simp[] >>
      qpat_x_assum ‘∀hd. _ ⇒ ∀i. i < N ⇒ ¬MEM hd _’ drule >> disch_then drule >> simp[])
  (* 14 *)
  >- (gen_tac >> qpat_x_assum ‘∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps)’ (qspec_then ‘hd'’ mp_tac) >>
      simp[])
  (* 15 refused or ended: no connection's *)
  >> gen_tac >> disch_tac >> gen_tac >> strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC
  >- (simp[chd_def] >> qpat_x_assum ‘∀x. _ ⇒ x ≠ hd’ irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘∀hd. _ ⇒ ∀i. i < N ⇒ ¬MEM hd _’ drule >> disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   Closing a connection's handle (refused, or EOF) keeps the relation
   ------------------------------------------------------------------------ *)

Theorem MAP_FST_ADELKEY:
  MAP FST (ADELKEY k l) = FILTER (λx. x ≠ k) (MAP FST l)
Proof
  simp[ADELKEY_def, FILTER_MAP, combinTheory.o_DEF]
QED

Theorem ALL_DISTINCT_MAP_FILTER:
  ∀l. ALL_DISTINCT (MAP f l) ⇒ ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem MEM_SND_ADELKEY:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ ALL_DISTINCT (MAP FST l) ∧ ALOOKUP l k = SOME v ⇒
      (MEM x (MAP SND (ADELKEY k l)) ⇔ MEM x (MAP SND l) ∧ x ≠ v)
Proof
  Induct >> simp[FORALL_PROD] >> rpt gen_tac >> rename1 ‘(k0, v0) :: l’ >> strip_tac >>
  simp[ADELKEY_def] >> Cases_on ‘k0 = k’ >> gvs[]
  >- (‘FILTER (λp. FST p ≠ k) l = l’
        by (simp[FILTER_EQ_ID, EVERY_MEM] >> gvs[MEM_MAP] >> metis_tac[FST]) >>
      simp[] >> metis_tac[]) >>
  ‘MEM v (MAP SND l)’ by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
  ‘v0 ≠ v’ by metis_tac[] >>
  gvs[ADELKEY_def] >> metis_tac[]
QED

Theorem ALL_DISTINCT_ADELKEY:
  ALL_DISTINCT (MAP f l) ⇒ ALL_DISTINCT (MAP f (ADELKEY k l))
Proof
  simp[ADELKEY_def, ALL_DISTINCT_MAP_FILTER]
QED

Theorem ALOOKUP_SND_inj:
  ∀l a b v. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l a = SOME v ∧ ALOOKUP l b = SOME v ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[SND]
QED

(* Frame facts for one connection's state change (LUPDATE c' k) *)
Theorem lupd_owner:
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧
  (∀hd. MEM hd (chd c') ⇒ MEM hd (chd (EL k cs))) ⇒
  Abbrev (
  ∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 (LUPDATE c' k cs))) ∧
             MEM hd (chd (EL i2 (LUPDATE c' k cs))) ⇒ i1 = i2)
Proof
  simp[markerTheory.Abbrev_def] >>
  rw[EL_LUPDATE] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem lupd_tbl_close:
  (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs))) ∧
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧ chd (EL k cs) = [hd0] ∧ chd c' = [] ⇒
  Abbrev (
  ∀hd. MEM hd (MAP FST (ADELKEY hd0 tbl)) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))))
Proof
  simp[markerTheory.Abbrev_def] >>
  rw[MAP_FST_ADELKEY, MEM_FILTER, EL_LUPDATE] >> eq_tac >> rw[]
  >- (qexists_tac ‘i’ >> rw[] >> gvs[]) >>
  Cases_on ‘i = k’ >> gvs[] >- (strip_tac >> gvs[] >> metis_tac[MEM]) >> metis_tac[]
QED

Theorem close_cok:
  (∀i hd. i < N ∧ MEM hd (chd (EL i cs)) ⇒
          ∃f j. ALOOKUP tbl hd = SOME f ∧ ALOOKUP ofds f = SOME j ∧ ALOOKUP hlc hd = SOME i ∧
                cok (brequests (rqs i)) (EL i cs) (EL j chans) (MEM hd sett) (hd ∈ rdyf i)
                    (hl_sent hd ps)) ∧
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧ chd (EL k cs) = [hd0] ∧ chd c' = [] ∧
  ALOOKUP tbl hd0 = SOME f0 ∧ ALOOKUP ofds f0 = SOME j0 ∧
  ALL_DISTINCT (MAP SND tbl) ∧ ALL_DISTINCT (MAP SND ofds) ∧
  (∀j. j ≠ j0 ⇒ EL j chans' = EL j chans) ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ∧ (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))) ⇒
         ∃f j. ALOOKUP (ADELKEY hd0 tbl) hd = SOME f ∧ ALOOKUP (ADELKEY f0 ofds) f = SOME j ∧
               ALOOKUP hlc hd = SOME i ∧
               cok (brequests (rqs i)) (EL i (LUPDATE c' k cs)) (EL j chans')
                   (MEM hd (FILTER (λy. hd0 ≠ y) sett)) (hd ∈ rdyf' i) (hl_sent hd ps'))
Proof
  simp[markerTheory.Abbrev_def] >>
  rpt strip_tac >> Cases_on ‘i = k’ >- gvs[EL_LUPDATE] >>
  gvs[EL_LUPDATE] >>
  ‘hd ≠ hd0’ by (strip_tac >> qpat_x_assum ‘hd = hd0’ SUBST_ALL_TAC >>
                 qpat_x_assum ‘∀i1 i2 hd. i1 < N ∧ i2 < N ∧ _ ⇒ _’
                   (qspecl_then [‘i’, ‘k’, ‘hd0’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
  ‘f ≠ f0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  ‘j ≠ j0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  qexistsl_tac [‘f’, ‘j’] >> simp[ALOOKUP_ADELKEY, MEM_FILTER]
QED

Theorem close_idle:
  (∀i hd'. i < N ∧ (EL i cs = CIdle ∨ ∃hd. EL i cs = CPend hd) ∧ ALOOKUP hlc hd' = SOME i ⇒
           hl_sent hd' ps = []) ∧
  k < N ∧ LENGTH cs = N ∧ chd c' = [] ∧ (c' = CIdle ⇒ ∃h. EL k cs = CPend h) ∧
  (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd'. i < N ∧ (EL i (LUPDATE c' k cs) = CIdle ∨ ∃hd. EL i (LUPDATE c' k cs) = CPend hd) ∧
          ALOOKUP hlc hd' = SOME i ⇒ hl_sent hd' ps' = [])
Proof
  simp[markerTheory.Abbrev_def] >>
  rpt strip_tac >> Cases_on ‘i = k’ >> gvs[EL_LUPDATE, chd_def] >> metis_tac[]
QED

Theorem close_up:
  (∀i hd rest hd'. i < N ∧ EL i cs = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                   hl_sent hd' ps ≠ [] ⇒ hd' = hd) ∧
  k < N ∧ LENGTH cs = N ∧ (∀h r. c' ≠ CUp h r) ∧ (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd rest hd'. i < N ∧ EL i (LUPDATE c' k cs) = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                  hl_sent hd' ps' ≠ [] ⇒ hd' = hd)
Proof
  simp[markerTheory.Abbrev_def] >>
  rpt strip_tac >> Cases_on ‘i = k’ >> gvs[EL_LUPDATE] >> metis_tac[]
QED

Theorem close_ended:
  (∀hd. MEM hd (MAP FST hlc) ⇔ MEM hd (hl_conn_handles ps)) ∧
  (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST hlc)) ∧
  (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ¬MEM hd (MAP FST tbl)) ∧
  (∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps)) ∧
  (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs))) ∧
  MEM hd0 (MAP FST hlc) ∧
  (∀hd. hd ≠ hd0 ⇒ (hl_refused hd ps' ⇔ hl_refused hd ps) ∧ (hl_eof hd ps' ⇔ hl_eof hd ps)) ∧
  ¬(hl_refused hd0 ps' ∧ hl_eof hd0 ps') ∧
  (∀hd. MEM hd (MAP FST (ADELKEY hd0 tbl)) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs'))) ⇒
  Abbrev (
  (∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ MEM hd (hl_conn_handles ps)) ∧
  (∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ ¬MEM hd (MAP FST (ADELKEY hd0 tbl))) ∧
  (∀hd. ¬(hl_refused hd ps' ∧ hl_eof hd ps')) ∧
  (∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ ∀i. i < N ⇒ ¬MEM hd (chd (EL i cs'))))
Proof
  simp[markerTheory.Abbrev_def] >>
  strip_tac >> rpt conj_tac >> gen_tac >> Cases_on ‘hd = hd0’ >>
  gvs[MAP_FST_ADELKEY, MEM_FILTER] >> metis_tac[]
QED

Theorem EVERY_ADELKEY:
  EVERY P (MAP g l) ⇒ EVERY P (MAP g (ADELKEY k l))
Proof
  simp[ADELKEY_def, EVERY_MEM, MEM_MAP, MEM_FILTER, PULL_EXISTS]
QED

Theorem crel_close:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ chd (EL k st.cs) = [hd] ∧
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧
  wframe j w w1 ∧ w1.open_fds = ADELKEY f w.open_fds ∧
  chd c' = [] ∧ (∀h r. c' ≠ CUp h r) ∧
  (c' = CIdle ⇒ (∃h. EL k st.cs = CPend h) ∧ hl_sent hd ps = []) ∧
  (∀hd'. hl_sent hd' ps' = hl_sent hd' ps) ∧ hl_conn_handles ps' = hl_conn_handles ps ∧
  (∀hd'. hd' ≠ hd ⇒ (hl_refused hd' ps' ⇔ hl_refused hd' ps) ∧ (hl_eof hd' ps' ⇔ hl_eof hd' ps)) ∧
  ¬(hl_refused hd ps' ∧ hl_eof hd ps') ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ⇒
  crel a N rqs lfd (st with cs := LUPDATE c' k st.cs) rdyf' ps' w1 (eh_del hd hs)
Proof
  strip_tac >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘wframe _ _ _’ (strip_assume_tac o REWRITE_RULE [wframe_def]) >>
  ‘MEM hd (chd (EL k st.cs))’ by simp[] >>
  ‘ALOOKUP st.hlc hd = SOME k’
    by (qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
        first_assum ACCEPT_TAC) >>
  ‘MEM hd (MAP FST st.hlc)’
    by (qpat_x_assum ‘ALOOKUP st.hlc hd = SOME k’ mp_tac >> rpt (pop_assum kall_tac) >>
        rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
  ‘∀x. MEM x (MAP SND (ADELKEY hd hs.tbl)) ⇔ MEM x (MAP SND hs.tbl) ∧ x ≠ f’
    by (gen_tac >> irule MEM_SND_ADELKEY >> simp[]) >>
  ‘∀hd'. MEM hd' (chd c') ⇒ MEM hd' (chd (EL k st.cs))’ by simp[] >>
  ‘c' = CIdle ⇒ ∃h. EL k st.cs = CPend h’ by (strip_tac >> fs[]) >>
  drule_all lupd_tbl_close >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_cok >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_idle >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_up >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_ended >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all lupd_owner >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  SIMP_TAC (srw_ss()) [crel_def, eh_del_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  TRY (irule ALL_DISTINCT_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (irule EVERY_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (gen_tac >> simp[MAP_FST_ADELKEY, MEM_FILTER] >>
       qpat_x_assum ‘∀f. MEM f (MAP FST w.open_fds) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       eq_tac >> rw[] >> NO_TAC) >>
  qpat_x_assum ‘w1.open_fds = _’ (fn th => REWRITE_TAC [th]) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (irule ALL_DISTINCT_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (irule EVERY_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (REWRITE_TAC [GSYM DE_MORGAN_THM] >> first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (rpt strip_tac >> qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       qpat_x_assum ‘∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ MEM hd (hl_conn_handles ps)’ irule >>
       simp[] >> NO_TAC) >>
  TRY (rpt gen_tac >> strip_tac >>
       qpat_x_assum ‘∀hd'. hl_sent hd' ps' = _’ (fn th => REWRITE_TAC [th]) >>
       qpat_x_assum ‘∀hd i. ALOOKUP st.hlc hd = SOME i ⇒ i < N ∧ _’ drule >> simp[] >> NO_TAC)
QED

(* ------------------------------------------------------------------------
   An action that keeps a connection's handle open keeps the relation
   ------------------------------------------------------------------------ *)

Theorem keep_tbl:
  (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs))) ∧
  LENGTH cs = N ∧ k < N ∧ chd c' = chd (EL k cs) ⇒
  Abbrev (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))))
Proof
  simp[markerTheory.Abbrev_def] >> rw[EL_LUPDATE] >> eq_tac >> rw[]
  >- (qexists_tac ‘i’ >> rw[] >> gvs[]) >>
  qexists_tac ‘i’ >> Cases_on ‘i = k’ >> gvs[]
QED

Theorem keep_cok:
  (∀i hd. i < N ∧ MEM hd (chd (EL i cs)) ⇒
          ∃f j. ALOOKUP tbl hd = SOME f ∧ ALOOKUP ofds f = SOME j ∧ ALOOKUP hlc hd = SOME i ∧
                cok (brequests (rqs i)) (EL i cs) (EL j chans) (MEM hd sett) (hd ∈ rdyf i)
                    (hl_sent hd ps)) ∧
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧ chd (EL k cs) = [hd0] ∧ chd c' = [hd0] ∧
  ALOOKUP tbl hd0 = SOME f0 ∧ ALOOKUP ofds f0 = SOME j0 ∧
  ALL_DISTINCT (MAP SND tbl) ∧ ALL_DISTINCT (MAP SND ofds) ∧
  (∀j. j ≠ j0 ⇒ EL j chans' = EL j chans) ∧
  cok (brequests (rqs k)) c' (EL j0 chans') (MEM hd0 sett) (hd0 ∈ rdyf' k) (hl_sent hd0 ps') ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ∧ (∀hd. hd ≠ hd0 ⇒ hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))) ⇒
         ∃f j. ALOOKUP tbl hd = SOME f ∧ ALOOKUP ofds f = SOME j ∧ ALOOKUP hlc hd = SOME i ∧
               cok (brequests (rqs i)) (EL i (LUPDATE c' k cs)) (EL j chans') (MEM hd sett)
                   (hd ∈ rdyf' i) (hl_sent hd ps'))
Proof
  simp[markerTheory.Abbrev_def] >> rpt strip_tac >> Cases_on ‘i = k’
  >- (qpat_x_assum ‘i = k’ SUBST_ALL_TAC >>
      qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ (qspecl_then [‘k’, ‘hd0’] mp_tac) >>
      simp[] >> strip_tac >> gvs[EL_LUPDATE]) >>
  gvs[EL_LUPDATE] >>
  ‘hd ≠ hd0’ by (strip_tac >> qpat_x_assum ‘hd = hd0’ SUBST_ALL_TAC >>
                 qpat_x_assum ‘∀i1 i2 hd. i1 < N ∧ i2 < N ∧ _ ⇒ _’
                   (qspecl_then [‘i’, ‘k’, ‘hd0’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
  ‘f ≠ f0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  ‘j ≠ j0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  qexistsl_tac [‘f’, ‘j’] >> simp[]
QED

Theorem keep_sends:
  (∀hd. hl_sent hd ps ≠ [] ⇒ MEM hd (MAP FST hlc)) ∧
  (∀hd i. ALOOKUP hlc hd = SOME i ⇒ i < N ∧ hl_sent hd ps ≼ brequests (rqs i)) ∧
  (∀hd hd' i. ALOOKUP hlc hd = SOME i ∧ ALOOKUP hlc hd' = SOME i ∧
              hl_sent hd ps ≠ [] ∧ hl_sent hd' ps ≠ [] ⇒ hd = hd') ∧
  (∀i hd'. i < N ∧ (EL i cs = CIdle ∨ ∃hd. EL i cs = CPend hd) ∧ ALOOKUP hlc hd' = SOME i ⇒
           hl_sent hd' ps = []) ∧
  (∀i hd rest hd'. i < N ∧ EL i cs = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                   hl_sent hd' ps ≠ [] ⇒ hd' = hd) ∧
  LENGTH cs = N ∧ k < N ∧ ALOOKUP hlc hd0 = SOME k ∧
  ((∃rest. EL k cs = CUp hd0 rest) ∨ EL k cs = CPend hd0) ∧
  ((∃rest. c' = CUp hd0 rest) ∨ c' = CPend hd0) ∧
  (∀h. c' = CPend h ⇒ EL k cs = CPend h) ∧
  (∀hd. hd ≠ hd0 ⇒ hl_sent hd ps' = hl_sent hd ps) ∧
  hl_sent hd0 ps' ≼ brequests (rqs k) ∧ (hl_sent hd0 ps' ≠ [] ⇒ ∃rest. c' = CUp hd0 rest) ⇒
  Abbrev (
  (∀hd. hl_sent hd ps' ≠ [] ⇒ MEM hd (MAP FST hlc)) ∧
  (∀hd i. ALOOKUP hlc hd = SOME i ⇒ i < N ∧ hl_sent hd ps' ≼ brequests (rqs i)) ∧
  (∀hd hd' i. ALOOKUP hlc hd = SOME i ∧ ALOOKUP hlc hd' = SOME i ∧
              hl_sent hd ps' ≠ [] ∧ hl_sent hd' ps' ≠ [] ⇒ hd = hd') ∧
  (∀i hd'. i < N ∧ (EL i (LUPDATE c' k cs) = CIdle ∨ ∃hd. EL i (LUPDATE c' k cs) = CPend hd) ∧
           ALOOKUP hlc hd' = SOME i ⇒ hl_sent hd' ps' = []) ∧
  (∀i hd rest hd'. i < N ∧ EL i (LUPDATE c' k cs) = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                   hl_sent hd' ps' ≠ [] ⇒ hd' = hd))
Proof
  simp[markerTheory.Abbrev_def] >> strip_tac >> rpt conj_tac >> rpt gen_tac >>
  TRY (Cases_on ‘hd = hd0’) >> TRY (Cases_on ‘hd' = hd0’) >> TRY (Cases_on ‘i = k’) >>
  rw[EL_LUPDATE] >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem keep_chd:
  chd c' = chd (EL k cs) ∧ k < LENGTH cs ⇒
  Abbrev (∀i. i < LENGTH cs ⇒ chd (EL i (LUPDATE c' k cs)) = chd (EL i cs))
Proof
  simp[markerTheory.Abbrev_def] >> rw[EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem crel_keep:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ chd (EL k st.cs) = [hd] ∧ chd c' = [hd] ∧
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧
  wframe j w w1 ∧ w1.open_fds = w.open_fds ∧
  cok (brequests (rqs k)) c' (EL j w1.chans) (MEM hd hs.settling) (hd ∈ rdyf' k) (hl_sent hd ps') ∧
  (∀h. c' = CPend h ⇒ EL k st.cs = CPend h) ∧
  (∀hd'. hd' ≠ hd ⇒ hl_sent hd' ps' = hl_sent hd' ps) ∧
  hl_sent hd ps' ≼ brequests (rqs k) ∧ (hl_sent hd ps' ≠ [] ⇒ ∃rest. c' = CUp hd rest) ∧
  hl_conn_handles ps' = hl_conn_handles ps ∧
  (∀hd'. hl_refused hd' ps' ⇔ hl_refused hd' ps) ∧ (∀hd'. hl_eof hd' ps' ⇔ hl_eof hd' ps) ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ⇒
  crel a N rqs lfd (st with cs := LUPDATE c' k st.cs) rdyf' ps' w1 hs
Proof
  strip_tac >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘wframe _ _ _’ (strip_assume_tac o REWRITE_RULE [wframe_def]) >>
  ‘MEM hd (chd (EL k st.cs))’ by simp[] >>
  ‘ALOOKUP st.hlc hd = SOME k’
    by (qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
        first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN ‘(∃rest. EL k st.cs = CUp hd rest) ∨ EL k st.cs = CPend hd’ assume_tac
  >- (qpat_x_assum ‘chd (EL k st.cs) = [hd]’ mp_tac >> rpt (pop_assum kall_tac) >>
      Cases_on ‘EL k st.cs’ >> simp[chd_def]) >>
  Q.SUBGOAL_THEN ‘(∃rest. c' = CUp hd rest) ∨ c' = CPend hd’ assume_tac
  >- (qpat_x_assum ‘chd c' = [hd]’ mp_tac >> rpt (pop_assum kall_tac) >>
      Cases_on ‘c'’ >> simp[chd_def]) >>
  ‘chd c' = chd (EL k st.cs)’ by simp[] >>
  ‘∀hd'. MEM hd' (chd c') ⇒ MEM hd' (chd (EL k st.cs))’ by simp[] >>
  ‘k < LENGTH st.cs’ by simp[] >>
  drule_all keep_chd >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all keep_tbl >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all keep_cok >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all keep_sends >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all lupd_owner >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  SIMP_TAC (srw_ss()) [crel_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  qpat_x_assum ‘w1.open_fds = _’ (fn th => REWRITE_TAC [th]) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (REWRITE_TAC [GSYM DE_MORGAN_THM] >> first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  qpat_x_assum ‘∀hd'. hl_refused hd' ps' ⇔ _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘∀hd'. hl_eof hd' ps' ⇔ _’ (fn th => REWRITE_TAC [th]) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (REWRITE_TAC [GSYM DE_MORGAN_THM] >> first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  gen_tac >> disch_tac >> gen_tac >> strip_tac >>
  ‘i < LENGTH st.cs’ by simp[] >>
  qpat_x_assum ‘∀i. i < LENGTH st.cs ⇒ chd _ = _’ (fn th => simp[th]) >>
  qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ∀i. i < N ⇒ ¬MEM hd _’ drule >>
  disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   A read on a connection's handle, a write on an up one
   ------------------------------------------------------------------------ *)

Theorem wframe_refl[simp]:
  wframe j w w
Proof
  simp[wframe_def]
QED

Theorem cupd_st_simp[simp]:
  st with <| cs := X; nh := st.nh; hlc := st.hlc |> = st with cs := X
Proof
  simp[theorem "cst_component_equality"]
QED

Theorem cread_bounds[simp]:
  0 < cread ∧ cread < 256 ** 8
Proof
  EVAL_TAC
QED

Theorem crel_handle:
  crel a N rqs lfd st rdyf ps w hs ∧ i < N ∧ MEM hd (chd (EL i st.cs)) ⇒
  ∃f j. ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
        ALOOKUP st.hlc hd = SOME i ∧
        cok (brequests (rqs i)) (EL i st.cs) (EL j w.chans) (MEM hd hs.settling)
            (hd ∈ rdyf i) (hl_sent hd ps)
Proof
  strip_tac >> qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
  qexistsl_tac [‘f’, ‘j’] >> simp[] >>
  imp_res_tac ALOOKUP_MEM >> fs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> res_tac >> fs[]
QED

Theorem crel_takes:
  crel a N rqs lfd st rdyf ps w hs ⇒ w.takes = (λj b n. n) ∧ LENGTH st.cs = N
Proof
  simp[crel_def]
QED

Theorem crel_open_not_ended:
  crel a N rqs lfd st rdyf ps w hs ∧ ALOOKUP hs.tbl hd = SOME f ⇒
  ¬hl_refused hd ps ∧ ¬hl_eof hd ps
Proof
  strip_tac >>
  ‘MEM hd (MAP FST hs.tbl)’
    by (qpat_x_assum ‘ALOOKUP hs.tbl hd = SOME f’ mp_tac >> rpt (pop_assum kall_tac) >>
        rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ¬MEM hd (MAP FST hs.tbl)’
    (qspec_then ‘hd’ mp_tac) >> simp[]
QED

Theorem crel_read:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ MEM hd (chd (EL k st.cs)) ∧
  (∀h. EL k st.cs = CPend h ⇒ hd ∈ rdyf k) ⇒
  ∃r w1 hs1. ehdo lfd (w, hs) (ERead hd cread) = SOME (r, (w1, hs1)) ∧
     crel a N rqs lfd (cupd rqs st [(k, ERead hd cread)] [r]) ((k =+ ∅) rdyf)
       (ps ++ [(ERead hd cread, r)]) w1 hs1 ∧ wkeep w w1
Proof
  strip_tac >> drule_all crel_handle >> strip_tac >>
  ‘chd (EL k st.cs) = [hd]’
    by (qpat_x_assum ‘MEM hd (chd _)’ mp_tac >> Cases_on ‘EL k st.cs’ >> simp[chd_def]) >>
  ‘(EL j w.chans).status ≠ Connecting ∧ (EL j w.chans).status ≠ Failed ∧
   ¬(EL j w.chans).shut ∧
   ((EL j w.chans).status = Refused ⇒ EL k st.cs = CPend hd) ∧
   hl_sent hd ps = (EL j w.chans).sent ∧
   (EL k st.cs = CPend hd ⇒ hl_sent hd ps = [])’
    by (Cases_on ‘EL k st.cs’ >> gvs[cok_def, chd_def]) >>
  ‘0 < cread ∧ cread < 256 ** 8’ by simp[] >>
  drule_all ehdo_read >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  qexistsl_tac [‘r’, ‘w'’, ‘hs'’] >> simp[] >>
  drule_all crel_open_not_ended >> strip_tac >>
  ‘(EL j w.chans).status = Up ∨ (EL j w.chans).status = Refused’
    by (Cases_on ‘(EL j w.chans).status’ >> fs[]) >>
  (* refused *)
  TRY (qpat_x_assum ‘r = ERefused’ SUBST_ALL_TAC >> qpat_x_assum ‘hs' = _’ SUBST_ALL_TAC >>
       ‘EL k st.cs = CPend hd’
         by (qpat_x_assum ‘_ ⇒ EL k st.cs = CPend hd’ irule >> first_assum ACCEPT_TAC) >>
       simp[cres_def, new_hd_def] >> conj_tac
       >- (irule crel_close >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
           qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[chd_def, combinTheory.APPLY_UPDATE_THM]) >>
       fs[wkeep_def, wframe_def] >> rw[] >> Cases_on ‘j' = j’ >> simp[] >> NO_TAC) >>
  (* EOF *)
  TRY (qpat_x_assum ‘r = EGot (SOME [])’ SUBST_ALL_TAC >> qpat_x_assum ‘hs' = _’ SUBST_ALL_TAC >>
       simp[cres_def, new_hd_def] >> conj_tac
       >- (irule crel_close >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
           qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[chd_def, combinTheory.APPLY_UPDATE_THM]) >>
       fs[wkeep_def, wframe_def] >> rw[] >> Cases_on ‘j' = j’ >> simp[] >> NO_TAC) >>
  (* data, none: the connection stays (CPend becomes CUp) *)
  ‘∀d. r = EGot (SOME d) ⇒ d ≠ []’ by (rw[] >> fs[cread_def]) >>
  ‘∃rest. cres (brequests (rqs k)) (EL k st.cs) (ERead hd cread) r = CUp hd rest ∧
          (EL j w.chans).sent ++ rest = brequests (rqs k)’
    by (Cases_on ‘EL k st.cs’ >> gvs[chd_def, cok_def, cres_def] >>
        Cases_on ‘TAKE cread (EL j w.chans).inbox’ >> gvs[TAKE_EQ_NIL]) >>
  qpat_x_assum ‘r = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_x_assum ‘cres _ _ _ _ = _’ (fn th => simp[new_hd_def, th]) >>
  TRY (conj_tac >- (irule crel_keep >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
                    qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[cok_def] >>
                    gvs[wframe_def] >> metis_tac[rich_listTheory.IS_PREFIX_APPEND]) >>
       fs[wkeep_def, wframe_def] >> rw[] >> Cases_on ‘j' = j’ >> simp[] >> NO_TAC) >>
  irule crel_keep >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
  qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[cok_def] >>
  metis_tac[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem crel_write:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CUp hd rest ∧ rest ≠ [] ⇒
  ∃r w1 hs1. ehdo lfd (w, hs) (EWrite hd rest) = SOME (r, (w1, hs1)) ∧
     crel a N rqs lfd (cupd rqs st [(k, EWrite hd rest)] [r]) rdyf
       (ps ++ [(EWrite hd rest, r)]) w1 hs1 ∧ wkeep w w1 ∧
     EL k (cupd rqs st [(k, EWrite hd rest)] [r]).cs = CUp hd [] ∧ new_hd r = NONE
Proof
  strip_tac >> ‘MEM hd (chd (EL k st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >> drule crel_takes >> strip_tac >>
  ‘(EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧
   (EL j w.chans).sent ++ rest = brequests (rqs k) ∧ hl_sent hd ps = (EL j w.chans).sent’
    by gvs[cok_def] >>
  drule_all ehdo_write_up >> disch_then (fn th => simp[th]) >>
  simp[cres_def, new_hd_def, EL_LUPDATE] >>
  qabbrev_tac ‘w1 = upd_chan j (λc. c with <| sent := c.sent ++ rest;
                                              inflight := c.inflight + LENGTH rest |>) w’ >>
  ‘wframe j w w1 ∧ w1.open_fds = w.open_fds ∧
   EL j w1.chans = (EL j w.chans) with <| sent := (EL j w.chans).sent ++ rest;
                                         inflight := (EL j w.chans).inflight + LENGTH rest |>’
    by simp[Abbr ‘w1’, wframe_def, upd_chan_def, EL_LUPDATE] >>
  conj_tac
  >- (irule crel_keep >> simp[chd_def, cok_def, hl_one] >>
      qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[chd_def] >> rw[] >>
      gvs[hl_one, Abbr ‘w1’, upd_chan_def, EL_LUPDATE]) >>
  simp[wkeep_def, Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >> rw[]
QED

Theorem wkeep_trans:
  wkeep w1 w2 ∧ wkeep w2 w3 ⇒ wkeep w1 w3
Proof
  rw[wkeep_def] >> rpt (first_x_assum (qspec_then ‘j’ mp_tac)) >> rw[] >> gvs[]
QED

Theorem ehacts_one:
  ehdo lfd st x = SOME (r, st1) ⇒ ehacts lfd st [x] = SOME ([r], st1)
Proof
  simp[ehacts_def]
QED

Theorem ehacts_two:
  ehdo lfd st x = SOME (r, st1) ∧ ehdo lfd st1 y = SOME (r', st2) ⇒
  ehacts lfd st [x; y] = SOME ([r; r'], st2)
Proof
  simp[ehacts_def]
QED

(* The goal and the assumptions in the same normal form, without using the
   assumptions *)
val norm_tac = RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >> SIMP_TAC (srw_ss()) [] >>
               rpt conj_tac >> TRY (first_assum ACCEPT_TAC);

(* Connection k's actions of the round (started with nh0 handles used):
   the relation holds after them, k's ready set used up; the others'
   states are untouched; at most one handle is issued *)
Theorem crel_conn:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ N < dimword (:64) ∧
  (nh0 < cbound ⇒ st.nh + 2 < dimword (:64)) ⇒
  ∃rs w1 hs1.
    ehacts lfd (w, hs) (cact1 a nh0 (EL k st.cs) (rdyf k)) = SOME (rs, (w1, hs1)) ∧
    crel a N rqs lfd (cupd rqs st (MAP (λx. (k, x)) (cact1 a nh0 (EL k st.cs) (rdyf k))) rs)
      ((k =+ ∅) rdyf) (ps ++ ZIP (cact1 a nh0 (EL k st.cs) (rdyf k), rs)) w1 hs1 ∧
    wkeep w w1 ∧ LENGTH rs = LENGTH (cact1 a nh0 (EL k st.cs) (rdyf k)) ∧
    (∀i. i ≠ k ⇒ EL i (cupd rqs st (MAP (λx. (k, x)) (cact1 a nh0 (EL k st.cs) (rdyf k))) rs).cs =
                 EL i st.cs) ∧
    (cupd rqs st (MAP (λx. (k, x)) (cact1 a nh0 (EL k st.cs) (rdyf k))) rs).nh ≤ st.nh + 1
Proof
  strip_tac >> ‘LENGTH st.cs = N ∧ st.nh = hs.nxt’ by fs[crel_def] >>
  (* no action: only the ready set changes *)
  ‘(∀hd. MEM hd (chd (EL k st.cs)) ⇒ hd ∉ rdyf k) ⇒
   crel a N rqs lfd st ((k =+ ∅) rdyf) ps w hs’
    by (strip_tac >> irule crel_rdyf >> qexists_tac ‘rdyf’ >>
        rw[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  Cases_on ‘EL k st.cs’ >> simp[cact1_def]
  >~ [‘EL k st.cs = CIdle’]
  >- (IF_CASES_TAC
      >- (‘hs.nxt + 2 < dimword (:64)’ by gvs[] >>
          drule_all crel_connect >> strip_tac >> drule ehacts_one >> strip_tac >>
          qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> norm_tac >> rw[EL_LUPDATE]) >>
      simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def])
  >~ [‘EL k st.cs = CDone’]
  >- (simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def])
  >~ [‘EL k st.cs = CPend hd’]
  >- (IF_CASES_TAC
      >- (‘MEM hd (chd (EL k st.cs)) ∧ ∀h. EL k st.cs = CPend h ⇒ hd ∈ rdyf k’ by simp[chd_def] >>
          drule_all crel_read >> strip_tac >> drule ehacts_one >> strip_tac >>
          qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> norm_tac >> rw[EL_LUPDATE]) >>
      simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def]) >>
  rename1 ‘EL k st.cs = CUp hd rest’ >>
  Cases_on ‘rest = []’ >> simp[]
  >- (IF_CASES_TAC
      >- (‘MEM hd (chd (EL k st.cs)) ∧ ∀h. EL k st.cs = CPend h ⇒ hd ∈ rdyf k’ by simp[chd_def] >>
          drule_all crel_read >> strip_tac >> drule ehacts_one >> strip_tac >>
          qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> norm_tac >> rw[EL_LUPDATE]) >>
      simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def]) >>
  drule_all crel_write >> strip_tac >>
  qabbrev_tac ‘st1 = cupd rqs st [(k, EWrite hd rest)] [r]’ >>
  ‘LENGTH st1.cs = N ∧ st1.nh = st.nh ∧ ∀i. i ≠ k ⇒ EL i st1.cs = EL i st.cs’
    by (simp[Abbr ‘st1’, EL_LUPDATE] >> fs[]) >>
  ‘∀r'. cupd rqs st [(k, EWrite hd rest); (k, ERead hd cread)] [r; r'] =
        cupd rqs st1 [(k, ERead hd cread)] [r']’
    by (rpt (qpat_x_assum ‘_ = _’ kall_tac) >> qunabbrev_tac ‘st1’ >>
        simp_tac (srw_ss()) [cupd_def]) >>
  ‘cupd rqs st [(k, EWrite hd rest)] [r] = st1’ by fs[markerTheory.Abbrev_def] >>
  IF_CASES_TAC
  >- (‘MEM hd (chd (EL k st1.cs)) ∧ ∀h. EL k st1.cs = CPend h ⇒ hd ∈ rdyf k’ by simp[chd_def] >>
      drule_all crel_read >> strip_tac >>
      ‘ehacts lfd (w, hs) [EWrite hd rest; ERead hd cread] = SOME ([r; r'], (w1', hs1'))’
        by (irule ehacts_two >> metis_tac[]) >>
      qexistsl_tac [‘[r; r']’, ‘w1'’, ‘hs1'’] >>
      SIMP_TAC list_ss [] >>
      qpat_x_assum ‘ehacts _ _ _ = _’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘∀r'. cupd _ _ [_; _] _ = _’ (fn th => REWRITE_TAC [th]) >>
      ‘ps ++ [(EWrite hd rest, r); (ERead hd cread, r')] =
       ps ++ [(EWrite hd rest, r)] ++ [(ERead hd cread, r')]’ by simp[] >>
      pop_assum SUBST1_TAC >> rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (irule wkeep_trans >> qexists_tac ‘w1’ >> conj_tac >> first_assum ACCEPT_TAC)
      >- (rpt strip_tac >> asm_simp_tac (srw_ss()) [EL_LUPDATE])
      >> SIMP_TAC (srw_ss()) [] >> qpat_x_assum ‘st1.nh = _’ SUBST1_TAC >> rw[]) >>
  qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> drule ehacts_one >> disch_then (fn th => REWRITE_TAC [th]) >>
  SIMP_TAC list_ss [] >> qpat_x_assum ‘cupd _ _ [_] _ = st1’ (fn th => REWRITE_TAC [th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule crel_rdyf >> qexists_tac ‘rdyf’ >> conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rw[combinTheory.APPLY_UPDATE_THM] >> gvs[chd_def]) >>
  simp[]
QED

Theorem cupd_APPEND:
  ∀xs rs st. LENGTH rs = LENGTH xs ⇒
    cupd rqs st (xs ++ ys) (rs ++ rs') = cupd rqs (cupd rqs st xs rs) ys rs'
Proof
  Induct >> simp[cupd_def] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >>
  simp[cupd_def]
QED

Theorem ehacts_APPEND:
  ∀xs st rs st1. ehacts lfd st xs = SOME (rs, st1) ∧ ehacts lfd st1 ys = SOME (rs', st2) ⇒
    ehacts lfd st (xs ++ ys) = SOME (rs ++ rs', st2)
Proof
  Induct >> simp[ehacts_def] >> rw[] >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

Theorem ehacts_LENGTH:
  ∀xs st rs st1. ehacts lfd st xs = SOME (rs, st1) ⇒ LENGTH rs = LENGTH xs
Proof
  Induct >> simp[ehacts_def] >> rw[] >> gvs[AllCaseEqs()] >> res_tac
QED

(* The round's actions, connection by connection: the first m *)
Definition cacts_upto_def:
  cacts_upto a st0 rdy m =
    FLAT (GENLIST (λi. MAP (λx. (i, x)) (cact1 a st0.nh (EL i st0.cs) rdy)) m)
End

Theorem cacts_upto_SUC:
  cacts_upto a st0 rdy (SUC m) =
    cacts_upto a st0 rdy m ++ MAP (λx. (m, x)) (cact1 a st0.nh (EL m st0.cs) rdy)
Proof
  simp[cacts_upto_def, GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

Theorem cacts_upto_all:
  cacts a st0 rdy = cacts_upto a st0 rdy (LENGTH st0.cs)
Proof
  simp[cacts_def, cacts_upto_def]
QED

(* The round's actions (from st0, with the ready handles rdy) keep the
   relation; every connection's ready set used up *)
Theorem crel_acts:
  crel a N rqs lfd st0 (K rdy) ps w hs ∧ N < dimword (:64) ∧
  (st0.nh < cbound ⇒ st0.nh + N + 1 < dimword (:64)) ⇒
  ∀m. m ≤ N ⇒
    ∃rs w1 hs1.
      ehacts lfd (w, hs) (MAP SND (cacts_upto a st0 rdy m)) = SOME (rs, (w1, hs1)) ∧
      LENGTH rs = LENGTH (cacts_upto a st0 rdy m) ∧
      crel a N rqs lfd (cupd rqs st0 (cacts_upto a st0 rdy m) rs) (λi. if i < m then ∅ else rdy)
        (ps ++ ZIP (MAP SND (cacts_upto a st0 rdy m), rs)) w1 hs1 ∧
      wkeep w w1 ∧
      (∀i. m ≤ i ⇒ EL i (cupd rqs st0 (cacts_upto a st0 rdy m) rs).cs = EL i st0.cs) ∧
      (cupd rqs st0 (cacts_upto a st0 rdy m) rs).nh ≤ st0.nh + m
Proof
  strip_tac >> Induct
  >- (simp[cacts_upto_def, ehacts_def, cupd_def] >>
      ‘(λi:num. rdy) = K rdy’ by simp[FUN_EQ_THM] >> simp[]) >>
  strip_tac >> fs[] >>
  qabbrev_tac ‘st = cupd rqs st0 (cacts_upto a st0 rdy m) rs’ >>
  ‘m < N’ by simp[] >>
  ‘st0.nh < cbound ⇒ st.nh + 2 < dimword (:64)’ by simp[] >>
  drule_then (qspecl_then [‘st0.nh’, ‘m’] mp_tac) crel_conn >> simp[] >>
  ‘EL m st.cs = EL m st0.cs’ by simp[] >> simp[] >> strip_tac >>
  qexistsl_tac [‘rs ++ rs'’, ‘w1'’, ‘hs1'’] >>
  qabbrev_tac ‘xs = cact1 a st0.nh (EL m st0.cs) rdy’ >>
  ‘MAP SND (cacts_upto a st0 rdy (SUC m)) = MAP SND (cacts_upto a st0 rdy m) ++ xs’
    by simp[cacts_upto_SUC, MAP_MAP_o, combinTheory.o_DEF] >>
  ‘cupd rqs st0 (cacts_upto a st0 rdy (SUC m)) (rs ++ rs') = cupd rqs st (MAP (λx. (m, x)) xs) rs'’
    by (simp[cacts_upto_SUC, Abbr ‘st’] >> irule cupd_APPEND >> simp[]) >>
  ‘(λi. if i < SUC m then ∅ else rdy) = (m =+ ∅) (λi. if i < m then ∅ else rdy)’
    by (simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[] >> fs[]) >>
  ‘ps ++ ZIP (MAP SND (cacts_upto a st0 rdy m) ++ xs, rs ++ rs') =
   ps ++ ZIP (MAP SND (cacts_upto a st0 rdy m), rs) ++ ZIP (xs, rs')’
    by simp[ZIP_APPEND] >>
  ‘LENGTH (cacts_upto a st0 rdy (SUC m)) = LENGTH (cacts_upto a st0 rdy m) + LENGTH xs’
    by simp[cacts_upto_SUC] >>
  ntac 5 (pop_assum (fn th => REWRITE_TAC [th] >> mp_tac th)) >>
  ntac 5 (disch_then (fn th => REWRITE_TAC [th])) >> rpt conj_tac
  >- (irule ehacts_APPEND >> metis_tac[])
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- (irule wkeep_trans >> qexists_tac ‘w1’ >> conj_tac >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> ‘i ≠ m ∧ m ≤ i’ by simp[] >> metis_tac[])
  >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll keeps the relation
   ------------------------------------------------------------------------ *)

(* What time passing does to the world: arrivals only; a channel's
   connect may settle; a channel still connecting is untouched *)
Definition tick_rel_def:
  tick_rel (w : eworld) w' ⇔
    w'.open_fds = w.open_fds ∧ w'.takes = w.takes ∧ w'.alloc = w.alloc ∧
    w'.reserved = w.reserved ∧ MAP FST w'.listening = MAP FST w.listening ∧
    w'.nosock = w.nosock ∧ w'.nconnects = w.nconnects ∧ w'.calls = w.calls ∧
    w'.hist = w.hist ∧ w'.env = w.env ∧ LENGTH w.chans ≤ LENGTH w'.chans ∧
    ∀j. j < LENGTH w.chans ⇒
        (EL j w'.chans).shut = (EL j w.chans).shut ∧
        (EL j w'.chans).sent = (EL j w.chans).sent ∧
        ((EL j w'.chans).status = (EL j w.chans).status ∨
         (EL j w.chans).status = Connecting ∧
         ((EL j w'.chans).status = Up ∨ (EL j w'.chans).status = Refused)) ∧
        ((EL j w'.chans).status = Connecting ⇒
         (EL j w'.chans).inbox = (EL j w.chans).inbox ∧
         (EL j w'.chans).peer_eof = (EL j w.chans).peer_eof)
End

Theorem tick_rel_refl:
  tick_rel w (w with clock := n)
Proof
  simp[tick_rel_def]
QED

Theorem tick_rel_trans:
  tick_rel w1 w2 ∧ tick_rel w2 w3 ⇒ tick_rel w1 w3
Proof
  simp[tick_rel_def] >> strip_tac >> gen_tac >> strip_tac >>
  ‘j < LENGTH w2.chans’ by simp[] >>
  rpt (first_x_assum (qspec_then ‘j’ mp_tac)) >> simp[] >> rw[] >> gvs[]
QED

Theorem tick_rel_deliver:
  tick_rel w (ep_deliver w x)
Proof
  Cases_on ‘x’ >> rw[ep_deliver_def, tick_rel_def, upd_chan_def, EL_LUPDATE] >>
  TRY (CASE_TAC >> simp[] >> PairCases_on ‘h’ >> simp[MAP_FST_AFUPDKEY, EL_APPEND1] >> NO_TAC) >>
  rw[] >> gvs[]
QED

Theorem tick_rel_FOLDL:
  ∀xs w0. tick_rel w w0 ⇒ tick_rel w (FOLDL ep_deliver w0 xs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[tick_rel_trans, tick_rel_deliver]
QED

Theorem tick_rel_tick:
  tick_rel w (ep_tick w)
Proof
  simp[ep_tick_def] >> irule tick_rel_FOLDL >> simp[tick_rel_refl]
QED

(* One connection's channel across the poll: sett' says whether the settle
   is still unreported; rd' whether the handle is reported ready *)
Theorem poll_cok:
  cok b c ch sett F sent ∧
  ch'.shut = ch.shut ∧ ch'.sent = ch.sent ∧
  (ch'.status = ch.status ∨ ch.status = Connecting ∧ (ch'.status = Up ∨ ch'.status = Refused)) ∧
  (ch'.status = Connecting ⇒ ch'.inbox = ch.inbox ∧ ch'.peer_eof = ch.peer_eof) ∧
  (sett' ⇔ sett ∧ ¬(inh ∧ ch'.status ≠ Connecting)) ∧
  (inh ∧ sett ∧ ch'.status ≠ Connecting ⇒ rd') ∧
  (rd' ⇒ ch'.inbox ≠ [] ∨ ch'.peer_eof ∨ ch'.status = Refused ∨ ch'.status = Failed ∨
         sett ∧ ch'.status ≠ Connecting) ⇒
  cok b c ch' sett' rd' sent
Proof
  Cases_on ‘c’ >> simp[cok_def] >> rw[] >> gvs[] >>
  Cases_on ‘ch'.status’ >> gvs[] >> metis_tac[]
QED

Theorem crel_poll:
  crel a N rqs lfd st (K ∅) ps w hs ∧ ehpoll lfd hs hfds w = (rdy, w', hs') ⇒
  crel a N rqs lfd st (K (set rdy)) ps w' hs'
Proof
  strip_tac >> qpat_x_assum ‘ehpoll _ _ _ _ = _’ mp_tac >> simp[ehpoll_def] >> strip_tac >>
  qabbrev_tac ‘w1 = ep_tick w’ >>
  ‘tick_rel w w1’ by simp[Abbr ‘w1’, tick_rel_tick] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [tick_rel_def]) >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  gvs[] >>
  SIMP_TAC (srw_ss()) [crel_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (‘LENGTH w'.listening = LENGTH w.listening’ by metis_tac[LENGTH_MAP] >> simp[] >> NO_TAC) >>
  TRY (fs[EVERY_MEM] >> rw[] >> res_tac >> simp[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_x_assum ‘∀hd. MEM hd (MAP FST hs.tbl) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       rpt strip_tac >> qpat_x_assum ‘∀hd. _ ⇒ ∀i. i < LENGTH st.cs ⇒ _’ drule >>
       disch_then drule >> simp[] >> NO_TAC) >>
  rpt strip_tac >> qpat_x_assum ‘∀i hd. i < LENGTH st.cs ∧ MEM hd _ ⇒ ∃f j. _’ drule_all >>
  strip_tac >> qexistsl_tac [‘f’, ‘j’] >> simp[] >>
  ‘j < LENGTH w.chans’
    by (imp_res_tac ALOOKUP_MEM >> fs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘¬MEM f (MAP FST w.listening)’
    by (imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘ep_chan_of w' f = SOME j’ by simp[ep_chan_of_def] >>
  ‘chan_status w' f = SOME (EL j w'.chans).status’ by simp[chan_status_def] >>
  ‘FILTER (λ(l, a, q). l = f) w'.listening = []’
    by (simp[FILTER_EQ_NIL, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
        qpat_x_assum ‘¬MEM f (MAP FST w.listening)’ mp_tac >>
        qpat_x_assum ‘MAP FST w'.listening = _’ (SUBST1_TAC o SYM) >>
        simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘ep_readable w' f ⇔ (EL j w'.chans).inbox ≠ [] ∨ (EL j w'.chans).peer_eof ∨
                      (EL j w'.chans).status = Refused ∨ (EL j w'.chans).status = Failed’
    by simp[ep_readable_def] >>
  qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  irule poll_cok >>
  qexistsl_tac [‘EL j w.chans’, ‘MEM hd hfds’, ‘MEM hd hs.settling’] >>
  simp[MEM_FILTER] >> rpt (pop_assum kall_tac) >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem ehdo_new_hd:
  ehdo lfd st x = SOME (r, st') ∧ (∀p. x ≠ EConnect p) ⇒ new_hd r = NONE
Proof
  PairCases_on ‘st’ >> Cases_on ‘x’ >> simp[ehdo_def] >> rw[] >>
  every_case_tac >> gvs[new_hd_def] >> pairarg_tac >> gvs[new_hd_def]
QED

Theorem ehacts_new_hd:
  ∀xs st rs st'. ehacts lfd st xs = SOME (rs, st') ∧ EVERY (λx. ∀p. x ≠ EConnect p) xs ⇒
    EVERY (λr. new_hd r = NONE) rs
Proof
  Induct >> simp[ehacts_def] >> rw[] >> gvs[AllCaseEqs()] >>
  metis_tac[ehdo_new_hd]
QED

Theorem cupd_nh_same:
  ∀xs rs st. EVERY (λr. new_hd r = NONE) rs ⇒ (cupd rqs st xs rs).nh = st.nh
Proof
  Induct >> simp[cupd_def] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >>
  simp[cupd_def]
QED

Theorem cacts_upto_noconnect:
  ¬(st0.nh < cbound) ⇒ EVERY (λx. ∀p. x ≠ EConnect p) (MAP SND (cacts_upto a st0 rdy m))
Proof
  strip_tac >> simp[cacts_upto_def, MAP_FLAT, EVERY_FLAT, EVERY_GENLIST, EVERY_MAP] >>
  rw[] >> Cases_on ‘EL i st0.cs’ >> rw[cact1_def]
QED

Theorem crel_last[simp]:
  crel a N rqs lfd (st with last := x) = crel a N rqs lfd st
Proof
  simp[FUN_EQ_THM, crel_def]
QED

Theorem cacts_last[simp]:
  cacts a (st with last := x) rdy = cacts a st rdy
Proof
  simp[cacts_def]
QED

Theorem crel_round:
  crel a N rqs lfd st0 (K rdy) ps w hs ∧ st0.last = cacts a st0 rdy ∧
  N < cbound ∧ st0.nh < cbound + N ∧
  ehacts_tot lfd (w, hs) (MAP SND st0.last) = (rs, (w1, hs1)) ∧
  ehpoll lfd hs1 hfds w1 = (rdy', w2, hs2) ⇒
  ehacts lfd (w, hs) (MAP SND st0.last) = SOME (rs, (w1, hs1)) ∧
  crel a N rqs lfd (cstep a rqs st0 (ssnap rdy' rs)) (K (set rdy'))
    (ps ++ ZIP (MAP SND st0.last, rs)) w2 hs2 ∧
  (cstep a rqs st0 (ssnap rdy' rs)).last = cacts a (cstep a rqs st0 (ssnap rdy' rs)) (set rdy') ∧
  (cstep a rqs st0 (ssnap rdy' rs)).nh < cbound + N ∧ wkeep w w1
Proof
  strip_tac >> ‘LENGTH st0.cs = N’ by fs[crel_def] >>
  ‘N < dimword (:64) ∧ (st0.nh < cbound ⇒ st0.nh + N + 1 < dimword (:64))’
    by fs[cbound_def] >>
  drule crel_acts >> simp[] >> disch_then (qspec_then ‘N’ mp_tac) >> simp[] >> strip_tac >>
  ‘st0.last = cacts_upto a st0 rdy N’ by simp[cacts_upto_all] >>
  ‘ehacts lfd (w, hs) (MAP SND st0.last) = SOME (rs', (w1', hs1'))’ by simp[] >>
  ‘rs' = rs ∧ w1' = w1 ∧ hs1' = hs1’ by gvs[ehacts_tot_def] >> gvs[] >>
  simp[cstep_def, asyncM3WorldTheory.ssnap_def] >>
  conj_tac
  >- (‘crel a (LENGTH st0.cs) rqs lfd (cupd rqs st0 (cacts a st0 rdy) rs) (K ∅)
         (ps ++ ZIP (MAP SND (cacts a st0 rdy), rs)) w1 hs1’
        by (irule crel_rdyf >> qexists_tac ‘λi. if i < LENGTH st0.cs then ∅ else rdy’ >>
            conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
      drule_all crel_poll >> simp[]) >>
  Cases_on ‘st0.nh < cbound’
  >- simp[] >>
  ‘(cupd rqs st0 (cacts a st0 rdy) rs).nh = st0.nh’ suffices_by simp[] >>
  irule cupd_nh_same >> irule ehacts_new_hd >>
  metis_tac[cacts_upto_noconnect]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

(* The ready handles the client's state has seen last *)
Definition crdy_def:
  crdy (h : (word64, eresp) snapshot list) = if h = [] then ∅ else (LAST h).ready
End

(* The invariant at round n of the client's run in w0 *)
Definition cinv_def:
  cinv a N rqs lfd w0 n ⇔
    let h = ehhist lfd (cifds a N rqs) (cprog a N rqs) w0 n;
        st = cstate a N rqs h in
      crel a N rqs lfd st (K (crdy h)) (hl_pairs (cprog a N rqs) h)
        (FST (ehst lfd (cifds a N rqs) (cprog a N rqs) w0 n))
        (SND (ehst lfd (cifds a N rqs) (cprog a N rqs) w0 n)) ∧
      st.last = cacts a st (crdy h) ∧ st.nh < cbound + N
End

Theorem crel_init:
  client_world lfd c w0 ⇒ crel a N rqs lfd (cinit a N) (K ∅) [] w0 ehinit
Proof
  rw[client_world_def, crel_def, cinit_def, ehinit_def, endpointSpecFormsTheory.no_backpressure_def, EL_REPLICATE,
     chd_def] >>
  TRY (simp[FUN_EQ_THM] >> NO_TAC) >>
  Cases_on ‘i < N’ >> gvs[EL_REPLICATE, chd_def]
QED

Theorem cinv_0:
  client_world lfd c w0 ⇒ cinv a N rqs lfd w0 0
Proof
  strip_tac >> drule crel_init >>
  simp[cinv_def, ehhist_def, ehst_def, ehrounds_def, cstate_def, crdy_def, hl_pairs_def] >>
  simp[cinit_def, cbound_def, cacts_def]
QED

Theorem cinv_SUC:
  cinv a N rqs lfd w0 n ∧ N < cbound ⇒
  cinv a N rqs lfd w0 (SUC n) ∧
  ehacts lfd (ehst lfd (cifds a N rqs) (cprog a N rqs) w0 n)
    (new_actions (log_of (cprog a N rqs)) (ehhist lfd (cifds a N rqs) (cprog a N rqs) w0 n)) ≠ NONE
Proof
  qmatch_goalsub_abbrev_tac ‘ehst lfd ifds m w0 n’ >>
  simp[cinv_def] >> strip_tac >>
  qabbrev_tac ‘h = ehhist lfd ifds m w0 n’ >>
  qabbrev_tac ‘st = cstate a N rqs h’ >>
  Cases_on ‘ehst lfd ifds m w0 n’ >> rename1 ‘_ = (w, hs)’ >> fs[] >>
  ‘new_actions (log_of m) h = MAP SND st.last’ by simp[Abbr ‘m’, Abbr ‘st’, cprog_new_actions] >>
  Cases_on ‘ehacts_tot lfd (w, hs) (MAP SND st.last)’ >> rename1 ‘_ = (rs, st1)’ >>
  PairCases_on ‘st1’ >> rename1 ‘_ = (rs, (w1, hs1))’ >>
  Cases_on ‘ehpoll lfd hs1 (ifds h) w1’ >> rename1 ‘_ = (rdy', r2)’ >>
  PairCases_on ‘r2’ >> rename1 ‘_ = (rdy', w2, hs2)’ >>
  ‘ehhist lfd ifds m w0 (SUC n) = h ++ [ssnap rdy' rs] ∧ ehst lfd ifds m w0 (SUC n) = (w2, hs2)’
    by (qunabbrev_tac ‘h’ >> irule honestL1EPRefineTheory.ehround_step >> gvs[]) >>
  ‘st.nh < cbound + N’ by simp[] >>
  drule_all crel_round >> strip_tac >>
  simp[cstate_SNOC, crdy_def, hl_pairs_SNOC] >>
  fs[asyncM3WorldTheory.ssnap_def, Abbr ‘st’, crdy_def] >>
  qpat_x_assum ‘(cstate a N rqs h).last = _’ (fn th => fs[GSYM th])
QED

Theorem cinv_all:
  client_world lfd c w0 ∧ N < cbound ⇒ ∀n. cinv a N rqs lfd w0 n
Proof
  strip_tac >> Induct >- metis_tac[cinv_0] >> metis_tac[cinv_SUC]
QED
