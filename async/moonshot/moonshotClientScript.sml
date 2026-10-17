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
  asyncLevel1 asyncCore
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
    w'.open_fds = ADELKEY f w.open_fds ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox ≠ [] ∧
    r = EGot (SOME (TAKE n (EL j w.chans).inbox)) ∧ hs' = hs ∧ w'.open_fds = w.open_fds ∧
    EL j w'.chans = EL j w.chans with inbox := DROP n (EL j w.chans).inbox ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox = [] ∧
    ((EL j w.chans).peer_eof ∨ (EL j w.chans).status = Failed) ∧
    r = EGot (SOME []) ∧ hs' = eh_del hd hs ∧ w'.open_fds = ADELKEY f w.open_fds ∨
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
        (ch.status = Connecting ∧ sett ∧ ¬rd ∨
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
    ALL_DISTINCT (MAP FST hs.tbl) ∧
    ALL_DISTINCT (MAP FST w.open_fds) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
    EVERY (λj. j < LENGTH w.chans) (MAP SND w.open_fds) ∧
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
    (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ¬MEM hd (MAP FST hs.tbl)) ∧
    (∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps)) ∧
    (∀hd. (hl_refused hd ps ∨ hl_eof hd ps) ⇒ ∀i. i < N ⇒ ¬MEM hd (chd (EL i st.cs)))
End
