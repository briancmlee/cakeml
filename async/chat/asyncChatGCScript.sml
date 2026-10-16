(*
  The chat hub with garbage collection (bounded memory).

  The hub of asyncChatModel keeps every complete line forever.  The GC hub
  keeps only the log from `base` on:
   - each connection has a cursor: where its writer last asked for the log
     from (Fetch i sets it to i), or its join position before that.  A
     writer asks for i only after it has written everything before i, so
     a cursor is how much of the log that client has been confirmed;
   - after every step the hub drops the log below the least cursor
     (collect), or all of it if no client is connected.

     gc_server lfd = with_tap gc_tap gc_delta empty_gstore (chat_inner lfd)

  The two hubs are related by gR (same buffers and joins, and the GC log is
  the full log from base on), whatever happens, except that the answers
  to Fetch i agree only if i ≥ base: the guard gc_guard.  With the guard,
  the GC invariant gc_inv holds, and so does the SPACE fact (gc_space):

     LENGTH st.glog = gend st − cmin st

  i.e. the hub holds exactly the bytes after the least cursor: the largest
  amount of the log any connected client has not yet confirmed.
*)
Theory asyncChatGC
Ancestors
  pair list rich_list arithmetic option string words alist
  asyncCore asyncLevel1 asyncServer asyncWithStore asyncWithTap
  asyncWithTapSim asyncChatSW asyncChatModel
Libs
  BasicProvers

Datatype:
  gstore = <| base : num                     (* log length dropped so far *)
            ; glog : string                  (* the log from base on *)
            ; gbufs : (word64 # string) list (* each connection's partial line *)
            ; gjoins : (word64 # num) list   (* log length when fd was accepted *)
            ; curs : (word64 # num) list     (* each connection's cursor *)
            |>
End

Definition empty_gstore_def:
  empty_gstore = <| base := 0; glog := ""; gbufs := []; gjoins := []; curs := [] |>
End

(* The length of the whole log (dropped and kept) *)
Definition gend_def:
  gend st = st.base + LENGTH st.glog
End

(* The least cursor (the end of the log if no client is connected) *)
Definition cmin_def:
  cmin st = FOLDR MIN (gend st) (MAP SND st.curs)
End

(* Drop the log below the least cursor *)
Definition collect_def:
  collect st =
    let nb = MIN (MAX st.base (cmin st)) (gend st) in
      st with <| base := nb; glog := DROP (nb − st.base) st.glog |>
End

Definition gbuf_of_def:
  gbuf_of st (w : word64) = case ALOOKUP st.gbufs w of SOME b => b | NONE => ""
End

(* The tap: as chat_tap; an accepted connection's cursor starts at its join
   position; then collect *)
Definition gc_tap0_def:
  gc_tap0 st a r =
    case (a, r) of
      (Read fd, Data s) =>
        (let t = gbuf_of st (n2w fd) ++ s;
             w = wls t
         in st with <| glog := st.glog ++ w;
                       gbufs := (n2w fd, DROP (LENGTH w) t) ::
                                FILTER (λp. FST p ≠ n2w fd) st.gbufs |>)
    | (Accept l, Accepted fd) =>
        st with <| gjoins := (n2w fd, gend st) :: st.gjoins;
                   curs := (n2w fd, gend st) :: st.curs |>
    | _ => st
End

Definition gc_tap_def:
  gc_tap st a r = collect (gc_tap0 st a r)
End

(* The queries: as chat_delta, on the kept log; a Fetch moves the cursor,
   then collect *)
Definition gc_delta_def:
  gc_delta st (q : num # cquery) =
    case SND q of
      Start => ((case ALOOKUP st.gjoins (n2w (FST q)) of
                   SOME j => Pos j | NONE => NotJoined), st)
    | Fetch i =>
        (Lines (DROP (i − st.base) st.glog),
         collect (st with curs := AFUPDKEY (n2w (FST q)) (K (MIN i (gend st))) st.curs))
End

Definition gc_server_def:
  gc_server lfd = with_tap gc_tap gc_delta empty_gstore (chat_inner lfd)
End

(* ------------------------------------------------------------------------
   The invariant and the relation to the full hub
   ------------------------------------------------------------------------ *)

(* Every cursor is between base and the end; base is the least cursor *)
Definition gc_inv_def:
  gc_inv st ⇔
    (∀c. MEM c (MAP SND st.curs) ⇒ st.base ≤ c ∧ c ≤ gend st) ∧
    st.base = cmin st
End

Definition gR_def:
  gR (a : cstore) b ⇔
    b.glog = DROP b.base a.log ∧ b.base ≤ LENGTH a.log ∧
    b.gbufs = a.bufs ∧ b.gjoins = a.joins ∧
    MAP FST b.curs = MAP FST b.gjoins ∧ gc_inv b
End

(* The guard: a Fetch asks for the log from at least base *)
Definition gc_guard_def:
  gc_guard st (q : num # cquery) ⇔ ∀i. SND q = Fetch i ⇒ st.base ≤ i
End

Theorem FOLDR_MIN_le[local]:
  ∀l d. FOLDR MIN d l ≤ d ∧ ∀c. MEM c l ⇒ FOLDR MIN d l ≤ c
Proof
  Induct >> rw[] >> fs[MIN_DEF] >> rw[] >>
  first_x_assum (qspec_then ‘d’ strip_assume_tac) >> res_tac >> simp[]
QED

Theorem FOLDR_MIN_ge[local]:
  ∀l d b. b ≤ d ∧ (∀c. MEM c l ⇒ b ≤ c) ⇒ b ≤ FOLDR MIN d l
Proof
  Induct >> rw[] >> fs[MIN_DEF] >> rw[]
QED

Theorem FOLDR_MIN_end[local]:
  ∀l d d'. d ≤ d' ∧ (∀c. MEM c l ⇒ c ≤ d) ⇒ FOLDR MIN d' l = FOLDR MIN d l ∨ l = []
Proof
  Induct >> rw[] >> fs[] >>
  first_x_assum (qspecl_then [‘d’, ‘d'’] mp_tac) >> simp[] >> strip_tac >>
  gvs[MIN_DEF] >> rw[] >> Cases_on ‘l’ >> gvs[MIN_DEF] >>
  qspecl_then [‘h'::t’, ‘d’] strip_assume_tac FOLDR_MIN_le >> fs[]
QED

(* collect, when every cursor is between base and the end *)
Theorem collect_thm:
  (∀c. MEM c (MAP SND st.curs) ⇒ st.base ≤ c ∧ c ≤ gend st) ⇒
  (collect st).base = cmin st ∧ gend (collect st) = gend st ∧
  (collect st).glog = DROP (cmin st − st.base) st.glog ∧
  (collect st).curs = st.curs ∧ (collect st).gjoins = st.gjoins ∧
  (collect st).gbufs = st.gbufs ∧ st.base ≤ cmin st ∧ cmin st ≤ gend st
Proof
  strip_tac >>
  ‘st.base ≤ cmin st ∧ cmin st ≤ gend st’
    by (simp[cmin_def] >> conj_tac
        >- (irule FOLDR_MIN_ge >> simp[gend_def])
        >> metis_tac[FOLDR_MIN_le]) >>
  ‘MIN (MAX st.base (cmin st)) (gend st) = cmin st’ by simp[MIN_DEF, MAX_DEF] >>
  simp[collect_def, gend_def] >> fs[gend_def]
QED

Theorem cmin_curs[local]:
  st'.curs = st.curs ∧ gend st ≤ gend st' ∧ st.curs ≠ [] ∧
  (∀c. MEM c (MAP SND st.curs) ⇒ c ≤ gend st) ⇒
  cmin st' = cmin st
Proof
  rw[cmin_def] >>
  qspecl_then [‘MAP SND st.curs’, ‘gend st’, ‘gend st'’] mp_tac FOLDR_MIN_end >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The simulation
   ------------------------------------------------------------------------ *)

Theorem gR_inv:
  gR a b ⇒ gend b = LENGTH a.log
Proof
  rw[gR_def, gend_def]
QED

Theorem gR_collect[local]:
  b.glog = DROP b.base L ∧ b.base ≤ LENGTH L ∧
  (∀c. MEM c (MAP SND b.curs) ⇒ b.base ≤ c ∧ c ≤ gend b) ⇒
  (collect b).glog = DROP (collect b).base L ∧ (collect b).base ≤ LENGTH L ∧
  gc_inv (collect b)
Proof
  strip_tac >> drule collect_thm >> strip_tac >>
  ‘gend b = LENGTH L’ by simp[gend_def] >>
  simp[DROP_DROP_T] >> rw[gc_inv_def]
  >- (fs[] >> first_x_assum drule >> simp[cmin_def] >>
      metis_tac[FOLDR_MIN_le])
  >- (fs[] >> first_x_assum drule >> simp[])
  >> simp[cmin_def] >> fs[cmin_def]
QED

Theorem gc_tap0_rel[local]:
  gR a b ⇒
  let B = gc_tap0 b x y; A = chat_tap a x y in
    B.glog = DROP B.base A.log ∧ B.base ≤ LENGTH A.log ∧
    (∀c. MEM c (MAP SND B.curs) ⇒ B.base ≤ c ∧ c ≤ gend B) ∧
    B.gbufs = A.bufs ∧ B.gjoins = A.joins ∧ MAP FST B.curs = MAP FST B.gjoins
Proof
  strip_tac >> fs[gR_def, gc_inv_def] >>
  qpat_x_assum ‘b.base = _’ kall_tac >>
  ‘gend b = LENGTH a.log ∧ b.base ≤ LENGTH a.log ∧ b.base − LENGTH a.log = 0’
    by simp[gend_def] >>
  Cases_on ‘x’ >> Cases_on ‘y’ >> simp[gc_tap0_def, chat_tap_def] >>
  simp[gend_def, gbuf_of_def, buf_of_def, DROP_APPEND] >>
  rw[] >> res_tac >> fs[gend_def]
QED

Theorem gc_sim_tap[local]:
  gR a b ⇒ gR (chat_tap a x y) (gc_tap b x y)
Proof
  strip_tac >>
  qspecl_then [‘a’, ‘b’, ‘x’, ‘y’] mp_tac (Q.GENL [‘a’, ‘b’, ‘x’, ‘y’] gc_tap0_rel) >>
  simp[] >>
  qabbrev_tac ‘B = gc_tap0 b x y’ >> qabbrev_tac ‘A = chat_tap a x y’ >>
  strip_tac >> simp[gc_tap_def] >>
  qspecl_then [‘B’, ‘A.log’] mp_tac (Q.GENL [‘b’, ‘L’] gR_collect) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_then strip_assume_tac collect_thm >>
  simp[gR_def, DROP_DROP_T]
QED

Theorem MAP_SND_AFUPDKEY[local]:
  ∀l. MEM c (MAP SND (AFUPDKEY k f l)) ⇒ MEM c (MAP SND l) ∨ ∃v. c = f v
Proof
  Induct >> simp[AFUPDKEY_def] >> PairCases >> rw[AFUPDKEY_def] >> fs[] >>
  metis_tac[]
QED

Theorem MAP_FST_AFUPDKEY_eq[local]:
  ∀l. MAP FST (AFUPDKEY k f l) = MAP FST l
Proof
  Induct >> simp[AFUPDKEY_def] >> PairCases >> rw[AFUPDKEY_def]
QED

Theorem gc_sim_delta[local]:
  gR a b ∧ gc_guard b q ⇒
  FST (chat_delta a q) = FST (gc_delta b q) ∧
  gR (SND (chat_delta a q)) (SND (gc_delta b q))
Proof
  PairCases_on ‘q’ >> Cases_on ‘q1’ >>
  simp[chat_delta_def, gc_delta_def, gc_guard_def] >> strip_tac >>
  fs[gR_def] >>
  simp[DROP_DROP_T] >>
  qmatch_goalsub_abbrev_tac ‘collect B’ >>
  ‘gend b = LENGTH a.log’ by simp[gend_def] >>
  ‘B.glog = DROP B.base a.log ∧ B.base ≤ LENGTH a.log ∧
   (∀c. MEM c (MAP SND B.curs) ⇒ B.base ≤ c ∧ c ≤ gend B)’
    by (simp[Abbr ‘B’, gend_def] >> rw[] >>
        drule MAP_SND_AFUPDKEY >> strip_tac >> gvs[gc_inv_def, gend_def] >>
        res_tac >> simp[]) >>
  drule_all gR_collect >> strip_tac >>
  drule_then strip_assume_tac collect_thm >>
  gvs[Abbr ‘B’, MAP_FST_AFUPDKEY_eq]
QED

Theorem gc_sim_ok:
  sim_ok gR gc_guard chat_tap chat_delta gc_tap gc_delta
Proof
  simp[sim_ok_def, gc_sim_tap, gc_sim_delta]
QED

Theorem gR_empty:
  gR empty_store empty_gstore
Proof
  simp[gR_def, empty_store_def, empty_gstore_def, gc_inv_def, cmin_def, gend_def]
QED

(* ------------------------------------------------------------------------
   Space
   ------------------------------------------------------------------------ *)

(* MAIN (space, store level): the GC hub holds exactly the bytes of the log
   after the least cursor (nothing if no client is connected) *)
Theorem gc_space:
  gc_inv st ⇒ LENGTH st.glog = gend st − cmin st
Proof
  rw[gc_inv_def, gend_def]
QED

Theorem gc_space_max:
  gc_inv st ∧ MEM (w, c) st.curs ⇒ gend st − c ≤ LENGTH st.glog
Proof
  rw[gc_inv_def, gend_def] >>
  ‘MEM c (MAP SND st.curs)’ by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  res_tac >> simp[]
QED
