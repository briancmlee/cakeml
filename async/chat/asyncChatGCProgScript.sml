(*
  The chat server with the garbage-collecting hub, in CakeML: asyncChatProg's
  program (with_tap, the handler and the skeleton are unchanged), plus the
  GC hub (asyncChatGC) translated, and

     fun gc_server lfd =
       with_tap gc_tap_s gdelta3 empty_gstore (cserver_with chandler lfd);

  The GC store is a CakeML record value of the translated gstore type: its
  glog field is a list of exactly LENGTH st.glog characters (gc_value_size).
*)
Theory asyncChatGCProg
Ancestors
  asyncCore asyncLevel1 asyncServer asyncM3World asyncM4SockModel
  asyncWithStore asyncWithTap asyncChatSW asyncChatModel asyncChatSafe
  asyncChatGC asyncChatProg ml_translator mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncChatProg"

(* ------------------------------------------------------------------------
   The GC hub, translation-friendly
   ------------------------------------------------------------------------ *)

Definition minl_def:
  minl (d : num) [] = d ∧
  minl d (x :: xs) = (let m = minl d xs in if x < m then x else m)
End

Theorem minl_thm[local]:
  ∀l d. minl d l = FOLDR MIN d l
Proof
  Induct >> rw[minl_def, MIN_DEF]
QED

Definition upd_cur_def:
  upd_cur (w : word64) (v : num) [] = [] ∧
  upd_cur w v ((k, c) :: l) = if w = k then (w, v) :: l else (k, c) :: upd_cur w v l
End

Theorem upd_cur_thm[local]:
  ∀l. upd_cur w v l = AFUPDKEY w (K v) l
Proof
  Induct >> simp[upd_cur_def, alistTheory.AFUPDKEY_def] >> PairCases >>
  rw[upd_cur_def, alistTheory.AFUPDKEY_def]
QED

Definition gcollect_def:
  gcollect st =
    let e = st.base + LENGTH st.glog;
        m = minl e (MAP SND st.curs);
        nb1 = (if st.base < m then m else st.base);
        nb = (if nb1 < e then nb1 else e)
    in st with <| base := nb; glog := drop2 (nb − st.base) st.glog |>
End

Theorem gcollect_thm:
  gcollect st = collect st
Proof
  simp[gcollect_def, collect_def, cmin_def, gend_def, minl_thm, drop2_thm,
       MIN_DEF, MAX_DEF] >>
  qabbrev_tac ‘X = FOLDR MIN (STRLEN st.glog + st.base) (MAP SND st.curs)’ >>
  Cases_on ‘st.base < X’ >> Cases_on ‘X < STRLEN st.glog + st.base’ >>
  Cases_on ‘STRLEN st.glog = 0’ >> simp[]
QED

Definition gtap_read_def:
  gtap_read st (fd : num) (s : string) =
    gcollect
      (let t = gbuf_of st (n2w fd) ++ s;
           w = wls2 t
       in st with <| glog := st.glog ++ w;
                     gbufs := (n2w fd, drop2 (LENGTH w) t) ::
                              FILTER (λp. FST p ≠ n2w fd) st.gbufs |>)
End

Definition gtap_accept_def:
  gtap_accept st (fd : num) =
    gcollect (st with <| gjoins := (n2w fd, st.base + LENGTH st.glog) :: st.gjoins;
                         curs := (n2w fd, st.base + LENGTH st.glog) :: st.curs |>)
End

Definition gdelta2_def:
  gdelta2 st (q : num # cquery) =
    case SND q of
      Start => ((case ALOOKUP st.gjoins (n2w (FST q)) of
                   SOME j => Pos j | NONE => NotJoined), st)
    | Fetch i =>
        (let e = st.base + LENGTH st.glog in
           (Lines (drop2 (if st.base ≤ i then i − st.base else 0) st.glog),
            gcollect (st with curs := upd_cur (n2w (FST q)) (if i < e then i else e) st.curs)))
End

Theorem gtap_read_thm:
  gc_tap st (Read fd) (Data s) = gtap_read st fd s
Proof
  simp[gc_tap_def, gc_tap0_def, gtap_read_def, gcollect_thm, wls2_thm, drop2_thm]
QED

Theorem gtap_accept_thm:
  gc_tap st (Accept l) (Accepted fd) = gtap_accept st fd
Proof
  simp[gc_tap_def, gc_tap0_def, gtap_accept_def, gcollect_thm, gend_def]
QED

Theorem gtap_other_thm:
  (∀fd s. a = Read fd ⇒ r ≠ Data s) ∧ (∀l fd. a = Accept l ⇒ r ≠ Accepted fd) ⇒
  gc_tap st a r = gcollect st
Proof
  simp[gc_tap_def, gc_tap0_def, gcollect_thm] >> Cases_on ‘a’ >> Cases_on ‘r’ >> simp[]
QED

Theorem gdelta2_thm:
  gdelta2 = gc_delta
Proof
  simp[FUN_EQ_THM, gdelta2_def, gc_delta_def, drop2_thm, gcollect_thm, upd_cur_thm,
       gend_def] >>
  rpt gen_tac >> PairCases_on ‘x'’ >> Cases_on ‘x'1’ >> rw[MIN_DEF] >> fs[] >>
  qmatch_goalsub_abbrev_tac ‘DROP (nn − bb) _’ >>
  ‘nn − bb = 0’ by (unabbrev_all_tac >> decide_tac) >> simp[]
QED

val _ = register_type “:gstore”;
val r = translate minl_def;
val r = translate upd_cur_def;
val r = translate gbuf_of_def;
val r = translate gcollect_def;
val r = translate gtap_read_def;
val r = translate gtap_accept_def;
val r = translate gdelta2_def;
val r = translate empty_gstore_def;

Definition gtap_read_t_def:
  gtap_read_t (st, fd, s) = gtap_read st fd s
End

Definition gtap_accept_t_def:
  gtap_accept_t (st, fd) = gtap_accept st fd
End

Definition gdelta2_t_def:
  gdelta2_t (st, q) = gdelta2 st q
End

val r = translate gtap_read_t_def;
val r = translate gtap_accept_t_def;
val r = translate gdelta2_t_def;

(* ------------------------------------------------------------------------
   The tap on socket actions, the server
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun gc_tap_s st a r =
    case a of
      Read c n =>
        (case r of
           Got (Some s) =>
             if s = "" then gcollect st else gtap_read_t (st, (c, String.explode s))
         | _ => gcollect st)
    | Accept l =>
        (case r of
           Accepted (Some c) => gtap_accept_t (st, c)
         | _ => gcollect st)
    | _ => gcollect st;

  fun gdelta3 st q = gdelta2_t (st, q);

  fun gc_server lfd =
    with_tap gc_tap_s gdelta3 empty_gstore (cserver_with chandler lfd);
End
