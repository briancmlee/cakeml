(*
  The chat server in CakeML, in M3/M4's program (extending
  asyncM4SockServer, whose sreadable and Async library it reuses).

  - with_tap (generic in the tap sigma and the query step delta): the pure
    effect handler of asyncWithTap.  The store is an argument of the
    residual's closure, passed on round by round; no refs:

       fun wt_res sigma delta st acts s =
         case s of
           Done x => Done x
         | Pending k => Pending (fn (rdy, t, rs) =>
             case wt_run sigma delta st acts rs of (bs, st2) =>
             case k (rdy, t, wt_merge acts rs bs) of (acts2, s2) =>
               (wt_socks acts2, wt_res sigma delta st2 acts2 s2));

  - the hub: chat_tap_s and chat_delta, translated from the model's
    definitions (the tap's core on the store record, plus a short wrapper
    on socket actions and responses);
  - the reader, the write loop, the writer, the handler and the skeleton,
    mirroring asyncChatSockModel's unfolding equations, in the vocabulary
    Sock sact | Kv (fd, query).
*)
Theory asyncChatProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer asyncWithStore asyncWithTap asyncWithTapStep
  asyncChatSW asyncChatModel asyncChatSafe asyncChatSockModel
  ml_translator mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM4SockServer"

(* ------------------------------------------------------------------------
   The hub
   ------------------------------------------------------------------------ *)

(* Translation-friendly versions of wls and DROP *)
Definition wls2_def:
  wls2 [] = "" ∧
  wls2 (c :: cs) =
    let r = wls2 cs in
    if r = "" then (if c = #"\n" then [c] else "") else c :: r
End

Theorem wls_sing1[local]:
  wls [c] = if c = #"\n" then [c] else ""
Proof
  rw[wls_def]
QED

Theorem wls_EQ_NIL[local]:
  ∀s. wls s = "" ⇔ ¬MEM #"\n" s
Proof
  Induct_on ‘s’ using SNOC_INDUCT >- simp[wls_def] >>
  rw[SNOC_APPEND, asyncChatSafeTheory.wls_APPEND, wls_sing1] >> metis_tac[]
QED

Theorem wls_CONS[local]:
  wls (h :: s) =
    if MEM #"\n" s then h :: wls s else if h = #"\n" then [h] else ""
Proof
  ‘h :: s = [h] ++ s’ by simp[] >> pop_assum (fn th => REWRITE_TAC[Once th]) >>
  REWRITE_TAC[asyncChatSafeTheory.wls_APPEND] >> rw[wls_sing1]
QED

Theorem wls2_thm:
  ∀s. wls2 s = wls s
Proof
  Induct >- simp[wls2_def, wls_def] >>
  rw[wls2_def, wls_CONS] >> gvs[wls_EQ_NIL]
QED

Definition drop2_def:
  drop2 (n : num) [] = [] ∧
  drop2 n (x :: xs) = if n = 0 then x :: xs else drop2 (n - 1) xs
End

Theorem drop2_thm:
  ∀n l. drop2 n l = DROP n l
Proof
  Induct_on ‘l’ >> rw[drop2_def]
QED

(* The tap's two cases and the query step, on simple types *)
Definition tap_read_def:
  tap_read st (fd : num) (s : string) =
    let t = buf_of st (n2w fd) ++ s;
        w = wls2 t
    in st with <| log := st.log ++ w;
                  bufs := (n2w fd, drop2 (LENGTH w) t) ::
                          FILTER (λp. FST p ≠ n2w fd) st.bufs |>
End

Definition tap_accept_def:
  tap_accept st (fd : num) = st with joins := (n2w fd, LENGTH st.log) :: st.joins
End

Definition delta2_def:
  delta2 st (q : num # cquery) =
    case SND q of
      Start => ((case ALOOKUP st.joins (n2w (FST q)) of
                   SOME j => Pos j | NONE => NotJoined), st)
    | Fetch i => (Lines (drop2 i st.log), st)
End

Theorem tap_read_thm:
  chat_tap st (Read fd) (Data s) = tap_read st fd s
Proof
  simp[chat_tap_def, tap_read_def, wls2_thm, drop2_thm]
QED

Theorem tap_accept_thm:
  chat_tap st (Accept l) (Accepted fd) = tap_accept st fd
Proof
  simp[chat_tap_def, tap_accept_def]
QED

Theorem delta2_thm:
  delta2 = chat_delta
Proof
  simp[FUN_EQ_THM, delta2_def, chat_delta_def, drop2_thm]
QED

val _ = register_type “:cstore”;
val _ = register_type “:cquery”;
val _ = register_type “:canswer”;
val r = translate wls2_def;
val r = translate drop2_def;
val r = translate buf_of_def;
Definition tap_read_t_def:
  tap_read_t (st, fd, s) = tap_read st fd s
End

Definition tap_accept_t_def:
  tap_accept_t (st, fd) = tap_accept st fd
End

Definition delta2_t_def:
  delta2_t (st, q) = delta2 st q
End

val r = translate tap_read_def;
val r = translate tap_accept_def;
val r = translate delta2_def;
val r = translate tap_read_t_def;
val r = translate tap_accept_t_def;
val r = translate delta2_t_def;
val r = translate empty_store_def;

(* A monomorphic length, so that the CF proof needs no type instantiation *)
Definition clen_def:
  clen (s : string) = LENGTH s
End
val r = translate clen_def;

(* ------------------------------------------------------------------------
   with_tap
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  datatype ('a, 'q) kact = Sock 'a | Kv 'q;
  datatype ('r, 'b) kres = Sockr 'r | Kvr 'b;

  fun wt_run sigma delta st acts rs =
    case acts of
      [] => ([], st)
    | a :: rest =>
        (case a of
           Sock x =>
             (case rs of
                [] => wt_run sigma delta st rest []
              | r :: rs1 => wt_run sigma delta (sigma st x r) rest rs1)
         | Kv q =>
             (case delta st q of
                (b, st1) =>
                  (case wt_run sigma delta st1 rest rs of
                     (bs, st2) => (b :: bs, st2))));

  fun wt_merge acts rs ans =
    case acts of
      [] => []
    | a :: rest =>
        (case a of
           Sock x =>
             (case rs of [] => [] | r :: rs1 => Sockr r :: wt_merge rest rs1 ans)
         | Kv q =>
             (case ans of [] => [] | b :: ans1 => Kvr b :: wt_merge rest rs ans1));

  fun wt_socks acts =
    case acts of
      [] => []
    | a :: rest =>
        (case a of Sock x => x :: wt_socks rest | Kv q => wt_socks rest);

  fun wt_res sigma delta st acts s =
    case s of
      Done x => Done x
    | Pending k =>
        Pending (fn w =>
          case w of
            (rdy, t, rs) =>
              (case wt_run sigma delta st acts rs of
                 (bs, st2) =>
                   (case k (rdy, t, wt_merge acts rs bs) of
                      (acts2, s2) =>
                        (wt_socks acts2, wt_res sigma delta st2 acts2 s2))));

  fun with_tap sigma delta st c =
    case c of (acts, s) => (wt_socks acts, wt_res sigma delta st acts s);
End

(* ------------------------------------------------------------------------
   The tap on socket actions, the server
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun chat_tap_s st a r =
    case a of
      Read c n =>
        (case r of
           Got (Some s) => if s = "" then st else tap_read_t (st, (c, String.explode s))
         | _ => st)
    | Accept l =>
        (case r of
           Accepted (Some c) => tap_accept_t (st, c)
         | _ => st)
    | _ => st;

  fun delta3 st q = delta2_t (st, q);

  fun cserver_with h lfd =
    Async.bind (sreadable lfd) (fn u =>
    Async.bind (Async.emit (Sock (Accept lfd))) (fn r =>
      case r of
        Sockr (Accepted (Some c)) =>
          async_map (fn p => ()) (async_both (h c) (cserver_with h lfd))
      | _ => cserver_with h lfd));

  fun creader fd =
    Async.bind (sreadable fd) (fn u =>
    Async.bind (Async.emit (Sock (Read fd 4096))) (fn r =>
      case r of
        Sockr (Got (Some s)) =>
          if s = "" then Async.return () else creader fd
      | _ => creader fd));

  fun cwloop fd i =
    Async.bind (Async.emit (Kv (fd, Fetch i))) (fn a =>
      case a of
        Kvr b =>
          (case b of
             Lines s =>
               (case s of
                  [] => cwloop fd i
                | c :: cs =>
                    Async.bind (Async.emit (Sock (Write fd (String.implode s))))
                      (fn w => cwloop fd (i + clen s)))
           | _ => Async.return ())
      | _ => Async.return ());

  fun cwriter fd =
    Async.bind (Async.emit (Kv (fd, Start))) (fn a =>
      case a of
        Kvr b =>
          (case b of
             Pos j => cwloop fd j
           | _ => Async.return ())
      | _ => Async.return ());

  fun chandler fd = async_map (fn p => ()) (async_both (creader fd) (cwriter fd));

  fun chat_server lfd =
    with_tap chat_tap_s delta3 empty_store (cserver_with chandler lfd);
End
