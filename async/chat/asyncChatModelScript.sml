(*
  The chat server in the async model.

     chat_server lfd = with_tap chat_tap chat_delta empty_store
                         (cserver_with chat_handler lfd)
     chat_handler fd = both (reader fd) (writer fd)

  - The hub is the store of with_tap: the log of all complete lines, in
    the order they were read, plus each connection's partial line and the
    log position at which each connection was accepted (keyed by the
    connection as a 64-bit word, as the socket world's fds are, so that
    the socket-level tap is literally the same function).  It is updated by
    the TAP (chat_tap), which sees every read and every accept in the
    order the world performed them: so the log is, by construction, the
    lines in the order the server completed reading them.
  - reader fd: read fd forever (until EOF); the data goes to the tap.
  - writer fd: ask the hub where fd joined (Start), then forever ask for
    the log from its position (Fetch i), and write what is new.

  Every entry of a handler's transcript is about its own fd
  (chat_handler_on_fdc), so the generic cserver_with lemmas apply.
*)
Theory asyncChatModel
Ancestors
  pair list rich_list arithmetic option pred_set string words alist
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncWithStore asyncWithTap asyncChatSW
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Lines and the order of completion, on model transcripts
   ------------------------------------------------------------------------ *)

(* The complete lines at the front of s (up to and including its last
   newline) *)
Definition wls_def:
  wls (s : string) = REVERSE (dropWhile (λc. c ≠ #"\n") (REVERSE s))
End

(* The lines that the entry p, after the entries pre, completes *)
Definition comp_def:
  comp pre (p : action # response option) =
    case p of
      (Read fd, SOME (Data s)) =>
        DROP (LENGTH (wls (CONCAT (read fd pre))))
             (wls (CONCAT (read fd pre) ++ s))
    | _ => ""
End

(* All lines completed in a transcript, in order *)
Definition lines_done_def:
  lines_done tr = FLAT (GENLIST (λk. comp (TAKE k tr) (EL k tr)) (LENGTH tr))
End

(* ------------------------------------------------------------------------
   The hub
   ------------------------------------------------------------------------ *)

Datatype:
  cstore = <| log : string                  (* complete lines, in order *)
            ; bufs : (word64 # string) list (* each connection's partial line *)
            ; joins : (word64 # num) list   (* log length when fd was accepted *)
            |>
End

Datatype:
  cquery = Start | Fetch num
End

Datatype:
  canswer = Pos num | NotJoined | Lines string
End

Definition empty_store_def:
  empty_store = <| log := ""; bufs := []; joins := [] |>
End

Definition buf_of_def:
  buf_of st (w : word64) = case ALOOKUP st.bufs w of SOME b => b | NONE => ""
End

(* The tap: complete lines are appended on a read; the join position is
   recorded on an accept *)
Definition chat_tap_def:
  chat_tap st a r =
    case (a, r) of
      (Read fd, Data s) =>
        (let t = buf_of st (n2w fd) ++ s;
             w = wls t
         in st with <| log := st.log ++ w;
                       bufs := (n2w fd, DROP (LENGTH w) t) ::
                               FILTER (λp. FST p ≠ n2w fd) st.bufs |>)
    | (Accept l, Accepted fd) =>
        st with joins := (n2w fd, LENGTH st.log) :: st.joins
    | _ => st
End

(* The queries: where did fd join; the log from position i *)
Definition chat_delta_def:
  chat_delta st (q : num # cquery) =
    case SND q of
      Start => ((case ALOOKUP st.joins (n2w (FST q)) of
                   SOME j => Pos j | NONE => NotJoined), st)
    | Fetch i => (Lines (DROP i st.log), st)
End

(* ------------------------------------------------------------------------
   The handler and the server
   ------------------------------------------------------------------------ *)

Definition reader_body_def:
  reader_body r fd =
    bind (readable fd) (λu.
    bind (emit (Sock (Read fd))) (λres.
      case res of
        SockR Eof => return ()
      | _ => r fd))
End

Theorem reader_body_contractive:
  contractive reader_body
Proof
  rw[contractive_def, reader_body_def]
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> gen_tac >> every_case_tac >> simp[nonexpansive_call, nonexpansive_const]
QED

Definition reader_def:
  reader = fix reader_body
End

Theorem reader_unfold:
  reader fd =
    bind (readable fd) (λu.
    bind (emit (Sock (Read fd))) (λres.
      case res of
        SockR Eof => return ()
      | _ => reader fd))
Proof
  simp[reader_def, Once (MATCH_MP fix_unfold reader_body_contractive)] >>
  simp[reader_body_def]
QED

Definition wloop_body_def:
  wloop_body r p =
    case p of
      (fd, i) =>
        bind (emit (Kv (fd, Fetch i))) (λa.
          case a of
            KvR (Lines s) =>
              if s = "" then r (fd, i)
              else bind (emit (Sock (Write fd s))) (λw. r (fd, i + LENGTH s))
          | _ => return ())
End

Theorem wloop_body_contractive:
  contractive wloop_body
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[wloop_body_def] >>
  ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot] >>
  gen_tac >> every_case_tac >> simp[nonexpansive_const, nonexpansive_call] >>
  ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const, nonexpansive_call]
QED

Definition wloop_def:
  wloop = fix wloop_body
End

Theorem wloop_unfold:
  wloop (fd, i) =
    bind (emit (Kv (fd, Fetch i))) (λa.
      case a of
        KvR (Lines s) =>
          if s = "" then wloop (fd, i)
          else bind (emit (Sock (Write fd s))) (λw. wloop (fd, i + LENGTH s))
      | _ => return ())
Proof
  simp[wloop_def, Once (MATCH_MP fix_unfold wloop_body_contractive)] >>
  simp[wloop_body_def]
QED

Definition writer_def:
  writer fd =
    bind (emit (Kv (fd, Start))) (λa.
      case a of
        KvR (Pos j) => wloop (fd, j)
      | _ => return ())
End

Definition chat_handler_def:
  chat_handler fd = map (λp. ()) (both (reader fd) (writer fd))
End

Definition chat_inner_def:
  chat_inner lfd = cserver_with chat_handler lfd
End

Definition chat_server_def:
  chat_server lfd = with_tap chat_tap chat_delta empty_store (chat_inner lfd)
End

(* ------------------------------------------------------------------------
   Well-formed and settled
   ------------------------------------------------------------------------ *)

Theorem wf_reader:
  wf (reader fd)
Proof
  simp[reader_def] >> irule wf_fix >> simp[reader_body_contractive] >>
  rw[reader_body_def] >>
  irule wf_bind >> simp[readable_def, wf_wait] >>
  irule wf_bind >> simp[wf_emit] >> gen_tac >> every_case_tac >> simp[wf_return]
QED

Theorem settled_reader:
  settled (reader fd)
Proof
  simp[reader_def] >> irule settled_fix >> simp[reader_body_contractive] >>
  rw[reader_body_def] >>
  irule settled_bind >> simp[readable_def, wf_wait, settled_wait] >>
  irule settled_bind >> simp[wf_emit, settled_emit] >> gen_tac >>
  every_case_tac >> simp[settled_return]
QED

Theorem wf_wloop:
  wf (wloop p)
Proof
  simp[wloop_def] >> irule wf_fix >> simp[wloop_body_contractive] >>
  rw[] >> PairCases_on ‘p’ >> simp[wloop_body_def] >>
  irule wf_bind >> simp[wf_emit] >> gen_tac >> every_case_tac >>
  simp[wf_return] >> irule wf_bind >> simp[wf_emit]
QED

Theorem settled_wloop:
  settled (wloop p)
Proof
  simp[wloop_def] >> irule settled_fix >> simp[wloop_body_contractive] >>
  rw[] >> PairCases_on ‘p’ >> simp[wloop_body_def] >>
  irule settled_bind >> simp[wf_emit, settled_emit] >> gen_tac >>
  every_case_tac >> simp[settled_return] >>
  irule settled_bind >> simp[wf_emit, settled_emit]
QED

Theorem wf_writer:
  wf (writer fd)
Proof
  simp[writer_def] >> irule wf_bind >> simp[wf_emit] >> gen_tac >>
  every_case_tac >> simp[wf_return, wf_wloop]
QED

Theorem settled_writer:
  settled (writer fd)
Proof
  simp[writer_def] >> irule settled_bind >> simp[wf_emit, settled_emit] >>
  gen_tac >> every_case_tac >> simp[settled_return, settled_wloop]
QED

Theorem wf_chat_handler:
  wf (chat_handler fd)
Proof
  simp[chat_handler_def] >> irule wf_map >> irule wf_both >>
  simp[wf_reader, wf_writer]
QED

Theorem settled_chat_handler:
  settled (chat_handler fd)
Proof
  simp[chat_handler_def] >> irule settled_map >> irule settled_both >>
  simp[wf_reader, wf_writer, settled_reader, settled_writer]
QED

Theorem wf_chat_inner:
  wf (chat_inner lfd)
Proof
  simp[chat_inner_def] >> irule wf_cserver_with >> simp[wf_chat_handler]
QED

Theorem wf_chat_server:
  wf (chat_server lfd)
Proof
  simp[chat_server_def] >> irule wf_with_tap >> simp[wf_chat_inner]
QED
