(*
  The concurrent echo server in CakeML, written with the library's
  combinators (asyncCfActProg, asyncCfActBoth), mirroring the model's
  definitions (async/model/asyncServerScript.sml):

     fun handler fd =
       bind (readable fd) (fn u =>
       bind (emit (Read fd)) (fn res =>
         case res of
           Data d => bind (emit (Write fd d)) (fn w => handler fd)
         | Eof => return ()
         | _ => handler fd));

     fun server lfd =
       bind (readable lfd) (fn u =>
       bind (emit (Accept lfd)) (fn res =>
         case res of
           Accepted fd => map (fn p => ()) (both (handler fd) (server lfd))
         | _ => server lfd));

  Recursion is ordinary CakeML recursion.  The calls are guarded: each
  recursive call sits in a continuation of bind, which bind only calls
  after a poll.

  The model's event, action and response types are used as CakeML
  datatypes as they are (register_type), and the ready set of a snapshot is
  a CakeML list of events (EVENTS).  This theory has the code and the specs
  of its helpers (readable, map); the specs of handler and server are in
  asyncM4ServerSpec.
*)
Theory asyncM4ServerProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActBothModel asyncCfActProg asyncCfActSpec asyncCfActBoth
  asyncM4Approx ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfActBoth"

(* ------------------------------------------------------------------------
   The model's types, as CakeML datatypes
   ------------------------------------------------------------------------ *)

val _ = register_type “:asyncServer$event”;
val _ = register_type “:asyncServer$action”;
val _ = register_type “:asyncServer$response”;

(* Is the event Readable fd in the list? *)
Definition has_readable_def:
  (has_readable fd [] ⇔ F) ∧
  (has_readable fd (e :: es) ⇔ e = Readable fd ∨ has_readable fd es)
End

val r = translate has_readable_def;

Theorem has_readable_MEM:
  ∀es. has_readable fd es ⇔ MEM (Readable fd) es
Proof
  Induct >> simp[has_readable_def] >> metis_tac[]
QED

(* EVENTS s v: v is a CakeML list of events whose set is the ready set s *)
Definition EVENTS_def:
  EVENTS s v ⇔ ∃es. s = set es ∧ LIST_TYPE ASYNCSERVER_EVENT_TYPE es v
End

(* ------------------------------------------------------------------------
   The CakeML code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun readable fd =
    wait (fn w => case w of (rdy, t, res) =>
      if has_readable fd rdy then Some () else None);

  fun map f c = bind c (fn x => return (f x));

  fun handler fd =
    bind (readable fd) (fn u =>
    bind (emit (Read fd)) (fn res =>
      case res of
        Data d => bind (emit (Write fd d)) (fn w => handler fd)
      | Eof => return ()
      | _ => handler fd));

  fun server lfd =
    bind (readable lfd) (fn u =>
    bind (emit (Accept lfd)) (fn res =>
      case res of
        Accepted fd => map (fn p => ()) (both (handler fd) (server lfd))
      | _ => server lfd));
End

(* ------------------------------------------------------------------------
   Specs of the helpers
   ------------------------------------------------------------------------ *)

(* readable fd implements the model's readable fd: it finishes, with (),
   at the first snapshot whose ready set contains Readable fd. *)
Theorem readable_spec:
  NUM fd fdv ⇒
  app (p:'ffi ffi_proj) readable_v [fdv] emp
    (POSTv v. &COMP p ACT UNIT_TYPE (SNAPSHOT EVENTS R) (readable fd) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "readable_v_def") >> xfun ‘f’ >>
  simp[readable_def] >> xapp_spec wait_spec >> simp[returns_def] >>
  rpt strip_tac >>
  qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def, EVENTS_def] >> xmatch >>
  xlet ‘POSTv bv. &BOOL (has_readable fd es) bv’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xif >> rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
  gvs[has_readable_MEM, std_preludeTheory.OPTION_TYPE_def]
QED

(* map f c implements the model's map f m, up to any depth n *)
Theorem map_spec_d:
  wf m ∧ COMPd p ACT A (SNAPSHOT READY R) n m mv ∧
  (∀x xv. A x xv ⇒ returns p fv [xv] (B (f x))) ⇒
  app (p:'ffi ffi_proj) map_v [fv; mv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B
                (SNAPSHOT READY (R : 'r -> v -> bool)) n (map f m) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "map_v_def") >> xfun ‘g’ >>
  ‘∀x xv. A x xv ⇒
     returns p g [xv] (COMPd p ACT B (SNAPSHOT READY R) n (return (f x)))’
    by (rpt strip_tac >> simp[returns_def] >>
        qpat_x_assum ‘curried _ _ g ∧ _’ (irule o CONJUNCT2) >>
        xlet ‘POSTv yv. &B (f x) yv’
        >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
        ‘app p return_v [yv] emp
           (POSTv v. &COMP p ACT B (SNAPSHOT READY R) (return (f x)) v)’
          by (irule return_spec >> simp[]) >>
        qpat_x_assum ‘app _ return_v _ _ _’ xapp_spec >> xsimpl >>
        simp[COMP_IMP_COMPd]) >>
  ‘app p bind_v [mv; g] emp
     (POSTv v. &COMPd p ACT B (SNAPSHOT READY R) n
                 (bind m (λx. return (f x))) v)’
    by (irule bind_spec_d >> simp[] >> metis_tac[]) >>
  simp[map_as_bind] >> qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl
QED
