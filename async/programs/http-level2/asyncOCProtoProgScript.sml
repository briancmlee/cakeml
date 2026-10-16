(*
  The generic protocol server at Level 2, in CakeML (option C, design/33
  §2.2): cf-actions' proto_handler / sserver_with / proto_server
  (asyncProtoProg), written with the Level 2 library
  (asyncOCProg), so that each declares what it waits for:

     fun sreadable2 fd =
       wait_on fd (fn w => case w of (rdy, t, res) =>
         if has_fd fd rdy then Some () else None);

     fun proto_handler2 parse respond fd buf =
       case parse buf of
         Pcomplete r rest =>
           bind2 (emit2 (Write fd (String.implode (respond r))))
                 (fn w => proto_handler2 parse respond fd rest)
       | Pincomplete =>
           bind2 (sreadable2 fd) (fn u =>
           bind2 (emit2 (Read fd 4096)) (fn r =>
             case r of
               Got (Some s) =>
                 if s = "" then return2 ()
                 else proto_handler2 parse respond fd (buf @ String.explode s)
             | _ => proto_handler2 parse respond fd buf))
       | Pinvalid => return2 ();

     fun sserver2 h lfd =
       bind2 (sreadable2 lfd) (fn u =>
       bind2 (emit2 (Accept lfd)) (fn r =>
         case r of
           Accepted (Some c) => map2 (fn p => ()) (both2 (h c) (sserver2 h lfd))
         | _ => sserver2 h lfd));

     fun proto_server2 parse respond lfd =
       sserver2 (fn fd => proto_handler2 parse respond fd []) lfd;

  The declared events are fds (ints), related to the model's word64 events
  by SEV.
*)
Theory asyncOCProtoProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 asyncServer
  asyncCfActModel asyncCfActProg asyncM3World asyncM3Loop asyncM4SockServer
  asyncOCModel asyncOCProg asyncOCSpec asyncOCApprox asyncProtoProg
  ml_translator mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncOCProg"

Quote add_cakeml:
  fun sreadable2 fd =
    wait_on fd (fn w => case w of (rdy, t, res) =>
      if has_fd fd rdy then Some () else None);

  fun proto_handler2 parse respond fd buf =
    case parse buf of
      Pcomplete r rest =>
        bind2 (emit2 (Write fd (String.implode (respond r))))
              (fn w => proto_handler2 parse respond fd rest)
    | Pincomplete =>
        bind2 (sreadable2 fd) (fn u =>
        bind2 (emit2 (Read fd 4096)) (fn r =>
          case r of
            Got (Some s) =>
              if s = "" then return2 ()
              else proto_handler2 parse respond fd (buf @ String.explode s)
          | _ => proto_handler2 parse respond fd buf))
    | Pinvalid => return2 ();

  fun sserver2 h lfd =
    bind2 (sreadable2 lfd) (fn u =>
    bind2 (emit2 (Accept lfd)) (fn r =>
      case r of
        Accepted (Some c) => map2 (fn p => ()) (both2 (h c) (sserver2 h lfd))
      | _ => sserver2 h lfd));

  fun proto_server2 parse respond lfd =
    sserver2 (fn fd => proto_handler2 parse respond fd []) lfd;
End

(* The declared events: socket fds, as CakeML ints *)
Definition SEV_def:
  SEV (c : word64) v ⇔ NUM (w2n c) v
End

Theorem MEM_MAP_w2n[local]:
  MEM fd (MAP w2n (fds:word64 list)) ⇔ ∃c. MEM c fds ∧ w2n c = fd
Proof
  simp[MEM_MAP] >> metis_tac[]
QED

(* sreadable2 fd declares fd and waits until it is ready *)
Theorem sreadable2_spec:
  NUM fd fdv ∧ fd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) sreadable2_v [fdv] emp
    (POSTv v. &COMPI p SACT UNIT_TYPE SEV SSNAP (wait_on (n2w fd) (λs. SOME ())) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "sreadable2_v_def") >> xfun ‘f’ >>
  ‘∀w wv. SSNAP w wv ⇒
     returns p f [wv]
       (OPTION_TYPE UNIT_TYPE (if n2w fd ∈ w.ready then SOME () else NONE))’
    by (rpt strip_tac >> simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        gvs[SNAPSHOT_def, SREADY_def] >> xmatch >>
        xlet ‘POSTv bv. &BOOL (MEM fd (MAP w2n fds)) bv’
        >- (xapp_spec has_fd_spec >> metis_tac[]) >>
        ‘MEM fd (MAP w2n fds) ⇔ MEM (n2w fd) fds’
          by (simp[MEM_MAP_w2n] >> eq_tac >> rw[] >> gvs[n2w_w2n] >>
              qexists_tac ‘n2w fd’ >> simp[w2n_n2w]) >>
        xif >> rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
        gvs[] >> rw[OPTION_TYPE_def] >> fs[UNIT_TYPE_def]) >>
  xapp_spec wait_on_specI >> simp[SEV_def, w2n_n2w] >>
  qexists_tac ‘λs. SOME ()’ >> simp[] >> metis_tac[]
QED
