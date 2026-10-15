(*
  The Level 2 protocol server in the socket vocabulary (option C, design/33
  §2.2), for the HTTP instance (identity vocabulary, no queries): what
  srelabel2 of the handler and of the skeleton unfold to.  These are the
  library computations that the CakeML code of asyncOCProtoProg mirrors,
  as asyncProtoSockModel's sproto_handler_unfold is at Level 1.
*)
Theory asyncOCProtoModel
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 asyncServer
  asyncM3World asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  asyncServerV asyncProto asyncProtoV asyncProtoV2 asyncOCRelabel
Libs
  BasicProvers wordsLib

Theorem comp2_eq[local]:
  c1 = c2 ⇔ c1.run = c2.run ∧ c1.interest = c2.interest
Proof
  simp[DB.fetch "asyncLevel2" "comp2_component_equality"]
QED

(* Mapping the result of the first part of a bind2 *)
Theorem bind2_map2:
  bind2 (map2 g c) f = bind2 c (λx. f (g x))
Proof
  rw[comp2_eq, bind2_def, map2_def, bind_map] >>
  simp[FUN_EQ_THM, bind_interest_def, asyncLevel1Theory.map_def] >>
  qx_gen_tac ‘h’ >>
  ‘(λp. OPTION_MAP g (c.run p).result ≠ NONE) = (λp. (c.run p).result ≠ NONE)’
    by simp[FUN_EQ_THM] >>
  simp[] >> CASE_TAC >> simp[] >>
  ‘log_of (map g c.run) = log_of c.run’
    by simp[FUN_EQ_THM, log_of_def, asyncLevel1Theory.map_def] >>
  simp[] >> gvs[first_prefix_SOME] >>
  Cases_on ‘(c.run (TAKE x h)).result’ >> gvs[]
QED

Overload hproto2 = “λP resp p. proto_handler_v2 (idV : (asyncServer$action, unit, unit, asyncServer$response) vocab) P (K (NONE : unit option)) (λr (k : unit option). resp r) p”

(* MAIN: the HTTP-instance Level 2 handler, in the socket vocabulary *)
Theorem sproto_handler2_unfold:
  fd < dimword(:64) ⇒
  srelabel2 (hproto2 P resp (fd, buf)) =
    case P.parse buf of
      PComplete req rest =>
        bind2 (emit2 (asyncM3World$Write (n2w fd) (MAP (n2w o ORD) (resp req))))
              (λw. srelabel2 (hproto2 P resp (fd, rest)))
    | PIncomplete =>
        bind2 (wait_on (n2w fd) (λs. SOME ())) (λu.
        bind2 (emit2 (asyncM3World$Read (n2w fd) bufsz)) (λr.
          case r of
            Got (SOME bs) =>
              if bs = [] then return2 ()
              else srelabel2 (hproto2 P resp (fd, buf ++ MAP (CHR o w2n) bs))
          | _ => srelabel2 (hproto2 P resp (fd, buf))))
    | PInvalid => return2 ()
Proof
  strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [proto_handler_v2_unfold])) >>
  simp[proto_body_v2_def] >>
  Cases_on ‘P.parse buf’ >>
  simp[relabel2_bind2, relabel2_emit2, relabel2_return2, ie_ok_sie,
       srelabel2_wait_readable, bind2_map2, sfa_def, idV_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> simp[sfr_def])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >>
      rw[relabel2_return2, ie_ok_sie])
  >> simp[sfr_def]
QED

Overload idVu = “idV : (asyncServer$action, unit, unit, asyncServer$response) vocab”

(* MAIN: the Level 2 skeleton (identity vocabulary), in the socket
   vocabulary *)
Theorem sserver_v2_unfold:
  lfd < dimword(:64) ⇒
  srelabel2 (server_v2 idVu h2 lfd) =
    bind2 (wait_on (n2w lfd) (λs. SOME ())) (λu.
    bind2 (emit2 (asyncM3World$Accept (n2w lfd))) (λr.
      case r of
        asyncM3World$Accepted (SOME c) =>
          map2 (λp. ()) (both2 (srelabel2 (h2 (w2n c)))
                               (srelabel2 (server_v2 idVu h2 lfd)))
      | _ => srelabel2 (server_v2 idVu h2 lfd)))
Proof
  strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [server_v2_unfold])) >>
  simp[server_v_body2_def, relabel2_bind2, relabel2_emit2, ie_ok_sie,
       srelabel2_wait_readable, bind2_map2, sfa_def, idV_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >>
      simp[sfr_def, vaccd_def, relabel2_map2, relabel2_both2, ie_ok_sie])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def, vaccd_def] >> rw[vaccd_def])
  >> simp[sfr_def, vaccd_def]
QED
