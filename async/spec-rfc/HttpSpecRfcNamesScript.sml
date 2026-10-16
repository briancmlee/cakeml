(*
  HttpSpecRfcNames: the names rfcAgree is stated with, against the REAL
  HttpSpec.  In the review's copy this theory added the tchar fix to
  HttpSpec; the real spec now has it (and the RFC character sets), so
  valid_brequest_t is just valid_brequest (valid_brequest_t_eq).
*)
Theory HttpSpecRfcNames
Ancestors
  HttpSpec HttpHeadersSpec HttpGetSpec
Libs
  preamble

Definition valid_bheader_t_def:
  valid_bheader_t (n, v) ⇔ valid_bheader (n, v) ∧ EVERY tchar n
End

Definition valid_brequest_t_def:
  valid_brequest_t (Req m p ver hs b) ⇔
    valid_brequest (Req m p ver hs b) ∧ EVERY valid_bheader_t hs
End

Theorem valid_brequest_t_eq:
  valid_brequest_t r ⇔ valid_brequest r
Proof
  Cases_on ‘r’ >> rw[valid_brequest_t_def, EQ_IMP_THM] >>
  fs[valid_brequest_def, EVERY_MEM, FORALL_PROD, valid_bheader_t_def] >>
  rpt strip_tac >> res_tac >> fs[valid_bheader_def, EVERY_MEM]
QED
