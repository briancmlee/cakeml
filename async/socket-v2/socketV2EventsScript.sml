(*
  The I/O events of «sock_poll» and «sock_close» against the version-2
  world, as the CakeML calls record them (socketV2Proof's specs) and as
  the handle-layer model predicts them (asyncHLModel).  Kept apart from
  the CF layer so that the model is plain HOL.
*)
Theory socketV2Events
Ancestors
  ffi ffiSpikeSocketFFI socketV2FFI
Libs
  preamble

(* The event of «sock_poll» on fds in state s *)
Definition spoll2_event_def:
  spoll2_event fds s =
    IO_event (ExtCall «sock_poll») (fds_bytes fds)
      (ZIP (REPLICATE (LENGTH fds) 0w,
            MAP (λfd. if is_ready2 (tick2 s) fd then 1w else 0w) fds))
End

(* The event of «sock_close» on c *)
Definition close_event_def:
  close_event c = IO_event (ExtCall «sock_close») (fd_bytes c) []
End
