;; Calls into `runtime-error-nested` with `contract-call?`, so that the trap
;; happens in a nested `call_function`.
(define-public (call-trap)
  (contract-call? .runtime-error-nested call-trap)
)
