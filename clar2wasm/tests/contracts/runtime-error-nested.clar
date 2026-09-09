;; Contract used to check that the host unwinds the nested contexts that a
;; runtime error (a Wasm trap) leaves open. A local call to a public function
;; opens a nested context (`begin_public_call`) that the Wasm code closes with
;; `commit_call`/`roll_back_call`, but a trap skips that close.

(define-data-var counter uint u0)

(define-read-only (get-counter)
  (var-get counter)
)

;; Writes to the data var and then raises a runtime error.
(define-public (write-then-trap)
  (begin
    (var-set counter u1)
    (ok (/ 42 0))
  )
)

;; Leaves one nested context open.
(define-public (call-trap)
  (write-then-trap)
)

;; Leaves two nested contexts open.
(define-public (call-call-trap)
  (call-trap)
)

;; `as-contract` opens a nested context too (`enter_as_contract`).
(define-public (as-contract-trap)
  (as-contract (write-then-trap))
)
