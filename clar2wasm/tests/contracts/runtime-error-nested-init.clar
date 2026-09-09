;; Contract whose initialization raises a runtime error from within a local
;; call to a public function, leaving a nested context open.
(define-data-var counter uint u0)

(define-public (write-then-trap)
  (begin
    (var-set counter u1)
    (ok (/ 42 0))
  )
)

(write-then-trap)
