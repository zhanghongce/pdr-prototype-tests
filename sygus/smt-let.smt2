(set-logic QF_BV)

(define-fun AllEq2
   ((A (_ BitVec 2))
    (B (_ BitVec 2))
    (C (_ BitVec 2))
   ) Bool
   (let ((c1 (= A B)))
    (let ((c2 (= B C)))
      (let ((c3 (and c1 c2)))
        c3
    )))
)

(define-fun INV ((A (_ BitVec 2)) (B (_ BitVec 2)) (C (_ BitVec 2))) Bool (not (= (bvadd #b11 A) C)))


(declare-fun a () (_ BitVec 2))
(declare-fun b () (_ BitVec 2))
(declare-fun c () (_ BitVec 2))

(assert (not (=> (AllEq2 a b c) (INV a b c))))
(check-sat)
