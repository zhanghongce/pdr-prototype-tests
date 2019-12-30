(set-option :fp.engine spacer)

; assuming 16 bits, so 0~(65536-1)

(define-fun INIT ((base Int) (addr Int) (cnt Int) (inp Int) (en Bool)) Bool
    (and
        (= base 0)
        (= addr 0)
        (= cnt 0)
    )
)

(define-fun Tr (
    (base Int) (addr Int) (cnt Int) (inp Int) (en Bool)
    (basePrime Int) (addrPrime Int) (cntPrime Int) (inpPrime Int) (enPrime Bool))
    Bool
  (and
    (= basePrime (ite en inp base))
    (= addrPrime (ite en inp (ite (= (+ addr 1) 65536) 0 (+ addr 1))))
    (= cntPrime  (ite en 0 (ite (= (+ cnt 1) 65536) 0 (+ cnt 1))))
  ))

(define-fun Prop ((base Int) (addr Int) (cnt Int) (inp Int) (en Bool)) Bool
    (and
        (>= base 0)
        (>= addr 0)
        (>= cnt 0)
        (< base 65536)
        (< addr 65536)
        (< cnt 65536)
        (= addr (ite (>= (+ base cnt) 65536) (- (+ base cnt) 65536) (+ base cnt)))
    )
)

(define-fun InputAssumption ((base Int) (addr Int) (cnt Int) (inp Int) (en Bool)) Bool
    (and
        (or (> inp 0) (= inp 0))
        (< inp 65536)
    )
)

(declare-rel INV (Int Int Int Int Bool))
(declare-rel fail ())

(declare-var baseV Int)
(declare-var addrV Int)
(declare-var cntV  Int)
(declare-var inpV  Int)
(declare-var enV   Bool)

(declare-var baseP Int)
(declare-var addrP Int)
(declare-var cntP  Int)
(declare-var inpP  Int)
(declare-var enP   Bool)


; init => inv
(rule (=> 
  (INIT baseV addrV cntV inpV enV)
  (INV  baseV addrV cntV inpV enV)
))

; inv /\ T => inv
(rule (=> (and 
  (INV baseV addrV cntV inpV enV)  
  (InputAssumption 
       baseV addrV cntV inpV enV)
  (Tr  baseV addrV cntV inpV enV
       baseP addrP cntP inpP enP)) 
  (INV baseP addrP cntP inpP enP)))

; inv /\ ~p => \bot
(rule (=> (and 
  (INV       baseV addrV cntV  inpV  enV)   
  (not (Prop baseV addrV cntV  inpV  enV)))
  fail))


(query fail :print-certificate true)
