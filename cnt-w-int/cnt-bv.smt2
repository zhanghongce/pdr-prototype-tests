(set-option :fp.engine spacer)

(define-fun INIT ((base (_ BitVec 16)) (addr (_ BitVec 16)) (cnt (_ BitVec 16)) (inp (_ BitVec 16)) (en Bool)) Bool
    (and
        (= base #x0000)
        (= addr #x0000)
        (= cnt #x0000)
    )
)

(define-fun Tr (
    (base (_ BitVec 16)) (addr (_ BitVec 16)) (cnt (_ BitVec 16)) (inp (_ BitVec 16)) (en Bool)
    (basePrime (_ BitVec 16)) (addrPrime (_ BitVec 16)) (cntPrime (_ BitVec 16)) (inpPrime (_ BitVec 16)) (enPrime Bool))
    Bool
  (and
    (= basePrime (ite en inp base))
    (= addrPrime (ite en inp (bvadd addr #x0001)))
    (= cntPrime  (ite en #x0000 (bvadd cnt #x0001)))
  ))

(define-fun Prop ((base (_ BitVec 16)) (addr (_ BitVec 16)) (cnt (_ BitVec 16)) (inp (_ BitVec 16)) (en Bool)) Bool
    (not (and
        (= base #b0111011000000100)
        (= addr #b1101110001100111)
        (= cnt #b1101110001100111)
    ))
)


(declare-rel INV ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) Bool))
(declare-rel fail ())

(declare-var baseV (_ BitVec 16))
(declare-var addrV (_ BitVec 16))
(declare-var cntV  (_ BitVec 16))
(declare-var inpV  (_ BitVec 16))
(declare-var enV   Bool)

(declare-var baseP (_ BitVec 16))
(declare-var addrP (_ BitVec 16))
(declare-var cntP  (_ BitVec 16))
(declare-var inpP  (_ BitVec 16))
(declare-var enP   Bool)


; init => inv
(rule (=> 
  (INIT baseV addrV cntV inpV enV)
  (INV  baseV addrV cntV inpV enV)
))

; inv /\ T => inv
(rule (=> (and 
  (INV baseV addrV cntV inpV enV)  
  (Tr  baseV addrV cntV inpV enV
       baseP addrP cntP inpP enP)) 
  (INV baseP addrP cntP inpP enP)))

; inv /\ ~p => \bot
(rule (=> (and 
  (INV       baseV addrV cntV  inpV  enV)   
  (not (Prop baseV addrV cntV  inpV  enV)))
  fail))


(query fail :print-certificate true)
