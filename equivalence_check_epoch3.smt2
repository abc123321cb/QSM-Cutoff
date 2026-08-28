; Type and Relation Declarations
(declare-datatypes () ((node n0 n1)))

(declare-fun ep_epoch0(node) Bool)
(declare-fun ep_epoch1(node) Bool)
(declare-fun ep_epoch2(node) Bool)
(declare-fun held(node) Bool)
(declare-fun locked_epoch0(node) Bool)
(declare-fun locked_epoch1(node) Bool)
(declare-fun locked_epoch2(node) Bool)
(declare-fun transfer_epoch0(node) Bool)
(declare-fun transfer_epoch1(node) Bool)
(declare-fun transfer_epoch2(node) Bool)

; Orbit Group F1
(declare-const R0 Bool)
(assert (= R0 (forall ((NODE0 node)) (not (locked_epoch0 NODE0)))))
(declare-const R1 Bool)
(assert (= R1 (forall ((NODE0 node)) (not (locked_epoch1 NODE0)))))
(declare-const F1 Bool)
(assert (= F1 (and R0 R1)))

; Orbit Group F2
(declare-const R2 Bool)
(assert (= R2 (forall ((NODE0 node)) (not (transfer_epoch0 NODE0)))))
(declare-const R3 Bool)
(assert (= R3 (forall ((NODE0 node)) (not (transfer_epoch1 NODE0)))))
(declare-const F2 Bool)
(assert (= F2 (and R2 R3)))

; Orbit Group F3
(declare-const R5 Bool)
(assert (= R5 (forall ((NODE0 node)) (or (not (ep_epoch0 NODE0)) (not (ep_epoch1 NODE0))))))
(declare-const R6 Bool)
(assert (= R6 (forall ((NODE0 node)) (or (not (ep_epoch0 NODE0)) (not (ep_epoch2 NODE0))))))
(declare-const R10 Bool)
(assert (= R10 (forall ((NODE0 node)) (or (not (ep_epoch1 NODE0)) (not (ep_epoch2 NODE0))))))
(declare-const F3 Bool)
(assert (= F3 (and R5 R6 R10)))

; Orbit Group F4
(declare-const R7 Bool)
(assert (= R7 (forall ((NODE0 node)) (or (not (ep_epoch0 NODE0)) (not (held NODE0))))))
(declare-const F4 Bool)
(assert (= F4 R7))

; Orbit Group F5
(declare-const R8 Bool)
(assert (= R8 (forall ((NODE0 node)) (or (not (ep_epoch0 NODE0)) (not (locked_epoch2 NODE0))))))
(declare-const R11 Bool)
(assert (= R11 (forall ((NODE0 node)) (or (not (ep_epoch1 NODE0)) (not (locked_epoch2 NODE0))))))
(declare-const F5 Bool)
(assert (= F5 (and R8 R11)))

; Orbit Group F6
(declare-const R13 Bool)
(assert (= R13 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch2 NODE0)) (not (held NODE1)) (= NODE0 NODE1)))))
(declare-const F6 Bool)
(assert (= F6 R13))

; Orbit Group F7
(declare-const R14 Bool)
(assert (= R14 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch2 NODE0)) (not (locked_epoch2 NODE1)) (= NODE0 NODE1)))))
(declare-const F7 Bool)
(assert (= F7 R14))

; Orbit Group F8
(declare-const R15 Bool)
(assert (= R15 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch2 NODE0)) (not (transfer_epoch2 NODE1))))))
(declare-const F8 Bool)
(assert (= F8 R15))

;Orbit Group F9
(declare-const R16 Bool)
(assert (= R16 (forall ((NODE0 node)) (or (not (ep_epoch2 NODE0)) (held NODE0)))))
(declare-const F9 Bool)
(assert (= F9 R16))

;Orbit Group F10
(declare-const R17 Bool)
(assert (= R17 (forall ((NODE0 node)) (or (not (ep_epoch2 NODE0)) (locked_epoch2 NODE0)))))
(declare-const F10 Bool)
(assert (= F10 R17))

;Orbit Group F11
(declare-const R19 Bool)
(assert (= R19 (forall ((NODE0 node) (NODE1 node)) (or (not (held NODE0)) (not (locked_epoch2 NODE1)) (= NODE0 NODE1)))))
(declare-const F11 Bool)
(assert (= F11 R19))

;Orbit Group F12
(declare-const R20 Bool)
(assert (= R20 (forall ((NODE0 node) (NODE1 node)) (or (not (held NODE0)) (not (transfer_epoch2 NODE1))))))
(declare-const F12 Bool)
(assert (= F12 R20))

;Orbit Group F13
(declare-const R22 Bool)
(assert (= R22 (forall ((NODE0 node) (NODE1 node)) (or (not (locked_epoch2 NODE0)) (not (transfer_epoch2 NODE1))))))
(declare-const F13 Bool)
(assert (= F13 R22))

; Orbit Group F14
(declare-const R23 Bool)
(assert (= R23 (forall ((NODE0 node)) (or (not (locked_epoch2 NODE0)) (ep_epoch2 NODE0)))))
(declare-const F14 Bool)
(assert (= F14 R23))

; Orbit Group F15
(declare-const R24 Bool)
(assert (= R24 (forall ((NODE0 node)) (or (not (locked_epoch2 NODE0)) (held NODE0)))))
(declare-const F15 Bool)
(assert (= F15 R24))

; Orbit Group F16
(declare-const R26 Bool)
(assert (= R26 (forall ((NODE2 node) (NODE1 node) (NODE0 node)) (or (not (ep_epoch0 NODE0)) (not (transfer_epoch2 NODE1)) (ep_epoch1 NODE2) (and (or (not (= NODE0 NODE1)) (= NODE0 NODE2)) (or (not (= NODE1 NODE2)) (= NODE0 NODE1)))))))
(declare-const R33 Bool)
(assert (= R33 (forall ((NODE2 node) (NODE1 node) (NODE0 node)) (or (not (ep_epoch1 NODE0)) (not (transfer_epoch2 NODE1)) (ep_epoch0 NODE2) (and (or (not (= NODE1 NODE2)) (= NODE0 NODE1)) (or (not (= NODE0 NODE1)) (= NODE0 NODE2)))))))
(declare-const F16 Bool)
(assert (= F16 (and R26 R33)))

; Orbit Group F17
(declare-const R27 Bool)
(assert (= R27 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch0 NODE0)) (ep_epoch1 NODE1) (ep_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const R34 Bool)
(assert (= R34 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (ep_epoch0 NODE1) (ep_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const R37 Bool)
(assert (= R37 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch2 NODE0)) (ep_epoch0 NODE1) (ep_epoch1 NODE1) (= NODE0 NODE1)))))
(declare-const F17 Bool)
(assert (= F17 (and R27 R34 R37)))

; Orbit Group F18
(declare-const R28 Bool)
(assert (= R28 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch0 NODE0)) (ep_epoch1 NODE1) (held NODE1) (= NODE0 NODE1)))))
(declare-const R35 Bool)
(assert (= R35 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (ep_epoch0 NODE1) (held NODE1) (= NODE0 NODE1)))))
(declare-const F18 Bool)
(assert (= F18 (and R28 R35)))

; Orbit Group F19
(declare-const R29 Bool)
(assert (= R29 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch0 NODE0)) (ep_epoch1 NODE1) (locked_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const R36 Bool)
(assert (= R36 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (ep_epoch0 NODE1) (locked_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F19 Bool)
(assert (= F19 (and R29 R36)))

; Orbit Group F20
(declare-const R30 Bool)
(assert (= R30 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (not (held NODE0)) (ep_epoch0 NODE1) (= NODE0 NODE1)))))
(declare-const R31 Bool)
(assert (= R31 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (not (held NODE1)) (ep_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F20 Bool)
(assert (= F20 (and R30 R31)))

; Orbit Group F21
(declare-const R32 Bool)
(assert (= R32 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (not (held NODE1)) (locked_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F21 Bool)
(assert (= F21 R32))

; Orbit group F22
(declare-const R38 Bool)
(assert (= R38 (forall ((NODE0 node) (NODE1 node)) (or (not (held NODE0)) (ep_epoch0 NODE1) (ep_epoch1 NODE1) (= NODE0 NODE1)))))
(declare-const R39 Bool)
(assert (= R39 (forall ((NODE0 node) (NODE1 node)) (or (not (held NODE0)) (ep_epoch0 NODE1) (ep_epoch2 NODE0) (= NODE0 NODE1)))))
(declare-const F22 Bool)
(assert (= F22 (and R38 R39)))

; Orbit Group F23
(declare-const R40 Bool)
(assert (= R40 (forall ((NODE0 node) (NODE1 node)) (or (not (held NODE0)) (ep_epoch0 NODE1) (locked_epoch2 NODE0) (= NODE0 NODE1)))))
(declare-const F23 Bool)
(assert (= F23 R40))

; Orbit Group F24
(declare-const R41 Bool)
(assert (= R41 (forall ((NODE0 node)) (or (not (held NODE0)) (ep_epoch1 NODE0) (ep_epoch2 NODE0)))))
(declare-const F24 Bool)
(assert (= F24 R41))

; Orbit Group F25
(declare-const R42 Bool)
(assert (= R42 (forall ((NODE0 node)) (or (not (held NODE0)) (ep_epoch1 NODE0) (locked_epoch2 NODE0)))))
(declare-const F25 Bool)
(assert (= F25 R42))

; Orbit Group F26
(declare-const R43 Bool)
(assert (= R43 (forall ((NODE0 node) (NODE1 node)) (or (not (locked_epoch2 NODE0)) (ep_epoch0 NODE1) (ep_epoch1 NODE1) (= NODE0 NODE1)))))
(declare-const F26 Bool)
(assert (= F26 R43))

; Orbit Group F27
(declare-const R44 Bool)
(assert (= R44 (forall ((NODE0 node) (NODE1 node)) (or (not (transfer_epoch2 NODE0)) (ep_epoch0 NODE0) (ep_epoch0 NODE1) (= NODE0 NODE1)))))
(declare-const R45 Bool)
(assert (= R45 (forall ((NODE0 node) (NODE1 node)) (or (not (transfer_epoch2 NODE0)) (ep_epoch0 NODE1) (ep_epoch1 NODE1)))))
(declare-const R46 Bool)
(assert (= R46 (forall ((NODE0 node) (NODE1 node)) (or (not (transfer_epoch2 NODE0)) (ep_epoch1 NODE0) (ep_epoch1 NODE1) (= NODE0 NODE1)))))
(declare-const F27 Bool)
(assert (= F27 (and R44 R45 R46)))

; Orbit Group F28
(declare-const R47 Bool)
(assert (= R47 (forall ((NODE0 node)) (or (ep_epoch0 NODE0) (ep_epoch1 NODE0) (ep_epoch2 NODE0)))))
(declare-const F28 Bool)
(assert (= F28 R47))

; Orbit Group F29
(declare-const R48 Bool)
(assert (= R48 (forall ((NODE0 node)) (or (ep_epoch0 NODE0) (ep_epoch1 NODE0) (held NODE0)))))
(declare-const F29 Bool)
(assert (= F29 R48))

; Orbit Group F30
(declare-const R49 Bool)
(assert (= R49 (forall ((NODE0 node)) (or (ep_epoch0 NODE0) (ep_epoch1 NODE0) (locked_epoch2 NODE0)))))
(declare-const F30 Bool)
(assert (= F30 R49))

; Orbit Group F31
(declare-const R50 Bool)
(assert (= R50 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch0 NODE0)) (held NODE1) (transfer_epoch2 NODE0) (transfer_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F31 Bool)
(assert (= F31 R50))

; Orbit Group F32
(declare-const R53 Bool)
(assert (= R53 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch0 NODE0) (ep_epoch0 NODE1) (ep_epoch2 NODE1) (held NODE0) (= NODE0 NODE1)))))
(declare-const R59 Bool)
(assert (= R59 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch1 NODE0) (ep_epoch1 NODE1) (ep_epoch2 NODE1) (held NODE0) (= NODE0 NODE1)))))
(declare-const F32 Bool)
(assert (= F32 (and R53 R59)))

; Orbit Group F33
(declare-const R54 Bool)
(assert (= R54 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch0 NODE0) (ep_epoch0 NODE1) (ep_epoch2 NODE1) (locked_epoch2 NODE0) (= NODE0 NODE1)))))
(declare-const R60 Bool)
(assert (= R60 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch1 NODE0) (ep_epoch1 NODE1) (ep_epoch2 NODE0) (locked_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F33 Bool)
(assert (= F33 (and R54 R60)))

; Orbit Group F34
(declare-const R56 Bool)
(assert (= R56 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch0 NODE0) (ep_epoch0 NODE1) (held NODE0) (locked_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const R62 Bool)
(assert (= R62 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch1 NODE0) (ep_epoch1 NODE1) (held NODE0) (locked_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F34 Bool)
(assert (= F34 (and R56 R62)))

; Orbit Group F35
(declare-const R65 Bool)
(assert (= R65 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (ep_epoch2 NODE1) (held NODE0) (transfer_epoch2 NODE0) (transfer_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F35 Bool)
(assert (= F35 R65))

; Orbit Group F36
(declare-const R66 Bool)
(assert (= R66 (forall ((NODE0 node) (NODE1 node)) (or (not (ep_epoch1 NODE0)) (held NODE0) (locked_epoch2 NODE1) (transfer_epoch2 NODE0) (transfer_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F36 Bool)
(assert (= F36 R66))

; Orbit Group F37
(declare-const R67 Bool)
(assert (= R67 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch0 NODE0) (ep_epoch2 NODE1) (held NODE0) (transfer_epoch2 NODE0) (transfer_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const R69 Bool)
(assert (= R69 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch1 NODE0) (ep_epoch2 NODE0) (held NODE1) (transfer_epoch2 NODE0) (transfer_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F37 Bool)
(assert (= F37 (and R67 R69)))

; Orbit Group F38
(declare-const R68 Bool)
(assert (= R68 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch0 NODE0) (held NODE0) (locked_epoch2 NODE1) (transfer_epoch2 NODE0) (transfer_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const R70 Bool)
(assert (= R70 (forall ((NODE0 node) (NODE1 node)) (or (ep_epoch1 NODE0) (held NODE1) (locked_epoch2 NODE0) (transfer_epoch2 NODE0) (transfer_epoch2 NODE1) (= NODE0 NODE1)))))
(declare-const F38 Bool)
(assert (= F38 (and R68 R70)))

; Orbit Group E1
(declare-const R4 Bool)
(assert (= R4 (exists ((NODE0 node)) (not (ep_epoch0 NODE0)))))
(declare-const R9 Bool)
(assert (= R9 (exists ((NODE0 node)) (not (ep_epoch1 NODE0)))))
(declare-const R12 Bool)
(assert (= R12 (exists ((NODE0 node)) (not (ep_epoch2 NODE0)))))
(declare-const E1 Bool)
(assert (= E1 (and R4 R9 R12)))

; Orbit Group E2
(declare-const R18 Bool)
(assert (= R18 (exists ((NODE0 node)) (not (held NODE0)))))
(declare-const E2 Bool)
(assert (= E2 R18))

; Orbit Group E3
(declare-const R21 Bool)
(assert (= R21 (exists ((NODE0 node)) (not (locked_epoch2 NODE0)))))
(declare-const E3 Bool)
(assert (= E3 R21))

; Orbit Group E4
(declare-const R25 Bool)
(assert (= R25 (exists ((NODE0 node)) (not (transfer_epoch2 NODE0)))))
(declare-const E4 Bool)
(assert (= E4 R25))

; Orbit Group E5
(declare-const R51 Bool)
(assert (= R51 (exists ((NODE0 node)) (or (ep_epoch0 NODE0) (ep_epoch1 NODE0)))))
(declare-const R52 Bool)
(assert (= R52 (exists ((NODE0 node)) (or (ep_epoch0 NODE0) (ep_epoch2 NODE0)))))
(declare-const R58 Bool)
(assert (= R58 (exists ((NODE0 node)) (or (ep_epoch1 NODE0) (ep_epoch2 NODE0)))))
(declare-const E5 Bool)
(assert (= E5 (and R51 R52 R58)))

; Orbit Groiup E6
(declare-const R55 Bool)
(assert (= R55 (exists ((NODE0 node)) (or (ep_epoch0 NODE0) (held NODE0)))))
(declare-const R61 Bool)
(assert (= R61 (exists ((NODE0 node)) (or (ep_epoch1 NODE0) (held NODE0)))))
(declare-const E6 Bool)
(assert (= E6 (and R55 R61)))

; Orbit Group E7
(declare-const R57 Bool)
(assert (= R57 (exists ((NODE0 node)) (or (ep_epoch0 NODE0) (locked_epoch2 NODE0)))))
(declare-const R63 Bool)
(assert (= R63 (exists ((NODE0 node)) (or (ep_epoch1 NODE0) (locked_epoch2 NODE0)))))
(declare-const E7 Bool)
(assert (= E7 (and R57 R63)))

; Orbit Group E8
(declare-const R64 Bool)
(assert (= R64 (exists ((NODE0 node)) (or (held NODE0) (transfer_epoch2 NODE0)))))
(declare-const E8 Bool)
(assert (= E8 R64))


; Truth table
; Variables are declared, in order of truth table columns, on lines 5 to 14
; Truth table row should be declared as S1, S2, ..., S10.
; Disjunction of the 10 rows is declared as S 
;
;01010010000000000000
;10001001000000000000
;01010000000000000010
;10001000000000000001
;00110010000010000000
;10000101000001000000
;01010000000000000001
;10001000000000000010
;01000101000001000000
;00101010000010000000
;; State definitions based on the truth table rows [cite: 28, 29]
;; Variable order: ep_epoch0..2(n0), ep_epoch0..2(n1), held(n0/n1), locked_epoch0..2(n0/n1), transfer_epoch0..2(n0/n1)

(define-fun S1 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
  ))
(define-fun S2 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
  ))
(define-fun S3 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (transfer_epoch2 n0)
    (not (transfer_epoch2 n1))
  ))
(define-fun S4 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (transfer_epoch2 n1)
  ))
(define-fun S5 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
  ))
(define-fun S6 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
  ))
(define-fun S7 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (transfer_epoch2 n1)
  ))
(define-fun S8 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (transfer_epoch2 n0)
    (not (transfer_epoch2 n1))
  ))
(define-fun S9 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
  ))
(define-fun S10 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (not (locked_epoch1 n1))
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
  ))

	
;; Disjunction of all states
(define-fun S () Bool
  (or S1 S2 S3 S4 S5 S6 S7 S8 S9 S10))

; R Formula
(declare-const R Bool)
(assert (= R (and
F1
F2
F3
F4 
F5
F6
F7
F8
F9
F10
F11
F12
F13
F14
F15
F16
F17
F18
F19
F20
F21
F22
F23
F24
F25
F26
F27
F28
F29
F30
F31
F32
F33
F34
F35
F36
F37
F38
E1 E2 E3 E4 E5 E6 E7 E8)))

; Check equivalence
(assert (not (= R S)))
(check-sat)
(get-model)