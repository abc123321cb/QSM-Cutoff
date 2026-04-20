; Declare node type
(declare-datatypes () ((node n0 n1)))

; Declare the relations
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
(assert (= R0 (forall ((N node)) (not (locked_epoch0 N)))))
(declare-const R1 Bool)
(assert (= R1 (forall ((N node)) (not (locked_epoch1 N)))))
(declare-const F1 Bool)
(assert (= F1 (and R0 R1)))

; Orbit Group F2
(declare-const R2 Bool)
(assert (= R2 (forall ((N node)) (not (transfer_epoch0 N)))))
(declare-const R3 Bool)
(assert (= R3 (forall ((N node)) (not (transfer_epoch1 N)))))
(declare-const F2 Bool)
(assert (= F2 (and R2 R3)))

; Orbit Group F3
(declare-const R5 Bool)
(assert (= R5 (forall ((N node)) (or (not (ep_epoch0 N)) (not (ep_epoch1 N))))))
(declare-const R6 Bool)
(assert (= R6 (forall ((N node)) (or (not (ep_epoch0 N)) (not (ep_epoch2 N))))))
(declare-const R10 Bool)
(assert (= R10 (forall ((N node)) (or (not (ep_epoch1 N)) (not (ep_epoch2 N))))))
(declare-const F3 Bool)
(assert (= F3 (and R5 R6 R10)))

; Orbit Group F4
(declare-const R7 Bool)
(assert (= R7 (forall ((N node)) (or (not (ep_epoch0 N)) (not (held N))))))
(declare-const F4 Bool)
(assert (= F4 R7))

; Orbit Group F5
(declare-const R8 Bool)
(assert (= R8 (forall ((N node)) (or (not (ep_epoch0 N)) (not (locked_epoch2 N))))))
(declare-const R11 Bool)
(assert (= R11 (forall ((N node)) (or (not (ep_epoch1 N)) (not (locked_epoch2 N))))))
(declare-const F5 Bool)
(assert (= F5 (and R8 R11)))

; Orbit Group F6
(declare-const R13 Bool)
(assert (= R13 (forall ((N1 node) (N0 node)) (or (not (ep_epoch2 N0)) (not (held N1)) (= N0 N1)))))
(declare-const F6 Bool)
(assert (= F6 R13))

; Orbit Group F7
(declare-const R14 Bool)
(assert (= R14 (forall ((N1 node) (N0 node)) (or (not (ep_epoch2 N0)) (not (locked_epoch2 N1)) (= N0 N1)))))
(declare-const F7 Bool)
(assert (= F7 R14))

; Orbit Group F8
(declare-const R15 Bool)
(assert (= R15 (forall ((N1 node) (N0 node)) (or (not (ep_epoch2 N0)) (not (transfer_epoch2 N1))))))
(declare-const F8 Bool)
(assert (= F8 R15))

; Orbit Group F9
(declare-const R16 Bool)
(assert (= R16 (forall ((N node)) (or (not (ep_epoch2 N)) (held N)))))
(declare-const F9 Bool)
(assert (= F9 R16))

; Orbit Group F10
(declare-const R17 Bool)
(assert (= R17 (forall ((N node)) (or (not (ep_epoch2 N)) (locked_epoch2 N)))))
(declare-const F10 Bool)
(assert (= F10 R17))

; Orbit Group F11
(declare-const R19 Bool)
(assert (= R19 (forall ((N1 node) (N0 node)) (or (not (held N0)) (not (locked_epoch2 N1)) (= N0 N1)))))
(declare-const F11 Bool)
(assert (= F11 R19))

; Orbit Group F12
(declare-const R20 Bool)
(assert (= R20 (forall ((N1 node) (N0 node)) (or (not (held N0)) (not (transfer_epoch2 N1))))))
(declare-const F12 Bool)
(assert (= F12 R20))

; Orbit Group F13
(declare-const R22 Bool)
(assert (= R22 (forall ((N1 node) (N0 node)) (or (not (locked_epoch2 N0)) (not (transfer_epoch2 N1))))))
(declare-const F13 Bool)
(assert (= F13 R22))

; Orbit Group F14
(declare-const R23 Bool)
(assert (= R23 (forall ((N node)) (or (not (locked_epoch2 N)) (ep_epoch2 N)))))
(declare-const F14 Bool)
(assert (= F14 R23))

; Orbit Group F15
(declare-const R24 Bool)
(assert (= R24 (forall ((N node)) (or (not (locked_epoch2 N)) (held N)))))
(declare-const F15 Bool)
(assert (= F15 R24))

; Orbit Group E1
(declare-const R4 Bool)
(assert (= R4 (exists ((N node)) (not (locked_epoch0 N)))))
(declare-const R9 Bool)
(assert (= R9 (exists ((N node)) (not (locked_epoch1 N)))))
(declare-const R12 Bool)
(assert (= R12 (exists ((N node)) (not (locked_epoch2 N)))))
(declare-const E1 Bool)
(assert (= E1 (and R4 R9 R12)))

; Orbit Group E2
(declare-const R18 Bool)
(assert (= R18 (exists ((N node)) (not (held N)))))
(declare-const E2 Bool)
(assert (= E2 R18))

; Orbit Group E3
(declare-const R21 Bool)
(assert (= R21 (exists ((N node)) (not (locked_epoch2 N)))))
(declare-const E3 Bool)
(assert (= E3 R21))

; Orbit Group E4
(declare-const R25 Bool)
(assert (= R25 (exists ((N node)) (not (transfer_epoch2 N)))))
(declare-const E4 Bool)
(assert (= E4 R25))

; Orbit Group E5
(declare-const R51 Bool)
(assert (= R51 (exists ((N node)) (or (ep_epoch0 N) (ep_epoch1 N)))))
(declare-const R52 Bool)
(assert (= R52 (exists ((N node)) (or (ep_epoch0 N) (ep_epoch2 N)))))
(declare-const R58 Bool)
(assert (= R58 (exists ((N node)) (or (ep_epoch1 N) (ep_epoch2 N)))))
(declare-const E5 Bool)
(assert (= E5 (and R51 R52 R58)))

; Orbit Group E6
(declare-const R55 Bool)
(assert (= R55 (exists ((N node)) (or (ep_epoch0 N) (held N)))))
(declare-const R61 Bool)
(assert (= R61 (exists ((N node)) (or (ep_epoch1 N) (held N)))))
(declare-const E6 Bool)
(assert (= E6 (and R55 R61)))

; Orbit Group E7
(declare-const R57 Bool)
(assert (= R57 (exists ((N node)) (or (ep_epoch0 N) (locked_epoch2 N)))))
(declare-const R63 Bool)
(assert (= R63 (exists ((N node)) (or (ep_epoch1 N) (locked_epoch2 N)))))
(declare-const E7 Bool)
(assert (= E7 (and R57 R63)))

; Orbit Group E8
(declare-const R64 Bool)
(assert (= R64 (exists ((N node)) (or (held N) (transfer_epoch2 N)))))
(declare-const E8 Bool)
(assert (= E8 R64))

; R Formula
(declare-const R Bool)
(assert (= R (and F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 E1 E2 E3 E4 E5 E6 E7 E8)))

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
  (and (not (ep_epoch0 n0)) (ep_epoch1 n0) (not (ep_epoch2 n0)) (ep_epoch0 n1) (not (ep_epoch1 n1)) (not (ep_epoch2 n1)) (held n0) (not (held n1)) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (not (transfer_epoch2 n1))))

(define-fun S2 () Bool
  (and (ep_epoch0 n0) (not (ep_epoch1 n0)) (not (ep_epoch2 n0)) (not (ep_epoch0 n1)) (ep_epoch1 n1) (not (ep_epoch2 n1)) (not (held n0)) (held n1) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (not (transfer_epoch2 n1))))

(define-fun S3 () Bool
  (and (not (ep_epoch0 n0)) (ep_epoch1 n0) (not (ep_epoch2 n0)) (ep_epoch0 n1) (not (ep_epoch1 n1)) (not (ep_epoch2 n1)) (not (held n0)) (not (held n1)) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (transfer_epoch1 n1) (not (transfer_epoch2 n1))))

(define-fun S4 () Bool
  (and (ep_epoch0 n0) (not (ep_epoch1 n0)) (not (ep_epoch2 n0)) (not (ep_epoch0 n1)) (ep_epoch1 n1) (not (ep_epoch2 n1)) (not (held n0)) (not (held n1)) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (transfer_epoch2 n1)))

(define-fun S5 () Bool
  (and (not (ep_epoch0 n0)) (not (ep_epoch1 n0)) (ep_epoch2 n0) (ep_epoch0 n1) (not (ep_epoch1 n1)) (not (ep_epoch2 n1)) (held n0) (not (held n1)) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (locked_epoch0 n1) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (not (transfer_epoch2 n1))))

(define-fun S6 () Bool
  (and (ep_epoch0 n0) (not (ep_epoch1 n0)) (not (ep_epoch2 n0)) (not (ep_epoch0 n1)) (not (ep_epoch1 n1)) (ep_epoch2 n1) (not (held n0)) (held n1) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (locked_epoch1 n1) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (not (transfer_epoch2 n1))))

(define-fun S7 () Bool
  (and (not (ep_epoch0 n0)) (ep_epoch1 n0) (not (ep_epoch2 n0)) (ep_epoch0 n1) (not (ep_epoch1 n1)) (not (ep_epoch2 n1)) (not (held n0)) (not (held n1)) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (transfer_epoch2 n1)))

(define-fun S8 () Bool
  (and (ep_epoch0 n0) (not (ep_epoch1 n0)) (not (ep_epoch2 n0)) (not (ep_epoch0 n1)) (ep_epoch1 n1) (not (ep_epoch2 n1)) (not (held n0)) (not (held n1)) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (transfer_epoch1 n1) (not (transfer_epoch2 n1))))

(define-fun S9 () Bool
  (and (not (ep_epoch0 n0)) (ep_epoch1 n0) (not (ep_epoch2 n0)) (not (ep_epoch0 n1)) (not (ep_epoch1 n1)) (ep_epoch2 n1) (not (held n0)) (held n1) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (not (locked_epoch0 n1)) (locked_epoch1 n1) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (not (transfer_epoch2 n1))))

(define-fun S10 () Bool
  (and (not (ep_epoch0 n0)) (not (ep_epoch1 n0)) (ep_epoch2 n0) (not (ep_epoch0 n1)) (ep_epoch1 n1) (not (ep_epoch2 n1)) (held n0) (not (held n1)) (not (locked_epoch0 n0)) (not (locked_epoch1 n0)) (not (locked_epoch2 n0)) (locked_epoch0 n1) (not (locked_epoch1 n1)) (not (locked_epoch2 n1)) (not (transfer_epoch0 n0)) (not (transfer_epoch1 n0)) (not (transfer_epoch2 n0)) (not (transfer_epoch0 n1)) (not (transfer_epoch1 n1)) (not (transfer_epoch2 n1))))
	
;; Disjunction of all states
(define-fun S () Bool
  (or S1 S2 S3 S4 S5 S6 S7 S8 S9 S10))

; Check equivalence
(assert (not (= R S)))
(check-sat)
(get-model)