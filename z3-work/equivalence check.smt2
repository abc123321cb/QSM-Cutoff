; Declare node type
(declare-datatypes () ((node n0 n1)))

; Declare the relations
(declare-fun x(node) Bool)
(declare-fun y(node) Bool)

; Declare labels for the invariants and assert their conjunction
(declare-const R1 Bool)
(declare-const R2 Bool)
(declare-const R3 Bool)
(declare-const R Bool)
(assert (= R (and R1 R2 R3)))

; Define the invariants
(assert (= R1 (exists ((N node)) (not (y N)))))
(assert (= R2 (exists ((N node)) (y N))))
(assert (= R3 (forall ((N node) (M node)) (or (not (x N)) (not (y M)) (= N M)))))


; Declare labels for the states and assert their disjunction
(declare-const S1 Bool)
(declare-const S2 Bool)
(declare-const S3 Bool)
(declare-const S4 Bool)
(declare-const S Bool)
(assert (= S (or S1 S2 S3 S4)))

; Define the states
(assert (= S1 (and (not (x n0)) (not (x n1)) (not (y n0)) ((y n1)) )))
(assert (= S2 (and (not (x n0)) (not (x n1)) ((y n0)) (not (y n1)) )))
(assert (= S3 (and (not (x n0)) ((x n1)) (not (y n0)) ((y n1)) )))
(assert (= S4 (and ((x n0)) (not (x n1)) ((y n0)) (not (y n1)) )))

; Check equivalence
(assert (= R S))
(check-sat)