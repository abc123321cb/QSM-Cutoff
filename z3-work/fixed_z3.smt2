; Declare node type
(declare-datatypes () ((node n0 n1)))

; Declare predicates/relations
(declare-fun ep_epoch0 (node) Bool)
(declare-fun ep_epoch1 (node) Bool)
(declare-fun ep_epoch2 (node) Bool)
(declare-fun ep_epoch3 (node) Bool)
(declare-fun held (node) Bool)
(declare-fun locked_epoch0 (node) Bool)
(declare-fun locked_epoch1 (node) Bool)
(declare-fun locked_epoch2 (node) Bool)
(declare-fun locked_epoch3 (node) Bool)
(declare-fun transfer_epoch0 (node) Bool)
(declare-fun transfer_epoch1 (node) Bool)
(declare-fun transfer_epoch2 (node) Bool)
(declare-fun transfer_epoch3 (node) Bool)

; States

; Invariants

(define-fun S1 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S2 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S3 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (transfer_epoch2 n0)
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S4 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (transfer_epoch2 n1)
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S5 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S6 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S7 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (transfer_epoch3 n0)
    (not (transfer_epoch3 n1))
)
)
(define-fun S8 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (transfer_epoch3 n1)
)
)
(define-fun S9 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (ep_epoch3 n0)
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (locked_epoch3 n0)
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S10 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (ep_epoch3 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (locked_epoch3 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S11 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (transfer_epoch3 n1)
)
)
(define-fun S12 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (transfer_epoch3 n0)
    (not (transfer_epoch3 n1))
)
)
(define-fun S13 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (ep_epoch3 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (locked_epoch3 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S14 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (ep_epoch3 n0)
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (locked_epoch3 n0)
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S15 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (transfer_epoch3 n0)
    (not (transfer_epoch3 n1))
)
)
(define-fun S16 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (transfer_epoch3 n1)
)
)
(define-fun S17 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (ep_epoch3 n0)
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (locked_epoch3 n0)
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S18 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (ep_epoch3 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (locked_epoch3 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S19 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (transfer_epoch2 n1)
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S20 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (transfer_epoch2 n0)
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S21 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S22 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S23 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (transfer_epoch3 n0)
    (not (transfer_epoch3 n1))
)
)
(define-fun S24 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (transfer_epoch3 n1)
)
)
(define-fun S25 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (ep_epoch3 n0)
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (locked_epoch3 n0)
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S26 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (ep_epoch3 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (locked_epoch3 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S27 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (ep_epoch2 n1)
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (transfer_epoch3 n1)
)
)
(define-fun S28 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (ep_epoch2 n0)
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (transfer_epoch3 n0)
    (not (transfer_epoch3 n1))
)
)
(define-fun S29 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (ep_epoch3 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (locked_epoch2 n1)
    (not (locked_epoch3 n0))
    (locked_epoch3 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S30 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (ep_epoch3 n0)
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (locked_epoch2 n0)
    (not (locked_epoch2 n1))
    (locked_epoch3 n0)
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S31 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (ep_epoch0 n1)
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (transfer_epoch3 n1)
)
)
(define-fun S32 () Bool
  (and
    (ep_epoch0 n0)
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (not (held n0))
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (transfer_epoch3 n0)
    (not (transfer_epoch3 n1))
)
)
(define-fun S33 () Bool
  (and
    (not (ep_epoch0 n0))
    (ep_epoch1 n0)
    (not (ep_epoch2 n0))
    (not (ep_epoch3 n0))
    (not (ep_epoch0 n1))
    (not (ep_epoch1 n1))
    (not (ep_epoch2 n1))
    (ep_epoch3 n1)
    (not (held n0))
    (held n1)
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (locked_epoch1 n0)
    (not (locked_epoch1 n1))
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (not (locked_epoch3 n0))
    (locked_epoch3 n1)
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun S34 () Bool
  (and
    (not (ep_epoch0 n0))
    (not (ep_epoch1 n0))
    (not (ep_epoch2 n0))
    (ep_epoch3 n0)
    (not (ep_epoch0 n1))
    (ep_epoch1 n1)
    (not (ep_epoch2 n1))
    (not (ep_epoch3 n1))
    (held n0)
    (not (held n1))
    (not (locked_epoch0 n0))
    (not (locked_epoch0 n1))
    (not (locked_epoch1 n0))
    (locked_epoch1 n1)
    (not (locked_epoch2 n0))
    (not (locked_epoch2 n1))
    (locked_epoch3 n0)
    (not (locked_epoch3 n1))
    (not (transfer_epoch0 n0))
    (not (transfer_epoch0 n1))
    (not (transfer_epoch1 n0))
    (not (transfer_epoch1 n1))
    (not (transfer_epoch2 n0))
    (not (transfer_epoch2 n1))
    (not (transfer_epoch3 n0))
    (not (transfer_epoch3 n1))
)
)
(define-fun R1 () Bool
  (forall ((node0 node)) (not (locked_epoch0 node0)))
)
(define-fun R2 () Bool
  (exists ((node0 node)) (not (ep_epoch0 node0)))
)
(define-fun R3 () Bool
  (forall ((node0 node)) (or (not (ep_epoch0 node0)) (not (ep_epoch1 node0))))
)
(define-fun R4 () Bool
  (forall ((node0 node)) (or (not (ep_epoch0 node0)) (not (ep_epoch2 node0))))
)
(define-fun R5 () Bool
  (forall ((node0 node)) (or (not (ep_epoch0 node0)) (not (ep_epoch3 node0))))
)
(define-fun R6 () Bool
  (forall ((node0 node)) (or (not (ep_epoch0 node0)) (not (held node0))))
)
(define-fun R7 () Bool
  (forall ((node0 node)) (or (not (ep_epoch0 node0)) (not (locked_epoch1 node0))))
)
(define-fun R8 () Bool
  (forall ((node0 node)) (or (not (ep_epoch0 node0)) (not (locked_epoch2 node0))))
)
(define-fun R9 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R10 () Bool
  (exists ((node0 node)) (not (ep_epoch1 node0)))
)
(define-fun R11 () Bool
  (forall ((node0 node)) (or (not (ep_epoch1 node0)) (not (ep_epoch2 node0))))
)
(define-fun R12 () Bool
  (forall ((node0 node)) (or (not (ep_epoch1 node0)) (not (ep_epoch3 node0))))
)
(define-fun R13 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (locked_epoch1 node1)) (= node0 node1)))
)
(define-fun R14 () Bool
  (forall ((node0 node)) (or (not (ep_epoch1 node0)) (not (locked_epoch2 node0))))
)
(define-fun R15 () Bool
  (forall ((node0 node)) (or (not (ep_epoch1 node0)) (locked_epoch1 node0)))
)
(define-fun R16 () Bool
  (exists ((node0 node)) (not (ep_epoch2 node0)))
)
(define-fun R17 () Bool
  (forall ((node0 node)) (or (not (ep_epoch2 node0)) (not (ep_epoch3 node0))))
)
(define-fun R18 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (locked_epoch2 node1)) (= node0 node1)))
)
(define-fun R19 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (transfer_epoch2 node1))))
)
(define-fun R20 () Bool
  (forall ((node0 node)) (or (not (ep_epoch2 node0)) (locked_epoch2 node0)))
)
(define-fun R21 () Bool
  (exists ((node0 node)) (not (ep_epoch3 node0)))
)
(define-fun R22 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (held node1)) (= node0 node1)))
)
(define-fun R23 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (transfer_epoch2 node1))))
)
(define-fun R24 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (transfer_epoch3 node1))))
)
(define-fun R25 () Bool
  (forall ((node0 node)) (or (not (ep_epoch3 node0)) (held node0)))
)
(define-fun R26 () Bool
  (exists ((node0 node)) (not (held node0)))
)
(define-fun R27 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (transfer_epoch2 node1))))
)
(define-fun R28 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (transfer_epoch3 node1))))
)
(define-fun R29 () Bool
  (exists ((node0 node)) (not (locked_epoch1 node0)))
)
(define-fun R30 () Bool
  (exists ((node0 node)) (not (locked_epoch2 node0)))
)
(define-fun R31 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (not (transfer_epoch2 node1))))
)
(define-fun R32 () Bool
  (exists ((node0 node)) (not (transfer_epoch2 node0)))
)
(define-fun R33 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch2 node0)) (not (transfer_epoch3 node1))))
)
(define-fun R34 () Bool
  (exists ((node0 node)) (not (transfer_epoch3 node0)))
)
(define-fun R35 () Bool
  (exists ((node0 node)) (locked_epoch1 node0))
)
(define-fun R36 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (not (transfer_epoch2 node1)) (ep_epoch1 node2) (and (or (not (= node1 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R37 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (ep_epoch2 node1)) (not (held node0)) (= node0 node1)))
)
(define-fun R38 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (held node0)) (not (locked_epoch2 node1)) (= node0 node1)))
)
(define-fun R39 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (held node0)) (ep_epoch0 node1) (= node0 node1)))
)
(define-fun R40 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (transfer_epoch2 node1)) (ep_epoch0 node2) (and (or (not (= node1 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R41 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (held node1)) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R42 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch2 node1)) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R43 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch2 node1)) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R44 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch2 node1)) (ep_epoch3 node0) (= node0 node1)))
)
(define-fun R45 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (transfer_epoch2 node1)) (ep_epoch0 node2) (and (or (not (= node1 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R46 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (transfer_epoch2 node1)) (ep_epoch1 node0)))
)
(define-fun R47 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch2 node0)))
)
(define-fun R48 () Bool
  (forall ((node0 node)) (or (not (locked_epoch2 node0)) (ep_epoch2 node0) (ep_epoch3 node0)))
)
(define-fun R49 () Bool
  (forall ((node0 node)) (or (not (locked_epoch2 node0)) (ep_epoch2 node0) (held node0)))
)
(define-fun R50 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch2 node0)) (ep_epoch0 node0) (ep_epoch0 node1) (= node0 node1)))
)
(define-fun R51 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1)))
)
(define-fun R52 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch2 node0)) (ep_epoch0 node1) (locked_epoch1 node1)))
)
(define-fun R53 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch2 node0)) (ep_epoch1 node0) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R54 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (transfer_epoch2 node0)) (ep_epoch1 node1) (locked_epoch1 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node0 node2)) (= node0 node1)))))
)
(define-fun R55 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (not (transfer_epoch3 node1)) (ep_epoch1 node2) (ep_epoch2 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R56 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (not (transfer_epoch3 node1)) (ep_epoch1 node2) (locked_epoch2 node2) (and (or (not (= node1 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R57 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (ep_epoch1 node1) (ep_epoch2 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R58 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (ep_epoch1 node1) (ep_epoch2 node1) (held node1) (= node0 node1)))
)
(define-fun R59 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (ep_epoch1 node1) (ep_epoch3 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R60 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (ep_epoch1 node1) (held node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R61 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (held node1)) (ep_epoch2 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R62 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (held node1)) (ep_epoch3 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R63 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (ep_epoch2 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R64 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (locked_epoch2 node2) (and (or (not (= node1 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R65 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R66 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (held node1) (= node0 node1)))
)
(define-fun R67 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (ep_epoch0 node1) (ep_epoch3 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R68 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (ep_epoch0 node1) (held node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R69 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (held node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (= node0 node1)))
)
(define-fun R70 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (held node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R71 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (held node0)) (ep_epoch0 node1) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R72 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (held node0)) (ep_epoch0 node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R73 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (held node0)) (ep_epoch1 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R74 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (locked_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R75 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R76 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (held node1) (= node0 node1)))
)
(define-fun R77 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (locked_epoch1 node1)) (not (transfer_epoch3 node2)) (ep_epoch1 node1) (and (or (not (= node0 node2)) (= node0 node1)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R78 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R79 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (held node1) (= node0 node1)))
)
(define-fun R80 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (ep_epoch1 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R81 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (locked_epoch1 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R82 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch1 node2) (locked_epoch1 node0) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R83 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R84 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (held node1) (= node0 node1)))
)
(define-fun R85 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (ep_epoch0 node1) (ep_epoch3 node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R86 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (ep_epoch0 node1) (held node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R87 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (ep_epoch1 node1) (ep_epoch3 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R88 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (ep_epoch1 node1) (held node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R89 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch1 node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (= node0 node1)))
)
(define-fun R90 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R91 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R92 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch1 node1)) (not (locked_epoch2 node0)) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R93 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R94 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R95 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R96 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R97 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (not (locked_epoch2 node0)) (ep_epoch1 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R98 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R99 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R100 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R101 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (ep_epoch0 node1) (locked_epoch1 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R102 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (ep_epoch1 node1) (ep_epoch2 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R103 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch3 node0)) (ep_epoch1 node1) (locked_epoch1 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R104 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (= node0 node1)))
)
(define-fun R105 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R106 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch3 node0) (= node0 node1)))
)
(define-fun R107 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node0)) (ep_epoch0 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R108 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node1)) (not (locked_epoch2 node0)) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R109 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R110 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (ep_epoch3 node0) (= node0 node1)))
)
(define-fun R111 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node1)) (ep_epoch1 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R112 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node1)) (ep_epoch2 node0) (ep_epoch3 node0) (= node0 node1)))
)
(define-fun R113 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch1 node1)) (ep_epoch3 node0) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R114 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R115 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R116 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (not (locked_epoch2 node0)) (ep_epoch1 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R117 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (ep_epoch1 node1) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R118 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (ep_epoch1 node1) (ep_epoch3 node0) (= node0 node1)))
)
(define-fun R119 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (ep_epoch1 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R120 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (ep_epoch2 node0) (ep_epoch3 node0) (= node0 node1)))
)
(define-fun R121 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (ep_epoch2 node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R122 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (ep_epoch3 node0) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R123 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (ep_epoch3 node0) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R124 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch0 node1) (locked_epoch1 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R125 () Bool
  (forall ((node0 node)) (or (not (held node0)) (ep_epoch1 node0) (ep_epoch2 node0) (ep_epoch3 node0)))
)
(define-fun R126 () Bool
  (forall ((node0 node)) (or (not (held node0)) (ep_epoch1 node0) (ep_epoch3 node0) (locked_epoch2 node0)))
)
(define-fun R127 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch1 node1) (ep_epoch2 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R128 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch1 node1) (ep_epoch3 node0) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R129 () Bool
  (forall ((node0 node) (node1 node)) (or (not (held node0)) (ep_epoch1 node1) (locked_epoch1 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R130 () Bool
  (forall ((node0 node)) (or (not (held node0)) (ep_epoch2 node0) (ep_epoch3 node0) (locked_epoch1 node0)))
)
(define-fun R131 () Bool
  (forall ((node0 node)) (or (not (held node0)) (ep_epoch3 node0) (locked_epoch1 node0) (locked_epoch2 node0)))
)
(define-fun R132 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R133 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch2 node0) (= node0 node1)))
)
(define-fun R134 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R135 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node0)) (ep_epoch0 node1) (held node1) (= node0 node1)))
)
(define-fun R136 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node1)) (not (transfer_epoch3 node2)) (ep_epoch1 node0) (and (or (not (= node1 node2)) (= node0 node1)) (or (not (= node0 node2)) (= node0 node1)))))
)
(define-fun R137 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node1)) (ep_epoch1 node0) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R138 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node1)) (ep_epoch1 node0) (ep_epoch3 node0) (= node0 node1)))
)
(define-fun R139 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (locked_epoch2 node1)) (ep_epoch1 node0) (held node0) (= node0 node1)))
)
(define-fun R140 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (ep_epoch1 node0) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R141 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (ep_epoch2 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R142 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (locked_epoch2 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R143 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch1 node0) (ep_epoch2 node0)))
)
(define-fun R144 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (not (transfer_epoch3 node1)) (ep_epoch1 node0) (locked_epoch2 node0)))
)
(define-fun R145 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R146 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (held node1) (= node0 node1)))
)
(define-fun R147 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch3 node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R148 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (held node1) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R149 () Bool
  (forall ((node0 node)) (or (not (locked_epoch1 node0)) (ep_epoch1 node0) (ep_epoch2 node0) (ep_epoch3 node0)))
)
(define-fun R150 () Bool
  (forall ((node0 node)) (or (not (locked_epoch1 node0)) (ep_epoch1 node0) (ep_epoch2 node0) (held node0)))
)
(define-fun R151 () Bool
  (forall ((node0 node)) (or (not (locked_epoch1 node0)) (ep_epoch1 node0) (ep_epoch3 node0) (locked_epoch2 node0)))
)
(define-fun R152 () Bool
  (forall ((node0 node)) (or (not (locked_epoch1 node0)) (ep_epoch1 node0) (held node0) (locked_epoch2 node0)))
)
(define-fun R153 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (ep_epoch1 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R154 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch0 node2) (locked_epoch1 node2) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R155 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (not (transfer_epoch3 node1)) (ep_epoch1 node2) (locked_epoch1 node0) (and (or (not (= node0 node1)) (= node0 node2)) (or (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R156 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (ep_epoch2 node0) (= node0 node1)))
)
(define-fun R157 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R158 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (held node1) (= node0 node1)))
)
(define-fun R159 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch2 node0) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R160 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch0 node1) (ep_epoch3 node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R161 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch0 node1) (held node1) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R162 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch1 node1) (ep_epoch2 node0) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R163 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch1 node1) (ep_epoch3 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R164 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch1 node1) (held node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R165 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (ep_epoch2 node1)))
)
(define-fun R166 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node1) (ep_epoch1 node1) (locked_epoch2 node1)))
)
(define-fun R167 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node1) (ep_epoch1 node2) (locked_epoch1 node1) (and (or (not (= node0 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R168 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node1) (ep_epoch2 node1) (locked_epoch1 node1)))
)
(define-fun R169 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node1) (locked_epoch1 node1) (locked_epoch2 node1)))
)
(define-fun R170 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch1 node1) (ep_epoch2 node1) (locked_epoch1 node2) (and (or (not (= node0 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R171 () Bool
  (forall ((node2 node) (node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch1 node1) (locked_epoch1 node2) (locked_epoch2 node1) (and (or (not (= node0 node2)) (= node0 node1)) (or (not (= node0 node1)) (= node0 node2)))))
)
(define-fun R172 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (ep_epoch2 node0) (ep_epoch3 node0)))
)
(define-fun R173 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (ep_epoch2 node0) (held node0)))
)
(define-fun R174 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (ep_epoch3 node0) (locked_epoch2 node0)))
)
(define-fun R175 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (held node0) (locked_epoch2 node0)))
)
(define-fun R176 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (ep_epoch2 node0) (ep_epoch3 node0) (locked_epoch1 node0)))
)
(define-fun R177 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (ep_epoch2 node0) (held node0) (locked_epoch1 node0)))
)
(define-fun R178 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (ep_epoch3 node0) (locked_epoch1 node0) (locked_epoch2 node0)))
)
(define-fun R179 () Bool
  (forall ((node0 node)) (or (ep_epoch0 node0) (held node0) (locked_epoch1 node0) (locked_epoch2 node0)))
)
(define-fun R180 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch2 node0) (ep_epoch3 node0) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R181 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch2 node0) (held node0) (locked_epoch1 node1) (= node0 node1)))
)
(define-fun R182 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch3 node0) (locked_epoch1 node1) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R183 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (held node0) (locked_epoch1 node1) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R184 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (not (ep_epoch2 node1)) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R185 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (not (locked_epoch2 node1)) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R186 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (ep_epoch1 node1) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R187 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (ep_epoch2 node1)) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R188 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (not (locked_epoch2 node1)) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R189 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (ep_epoch0 node1) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R190 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (ep_epoch3 node1) (held node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R191 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch2 node0)) (held node0) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R192 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch1 node0) (ep_epoch2 node0) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R193 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch1 node0) (ep_epoch2 node2) (locked_epoch2 node3) (and (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)) (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R194 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch1 node0) (ep_epoch3 node0) (ep_epoch3 node1) (= node0 node1)))
)
(define-fun R195 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch1 node0) (ep_epoch3 node2) (held node3) (and (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)) (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)))))
)
(define-fun R196 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch1 node0) (held node0) (held node1) (= node0 node1)))
)
(define-fun R197 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch1 node0) (locked_epoch2 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R198 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (ep_epoch3 node1) (held node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R199 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch2 node0)) (held node0) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R200 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch1 node0) (ep_epoch1 node1) (= node0 node1)))
)
(define-fun R201 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch2 node0) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R202 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch2 node2) (locked_epoch2 node3) (and (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)) (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R203 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch0 node0) (ep_epoch0 node1) (locked_epoch2 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R204 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node0) (ep_epoch2 node1) (= node0 node1)))
)
(define-fun R205 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (not (transfer_epoch3 node0)) (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node2) (locked_epoch2 node3) (and (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)) (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R206 () Bool
  (forall ((node0 node) (node1 node)) (or (not (transfer_epoch3 node0)) (ep_epoch1 node0) (ep_epoch1 node1) (locked_epoch2 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R207 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch1 node1) (ep_epoch2 node0) (ep_epoch2 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R208 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (ep_epoch0 node0) (ep_epoch1 node1) (ep_epoch2 node2) (locked_epoch1 node0) (locked_epoch2 node3) (and (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)) (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R209 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch1 node1) (ep_epoch3 node0) (ep_epoch3 node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R210 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (ep_epoch0 node0) (ep_epoch1 node1) (ep_epoch3 node2) (held node3) (locked_epoch1 node0) (and (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)) (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R211 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch1 node1) (held node0) (held node1) (locked_epoch1 node0) (= node0 node1)))
)
(define-fun R212 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch1 node1) (locked_epoch1 node0) (locked_epoch2 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R213 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch0 node0)) (held node1) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R214 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (ep_epoch3 node0) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R215 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch0 node1) (held node0) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R216 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch1 node0) (ep_epoch3 node1) (held node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R217 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch1 node0) (held node0) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R218 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (ep_epoch2 node0)))
)
(define-fun R219 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node1) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R220 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (ep_epoch3 node0)))
)
(define-fun R221 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch3 node0) (held node1) (= node0 node1)))
)
(define-fun R222 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (held node0)))
)
(define-fun R223 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (locked_epoch2 node0)))
)
(define-fun R224 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (ep_epoch2 node0) (ep_epoch3 node0)))
)
(define-fun R225 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch2 node0) (ep_epoch2 node1) (ep_epoch3 node0) (held node1) (= node0 node1)))
)
(define-fun R226 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (ep_epoch2 node0) (held node0)))
)
(define-fun R227 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch2 node1) (ep_epoch3 node0) (ep_epoch3 node1) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R228 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch2 node1) (ep_epoch3 node2) (held node3) (locked_epoch2 node0) (and (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)) (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R229 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch2 node1) (held node0) (held node1) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R230 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (ep_epoch3 node0) (locked_epoch2 node0)))
)
(define-fun R231 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch3 node0) (held node1) (locked_epoch2 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R232 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (held node0) (locked_epoch2 node0)))
)
(define-fun R233 () Bool
  (exists ((node0 node)) (or (ep_epoch0 node0) (held node0) (transfer_epoch3 node0)))
)
(define-fun R234 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (ep_epoch3 node1) (held node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R235 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch1 node0) (held node0) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R236 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch3 node1) (held node0) (locked_epoch1 node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R237 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (held node0) (held node1) (locked_epoch1 node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R238 () Bool
  (exists ((node0 node)) (or (ep_epoch1 node0) (ep_epoch2 node0) (ep_epoch3 node0)))
)
(define-fun R239 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node0) (ep_epoch2 node1) (ep_epoch3 node0) (held node1) (= node0 node1)))
)
(define-fun R240 () Bool
  (exists ((node0 node)) (or (ep_epoch1 node0) (ep_epoch2 node0) (held node0)))
)
(define-fun R241 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node1) (ep_epoch3 node0) (ep_epoch3 node1) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R242 () Bool
  (forall ((node2 node) (node0 node) (node1 node) (node3 node)) (or (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node1) (ep_epoch3 node2) (held node3) (locked_epoch2 node0) (and (or (not (= node0 node2)) (not (= node1 node3)) (= node0 node1)) (or (not (= node0 node3)) (not (= node1 node2)) (= node0 node1)))))
)
(define-fun R243 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node1) (held node0) (held node1) (locked_epoch2 node0) (= node0 node1)))
)
(define-fun R244 () Bool
  (exists ((node0 node)) (or (ep_epoch1 node0) (ep_epoch3 node0) (locked_epoch2 node0)))
)
(define-fun R245 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch3 node0) (held node1) (locked_epoch2 node0) (locked_epoch2 node1) (= node0 node1)))
)
(define-fun R246 () Bool
  (exists ((node0 node)) (or (ep_epoch1 node0) (held node0) (locked_epoch2 node0)))
)
(define-fun R247 () Bool
  (exists ((node0 node)) (or (ep_epoch1 node0) (held node0) (transfer_epoch3 node0)))
)
(define-fun R248 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch3 node1) (held node0) (locked_epoch1 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R249 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (held node0) (held node1) (locked_epoch1 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R250 () Bool
  (exists ((node0 node)) (or (held node0) (transfer_epoch2 node0) (transfer_epoch3 node0)))
)
(define-fun R251 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch2 node1) (ep_epoch3 node1) (held node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R252 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch0 node1) (ep_epoch3 node0) (held node1) (locked_epoch2 node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R253 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch2 node0) (ep_epoch3 node0) (held node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R254 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch1 node1) (ep_epoch3 node0) (held node1) (locked_epoch2 node0) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R255 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (ep_epoch2 node1) (ep_epoch3 node1) (held node0) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R256 () Bool
  (forall ((node0 node) (node1 node)) (or (not (ep_epoch1 node0)) (ep_epoch3 node1) (held node0) (locked_epoch2 node1) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R257 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch2 node1) (ep_epoch3 node1) (held node0) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R258 () Bool
  (forall ((node0 node) (node1 node)) (or (not (locked_epoch1 node0)) (ep_epoch3 node1) (held node0) (locked_epoch2 node1) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R259 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch2 node1) (ep_epoch3 node1) (held node0) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R260 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch0 node0) (ep_epoch3 node1) (held node0) (locked_epoch2 node1) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R261 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch2 node0) (ep_epoch3 node0) (held node1) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R262 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch1 node0) (ep_epoch3 node0) (held node1) (locked_epoch2 node0) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R263 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch2 node0) (ep_epoch3 node0) (held node1) (locked_epoch1 node0) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R264 () Bool
  (forall ((node0 node) (node1 node)) (or (ep_epoch3 node0) (held node1) (locked_epoch1 node0) (locked_epoch2 node0) (transfer_epoch2 node0) (transfer_epoch2 node1) (transfer_epoch3 node0) (transfer_epoch3 node1) (= node0 node1)))
)
(define-fun R265 () Bool
  (forall ((node0 node)) (= (locked_epoch0 node0) (transfer_epoch0 node0)))
)
(define-fun R266 () Bool
  (forall ((node0 node)) (= (locked_epoch0 node0) (transfer_epoch1 node0)))
)
(define-fun R267 () Bool
  (forall ((node0 node)) (= (ep_epoch3 node0) (locked_epoch3 node0)))
)
(define-fun S () Bool
  (or 
  S1  S2  S3  S4  S5  S6  S7  S8  S9  S10 
  S11 S12 S13 S14 S15 S16 S17 S18 S19 S20 
  S21 S22 S23 S24 S25 S26 S27 S28 S29 S30 
  S31 S32 S33 S34
)
)
(define-fun R () Bool
  (and 
  R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
  R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
  R21 R22 R23 R24 R25 R26 R27 R28 R29 R30
  R31 R32 R33 R34 R35 R36 R37 R38 R39 R40
  R41 R42 R43 R44 R45 R46 R47 R48 R49 R50
  R51 R52 R53 R54 R55 R56 R57 R58 R59 R60
  R61 R62 R63 R64 R65 R66 R67 R68 R69 R70
  R71 R72 R73 R74 R75 R76 R77 R78 R79 R80
  R81 R82 R83 R84 R85 R86 R87 R88 R89 R90
  R91 R92 R93 R94 R95 R96 R97 R98 R99 R100
  R101 R102 R103 R104 R105 R106 R107 R108 R109 R110
  R111 R112 R113 R114 R115 R116 R117 R118 R119 R120
  R121 R122 R123 R124 R125 R126 R127 R128 R129 R130
  R131 R132 R133 R134 R135 R136 R137 R138 R139 R140
  R141 R142 R143 R144 R145 R146 R147 R148 R149 R150
  R151 R152 R153 R154 R155 R156 R157 R158 R159 R160
  R161 R162 R163 R164 R165 R166 R167 R168 R169 R170
  R171 R172 R173 R174 R175 R176 R177 R178 R179 R180
  R181 R182 R183 R184 R185 R186 R187 R188 R189 R190
  R191 R192 R193 R194 R195 R196 R197 R198 R199 R200
  R201 R202 R203 R204 R205 R206 R207 R208 R209 R210
  R211 R212 R213 R214 R215 R216 R217 R218 R219 R220
  R221 R222 R223 R224 R225 R226 R227 R228 R229 R230
  R231 R232 R233 R234 R235 R236 R237 R238 R239 R240
  R241 R242 R243 R244 R245 R246 R247 R248 R249 R250
  R251 R252 R253 R254 R255 R256 R257 R258 R259 R260
  R261 R262 R263 R264 R265 R266 R267
)
)

(assert (not (= R S) ))

(check-sat)
(get-model)