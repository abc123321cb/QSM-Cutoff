; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes ((Node 0)) (((node0) (node1))))
(declare-datatypes ((Epoch 0)) (((epoch0) (epoch1) (epoch2))))
(declare-fun locked (Epoch Node) Bool)
(declare-fun transfer (Epoch Node) Bool)
(declare-fun ep (Node) Epoch)
(declare-fun held (Node) Bool)
(declare-fun first () Node)
(declare-fun le (Epoch Epoch) Bool)

; ===== Orbit Group F1 =====
; orbit[0] F1 1 line 2: 1: forall N. ~locked_epoch1(N) ==> forall N. ~locked(epoch1,N)
(assert
  (and
    (not
      (locked epoch1 node0)
    )
    (not
      (locked epoch1 node1)
    )
  )
)

; ===== Orbit Group F2 =====
; orbit[1] F2 2 line 5: 2: forall N. ~transfer_epoch0(N) ==> forall N. ~transfer(epoch0,N)
(assert
  (and
    (not
      (transfer epoch0 node0)
    )
    (not
      (transfer epoch0 node1)
    )
  )
)
; orbit[2] F2 3 line 6: 3: forall N. ~transfer_epoch1(N) ==> forall N. ~transfer(epoch1,N)
(assert
  (and
    (not
      (transfer epoch1 node0)
    )
    (not
      (transfer epoch1 node1)
    )
  )
)

; ===== Orbit Group F3 =====
; orbit[3] F3 5 line 9: 5: forall N. ~ep_epoch0(N) | ~ep_epoch1(N) ==> forall N. ~ep(N)=epoch0 | ~ep(N)=epoch1
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch0
        )
      )
      (not
        (=
          (ep node0)
          epoch1
        )
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch0
        )
      )
      (not
        (=
          (ep node1)
          epoch1
        )
      )
    )
  )
)
; orbit[4] F3 6 line 10: 6: forall N. ~ep_epoch0(N) | ~ep_epoch2(N) ==> forall N. ~ep(N)=epoch0 | ~ep(N)=epoch2
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch0
        )
      )
      (not
        (=
          (ep node0)
          epoch2
        )
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch0
        )
      )
      (not
        (=
          (ep node1)
          epoch2
        )
      )
    )
  )
)
; orbit[5] F3 10 line 11: 10: forall N. ~ep_epoch1(N) | ~ep_epoch2(N) ==> forall N. ~ep(N)=epoch1 | ~ep(N)=epoch2
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch1
        )
      )
      (not
        (=
          (ep node0)
          epoch2
        )
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch1
        )
      )
      (not
        (=
          (ep node1)
          epoch2
        )
      )
    )
  )
)

; ===== Orbit Group F4 =====
; orbit[6] F4 7 line 14: 7: forall N. ~ep_epoch0(N) | ~held(N) ==> forall N. ~ep(N)=epoch0 | ~held(N)
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch0
        )
      )
      (not
        (held node0)
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch0
        )
      )
      (not
        (held node1)
      )
    )
  )
)

; ===== Orbit Group F5 =====
; orbit[7] F5 8 line 17: 8: forall N. ~ep_epoch0(N) | ~locked_epoch2(N) ==> forall N. ~ep(N)=epoch0 | ~locked(epoch2,N)
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch0
        )
      )
      (not
        (locked epoch2 node0)
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch0
        )
      )
      (not
        (locked epoch2 node1)
      )
    )
  )
)
; orbit[8] F5 11 line 18: 11: forall N. ~ep_epoch1(N) | ~locked_epoch2(N) ==> forall N. ~ep(N)=epoch1 | ~locked(epoch2,N)
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch1
        )
      )
      (not
        (locked epoch2 node0)
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch1
        )
      )
      (not
        (locked epoch2 node1)
      )
    )
  )
)

; ===== Orbit Group F6 =====
; orbit[9] F6 13 line 21: 13: forall N1,N0. ~ep_epoch2(N0) | ~held(N1) | N0 = N1 ==> forall N1,N0. ~ep(N0)=epoch2 | ~held(N1) | N0 = N1
(assert
  (and
    (or
      (or
        (not
          (=
            (ep node0)
            epoch2
          )
        )
        (not
          (held node0)
        )
      )
      (= node0 node0)
    )
    (or
      (or
        (not
          (=
            (ep node1)
            epoch2
          )
        )
        (not
          (held node0)
        )
      )
      (= node1 node0)
    )
    (or
      (or
        (not
          (=
            (ep node0)
            epoch2
          )
        )
        (not
          (held node1)
        )
      )
      (= node0 node1)
    )
    (or
      (or
        (not
          (=
            (ep node1)
            epoch2
          )
        )
        (not
          (held node1)
        )
      )
      (= node1 node1)
    )
  )
)

; ===== Orbit Group F7 =====
; orbit[10] F7 14 line 24: 14: forall N1,N0. ~ep_epoch2(N0) | ~locked_epoch2(N1) | N0 = N1 ==> forall N1,N0. ~ep(N0)=epoch2 | ~locked(epoch2,N1) | N0 = N1
(assert
  (and
    (or
      (or
        (not
          (=
            (ep node0)
            epoch2
          )
        )
        (not
          (locked epoch2 node0)
        )
      )
      (= node0 node0)
    )
    (or
      (or
        (not
          (=
            (ep node1)
            epoch2
          )
        )
        (not
          (locked epoch2 node0)
        )
      )
      (= node1 node0)
    )
    (or
      (or
        (not
          (=
            (ep node0)
            epoch2
          )
        )
        (not
          (locked epoch2 node1)
        )
      )
      (= node0 node1)
    )
    (or
      (or
        (not
          (=
            (ep node1)
            epoch2
          )
        )
        (not
          (locked epoch2 node1)
        )
      )
      (= node1 node1)
    )
  )
)

; ===== Orbit Group F8 =====
; orbit[11] F8 15 line 27: 15: forall N1,N0. ~ep_epoch2(N0) | ~transfer_epoch2(N1) ==> forall N1,N0. ~ep(N0)=epoch2 | ~transfer(epoch2,N1)
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch2
        )
      )
      (not
        (transfer epoch2 node0)
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch2
        )
      )
      (not
        (transfer epoch2 node0)
      )
    )
    (or
      (not
        (=
          (ep node0)
          epoch2
        )
      )
      (not
        (transfer epoch2 node1)
      )
    )
    (or
      (not
        (=
          (ep node1)
          epoch2
        )
      )
      (not
        (transfer epoch2 node1)
      )
    )
  )
)

; ===== Orbit Group F9 =====
; orbit[12] F9 16 line 30: 16: forall N. ~ep_epoch2(N) | held(N) ==> forall N. ~ep(N)=epoch2 | held(N)
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch2
        )
      )
      (held node0)
    )
    (or
      (not
        (=
          (ep node1)
          epoch2
        )
      )
      (held node1)
    )
  )
)

; ===== Orbit Group F10 =====
; orbit[13] F10 17 line 33: 17: forall N. ~ep_epoch2(N) | locked_epoch2(N) ==> forall N. ~ep(N)=epoch2 | locked(epoch2,N)
(assert
  (and
    (or
      (not
        (=
          (ep node0)
          epoch2
        )
      )
      (locked epoch2 node0)
    )
    (or
      (not
        (=
          (ep node1)
          epoch2
        )
      )
      (locked epoch2 node1)
    )
  )
)

; ===== Orbit Group F11 =====
; orbit[14] F11 19 line 36: 19: forall N1,N0. ~held(N0) | ~locked_epoch2(N1) | N0 = N1 ==> forall N1,N0. ~held(N0) | ~locked(epoch2,N1) | N0 = N1
(assert
  (and
    (or
      (or
        (not
          (held node0)
        )
        (not
          (locked epoch2 node0)
        )
      )
      (= node0 node0)
    )
    (or
      (or
        (not
          (held node1)
        )
        (not
          (locked epoch2 node0)
        )
      )
      (= node1 node0)
    )
    (or
      (or
        (not
          (held node0)
        )
        (not
          (locked epoch2 node1)
        )
      )
      (= node0 node1)
    )
    (or
      (or
        (not
          (held node1)
        )
        (not
          (locked epoch2 node1)
        )
      )
      (= node1 node1)
    )
  )
)

; ===== Orbit Group F12 =====
; orbit[15] F12 20 line 39: 20: forall N1,N0. ~held(N0) | ~transfer_epoch2(N1) ==> forall N1,N0. ~held(N0) | ~transfer(epoch2,N1)
(assert
  (and
    (or
      (not
        (held node0)
      )
      (not
        (transfer epoch2 node0)
      )
    )
    (or
      (not
        (held node1)
      )
      (not
        (transfer epoch2 node0)
      )
    )
    (or
      (not
        (held node0)
      )
      (not
        (transfer epoch2 node1)
      )
    )
    (or
      (not
        (held node1)
      )
      (not
        (transfer epoch2 node1)
      )
    )
  )
)

; ===== Orbit Group F13 =====
; orbit[16] F13 22 line 42: 22: forall N1,N0. ~locked_epoch2(N0) | ~transfer_epoch2(N1) ==> forall N1,N0. ~locked(epoch2,N0) | ~transfer(epoch2,N1)
(assert
  (and
    (or
      (not
        (locked epoch2 node0)
      )
      (not
        (transfer epoch2 node0)
      )
    )
    (or
      (not
        (locked epoch2 node1)
      )
      (not
        (transfer epoch2 node0)
      )
    )
    (or
      (not
        (locked epoch2 node0)
      )
      (not
        (transfer epoch2 node1)
      )
    )
    (or
      (not
        (locked epoch2 node1)
      )
      (not
        (transfer epoch2 node1)
      )
    )
  )
)

; ===== Orbit Group F14 =====
; orbit[17] F14 23 line 45: 23: forall N. ~locked_epoch2(N) | ep_epoch2(N) ==> forall N. ~locked(epoch2,N) | ep(N)=epoch2
(assert
  (and
    (or
      (not
        (locked epoch2 node0)
      )
      (=
        (ep node0)
        epoch2
      )
    )
    (or
      (not
        (locked epoch2 node1)
      )
      (=
        (ep node1)
        epoch2
      )
    )
  )
)

; ===== Orbit Group F15 =====
; orbit[18] F15 24 line 48: 24: forall N. ~locked_epoch2(N) | held(N) ==> forall N. ~locked(epoch2,N) | held(N)
(assert
  (and
    (or
      (not
        (locked epoch2 node0)
      )
      (held node0)
    )
    (or
      (not
        (locked epoch2 node1)
      )
      (held node1)
    )
  )
)

; ===== Orbit Group E1 =====
; orbit[19] E1 4 line 51: 4: exists N. ~ep_epoch0(N) ==> exists N. ~ep(N)=epoch0
(assert
  (or
    (not
      (=
        (ep node0)
        epoch0
      )
    )
    (not
      (=
        (ep node1)
        epoch0
      )
    )
  )
)
; orbit[20] E1 9 line 52: 9: exists N. ~ep_epoch1(N) ==> exists N. ~ep(N)=epoch1
(assert
  (or
    (not
      (=
        (ep node0)
        epoch1
      )
    )
    (not
      (=
        (ep node1)
        epoch1
      )
    )
  )
)
; orbit[21] E1 12 line 53: 12: exists N. ~ep_epoch2(N) ==> exists N. ~ep(N)=epoch2
(assert
  (or
    (not
      (=
        (ep node0)
        epoch2
      )
    )
    (not
      (=
        (ep node1)
        epoch2
      )
    )
  )
)

; ===== Orbit Group E2 =====
; orbit[22] E2 18 line 56: 18: exists N. ~held(N)
(assert
  (or
    (not
      (held node0)
    )
    (not
      (held node1)
    )
  )
)
(assert
  (= first node0)
)
(assert
  (not
    (= first node1)
  )
)
(assert
  (not
    (= epoch1 epoch0)
  )
)
(assert
  (= epoch1 epoch1)
)
(assert
  (not
    (= epoch1 epoch2)
  )
)
(assert
  (le epoch0 epoch0)
)
(assert
  (le epoch0 epoch1)
)
(assert
  (le epoch0 epoch2)
)
(assert
  (not
    (le epoch1 epoch0)
  )
)
(assert
  (le epoch1 epoch1)
)
(assert
  (le epoch1 epoch2)
)
(assert
  (not
    (le epoch2 epoch0)
  )
)
(assert
  (not
    (le epoch2 epoch1)
  )
)
(assert
  (le epoch2 epoch2)
)
(assert
  (not
    (= epoch2 epoch0)
  )
)
(assert
  (not
    (= epoch2 epoch1)
  )
)
(assert
  (= epoch2 epoch2)
)
(assert
  (= epoch0 epoch0)
)
(assert
  (not
    (= epoch0 epoch1)
  )
)
(assert
  (not
    (= epoch0 epoch2)
  )
)
; --- reachable state exclusions begin: excluding 10 reachable states ---
(assert
  (or
    (=
      (ep node0)
      epoch0
    )
    (=
      (ep node0)
      epoch1
    )
    (not
      (=
        (ep node0)
        epoch2
      )
    )
    (not
      (=
        (ep node1)
        epoch0
      )
    )
    (=
      (ep node1)
      epoch1
    )
    (=
      (ep node1)
      epoch2
    )
    (not
      (held node0)
    )
    (held node1)
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (not
      (locked epoch2 node0)
    )
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (transfer epoch2 node1)
  )
)
(assert
  (or
    (not
      (=
        (ep node0)
        epoch0
      )
    )
    (=
      (ep node0)
      epoch1
    )
    (=
      (ep node0)
      epoch2
    )
    (=
      (ep node1)
      epoch0
    )
    (not
      (=
        (ep node1)
        epoch1
      )
    )
    (=
      (ep node1)
      epoch2
    )
    (held node0)
    (not
      (held node1)
    )
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (transfer epoch2 node1)
  )
)
(assert
  (or
    (=
      (ep node0)
      epoch0
    )
    (not
      (=
        (ep node0)
        epoch1
      )
    )
    (=
      (ep node0)
      epoch2
    )
    (not
      (=
        (ep node1)
        epoch0
      )
    )
    (=
      (ep node1)
      epoch1
    )
    (=
      (ep node1)
      epoch2
    )
    (held node0)
    (held node1)
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (not
      (transfer epoch2 node1)
    )
  )
)
(assert
  (or
    (=
      (ep node0)
      epoch0
    )
    (=
      (ep node0)
      epoch1
    )
    (not
      (=
        (ep node0)
        epoch2
      )
    )
    (=
      (ep node1)
      epoch0
    )
    (not
      (=
        (ep node1)
        epoch1
      )
    )
    (=
      (ep node1)
      epoch2
    )
    (not
      (held node0)
    )
    (held node1)
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (not
      (locked epoch2 node0)
    )
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (transfer epoch2 node1)
  )
)
(assert
  (or
    (not
      (=
        (ep node0)
        epoch0
      )
    )
    (=
      (ep node0)
      epoch1
    )
    (=
      (ep node0)
      epoch2
    )
    (=
      (ep node1)
      epoch0
    )
    (=
      (ep node1)
      epoch1
    )
    (not
      (=
        (ep node1)
        epoch2
      )
    )
    (held node0)
    (not
      (held node1)
    )
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (not
      (locked epoch2 node1)
    )
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (transfer epoch2 node1)
  )
)
(assert
  (or
    (not
      (=
        (ep node0)
        epoch0
      )
    )
    (=
      (ep node0)
      epoch1
    )
    (=
      (ep node0)
      epoch2
    )
    (=
      (ep node1)
      epoch0
    )
    (not
      (=
        (ep node1)
        epoch1
      )
    )
    (=
      (ep node1)
      epoch2
    )
    (held node0)
    (held node1)
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (not
      (transfer epoch2 node1)
    )
  )
)
(assert
  (or
    (=
      (ep node0)
      epoch0
    )
    (not
      (=
        (ep node0)
        epoch1
      )
    )
    (=
      (ep node0)
      epoch2
    )
    (not
      (=
        (ep node1)
        epoch0
      )
    )
    (=
      (ep node1)
      epoch1
    )
    (=
      (ep node1)
      epoch2
    )
    (held node0)
    (held node1)
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (not
      (transfer epoch2 node0)
    )
    (transfer epoch2 node1)
  )
)
(assert
  (or
    (=
      (ep node0)
      epoch0
    )
    (not
      (=
        (ep node0)
        epoch1
      )
    )
    (=
      (ep node0)
      epoch2
    )
    (not
      (=
        (ep node1)
        epoch0
      )
    )
    (=
      (ep node1)
      epoch1
    )
    (=
      (ep node1)
      epoch2
    )
    (not
      (held node0)
    )
    (held node1)
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (transfer epoch2 node1)
  )
)
(assert
  (or
    (not
      (=
        (ep node0)
        epoch0
      )
    )
    (=
      (ep node0)
      epoch1
    )
    (=
      (ep node0)
      epoch2
    )
    (=
      (ep node1)
      epoch0
    )
    (not
      (=
        (ep node1)
        epoch1
      )
    )
    (=
      (ep node1)
      epoch2
    )
    (held node0)
    (held node1)
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (locked epoch2 node1)
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (not
      (transfer epoch2 node0)
    )
    (transfer epoch2 node1)
  )
)
(assert
  (or
    (=
      (ep node0)
      epoch0
    )
    (not
      (=
        (ep node0)
        epoch1
      )
    )
    (=
      (ep node0)
      epoch2
    )
    (=
      (ep node1)
      epoch0
    )
    (=
      (ep node1)
      epoch1
    )
    (not
      (=
        (ep node1)
        epoch2
      )
    )
    (held node0)
    (not
      (held node1)
    )
    (locked epoch0 node0)
    (locked epoch0 node1)
    (locked epoch1 node0)
    (locked epoch1 node1)
    (locked epoch2 node0)
    (not
      (locked epoch2 node1)
    )
    (transfer epoch0 node0)
    (transfer epoch0 node1)
    (transfer epoch1 node0)
    (transfer epoch1 node1)
    (transfer epoch2 node0)
    (transfer epoch2 node1)
  )
)
(check-sat)
