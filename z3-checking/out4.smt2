; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes ((Node 0)) (((node0) (node1))))
(declare-datatypes ((Epoch 0)) (((epoch0) (epoch1) (epoch2) (epoch3))))
(declare-fun locked (Epoch Node) Bool)
(declare-fun transfer (Epoch Node) Bool)
(declare-fun ep (Node) Epoch)
(declare-fun held (Node) Bool)
(declare-fun le (Epoch Epoch) Bool)
(declare-fun first () Node)
; ===== Orbit Group F1 =====
; 1: forall N. ~locked_epoch1(N)
(declare-fun orbit_group_F1 () Bool)
(assert (= orbit_group_F1 (and (not (locked epoch1 node0)) (not (locked epoch1 node1)))))

; ===== Orbit Group F2 =====
; 2: forall N. ~transfer_epoch0(N)
; 3: forall N. ~transfer_epoch1(N)
(declare-fun orbit_group_F2 () Bool)
(assert (= orbit_group_F2 (and (not (transfer epoch0 node0)) (not (transfer epoch0 node1)) (not (transfer epoch1 node0)) (not (transfer epoch1 node1)))))

; ===== Orbit Group F3 =====
; 5: forall N. ~ep_epoch0(N) | ~ep_epoch1(N)
; 6: forall N. ~ep_epoch0(N) | ~ep_epoch2(N)
; 10: forall N. ~ep_epoch1(N) | ~ep_epoch2(N)
; 7: forall N. ~ep_epoch0(N) | ~ep_epoch3(N)
; 13: forall N. ~ep_epoch1(N) | ~ep_epoch3(N)
; 17: forall N. ~ep_epoch2(N) | ~ep_epoch3(N)
(declare-fun orbit_group_F3 () Bool)
(assert (= orbit_group_F3 (and (or (not (= (ep node0) epoch0)) (not (= (ep node0) epoch1))) (or (not (= (ep node1) epoch0)) (not (= (ep node1) epoch1))) (or (not (= (ep node0) epoch0)) (not (= (ep node0) epoch2))) (or (not (= (ep node1) epoch0)) (not (= (ep node1) epoch2))) (or (not (= (ep node0) epoch1)) (not (= (ep node0) epoch2))) (or (not (= (ep node1) epoch1)) (not (= (ep node1) epoch2))) (or (not (= (ep node0) epoch0)) (not (= (ep node0) epoch3))) (or (not (= (ep node1) epoch0)) (not (= (ep node1) epoch3))) (or (not (= (ep node0) epoch1)) (not (= (ep node0) epoch3))) (or (not (= (ep node1) epoch1)) (not (= (ep node1) epoch3))) (or (not (= (ep node0) epoch2)) (not (= (ep node0) epoch3))) (or (not (= (ep node1) epoch2)) (not (= (ep node1) epoch3))))))

; ===== Orbit Group F4 =====
; 7: forall N. ~ep_epoch0(N) | ~held(N)
(declare-fun orbit_group_F4 () Bool)
(assert (= orbit_group_F4 (and (or (not (= (ep node0) epoch0)) (not (held node0))) (or (not (= (ep node1) epoch0)) (not (held node1))))))

; ===== Orbit Group F5 =====
; 8: forall N. ~ep_epoch0(N) | ~locked_epoch2(N)
; 11: forall N. ~ep_epoch1(N) | ~locked_epoch2(N)
; 10: forall N. ~ep_epoch0(N) | ~locked_epoch3(N)
; 15: forall N. ~ep_epoch1(N) | ~locked_epoch3(N)
; 19: forall N. ~ep_epoch2(N) | ~locked_epoch3(N)
(declare-fun orbit_group_F5 () Bool)
(assert (= orbit_group_F5 (and (or (not (= (ep node0) epoch0)) (not (locked epoch2 node0))) (or (not (= (ep node1) epoch0)) (not (locked epoch2 node1))) (or (not (= (ep node0) epoch1)) (not (locked epoch2 node0))) (or (not (= (ep node1) epoch1)) (not (locked epoch2 node1))) (or (not (= (ep node0) epoch0)) (not (locked epoch3 node0))) (or (not (= (ep node1) epoch0)) (not (locked epoch3 node1))) (or (not (= (ep node0) epoch1)) (not (locked epoch3 node0))) (or (not (= (ep node1) epoch1)) (not (locked epoch3 node1))) (or (not (= (ep node0) epoch2)) (not (locked epoch3 node0))) (or (not (= (ep node1) epoch2)) (not (locked epoch3 node1))))))

; ===== Orbit Group F6 =====
; 23: forall N1,N0. ~ep_epoch3(N0) | ~held(N1) | N0 = N1
(declare-fun orbit_group_F6 () Bool)
(assert (= orbit_group_F6 (and (or (or (not (= (ep node0) epoch3)) (not (held node0))) (= node0 node0)) (or (or (not (= (ep node1) epoch3)) (not (held node0))) (= node1 node0)) (or (or (not (= (ep node0) epoch3)) (not (held node1))) (= node0 node1)) (or (or (not (= (ep node1) epoch3)) (not (held node1))) (= node1 node1)))))

; ===== Orbit Group F7 =====
; 14: forall N1,N0. ~ep_epoch2(N0) | ~locked_epoch2(N1) | N0 = N1
; 24: forall N1,N0. ~ep_epoch3(N0) | ~locked_epoch3(N1) | N0 = N1
(declare-fun orbit_group_F7 () Bool)
(assert (= orbit_group_F7 (and (or (or (not (= (ep node0) epoch2)) (not (locked epoch2 node0))) (= node0 node0)) (or (or (not (= (ep node1) epoch2)) (not (locked epoch2 node0))) (= node1 node0)) (or (or (not (= (ep node0) epoch2)) (not (locked epoch2 node1))) (= node0 node1)) (or (or (not (= (ep node1) epoch2)) (not (locked epoch2 node1))) (= node1 node1)) (or (or (not (= (ep node0) epoch3)) (not (locked epoch3 node0))) (= node0 node0)) (or (or (not (= (ep node1) epoch3)) (not (locked epoch3 node0))) (= node1 node0)) (or (or (not (= (ep node0) epoch3)) (not (locked epoch3 node1))) (= node0 node1)) (or (or (not (= (ep node1) epoch3)) (not (locked epoch3 node1))) (= node1 node1)))))

; ===== Orbit Group F8 =====
; 15: forall N1,N0. ~ep_epoch2(N0) | ~transfer_epoch2(N1)
; 25: forall N1,N0. ~ep_epoch3(N0) | ~transfer_epoch2(N1)
; 26: forall N1,N0. ~ep_epoch3(N0) | ~transfer_epoch3(N1)
(declare-fun orbit_group_F8 () Bool)
(assert (= orbit_group_F8 (and (or (not (= (ep node0) epoch2)) (not (transfer epoch2 node0))) (or (not (= (ep node1) epoch2)) (not (transfer epoch2 node0))) (or (not (= (ep node0) epoch2)) (not (transfer epoch2 node1))) (or (not (= (ep node1) epoch2)) (not (transfer epoch2 node1))) (or (not (= (ep node0) epoch3)) (not (transfer epoch2 node0))) (or (not (= (ep node1) epoch3)) (not (transfer epoch2 node0))) (or (not (= (ep node0) epoch3)) (not (transfer epoch2 node1))) (or (not (= (ep node1) epoch3)) (not (transfer epoch2 node1))) (or (not (= (ep node0) epoch3)) (not (transfer epoch3 node0))) (or (not (= (ep node1) epoch3)) (not (transfer epoch3 node0))) (or (not (= (ep node0) epoch3)) (not (transfer epoch3 node1))) (or (not (= (ep node1) epoch3)) (not (transfer epoch3 node1))))))

; ===== Orbit Group F9 =====
; 27: forall N. ~ep_epoch3(N) | held(N)
(declare-fun orbit_group_F9 () Bool)
(assert (= orbit_group_F9 (and (or (not (= (ep node0) epoch3)) (held node0)) (or (not (= (ep node1) epoch3)) (held node1)))))

; ===== Orbit Group F10 =====
; 17: forall N. ~ep_epoch2(N) | locked_epoch2(N)
; 28: forall N. ~ep_epoch3(N) | locked_epoch3(N)
(declare-fun orbit_group_F10 () Bool)
(assert (= orbit_group_F10 (and (or (not (= (ep node0) epoch2)) (locked epoch2 node0)) (or (not (= (ep node1) epoch2)) (locked epoch2 node1)) (or (not (= (ep node0) epoch3)) (locked epoch3 node0)) (or (not (= (ep node1) epoch3)) (locked epoch3 node1)))))

; ===== Orbit Group F11 =====
; 30: forall N1,N0. ~held(N0) | ~locked_epoch3(N1) | N0 = N1
(declare-fun orbit_group_F11 () Bool)
(assert (= orbit_group_F11 (and (or (or (not (held node0)) (not (locked epoch3 node0))) (= node0 node0)) (or (or (not (held node1)) (not (locked epoch3 node0))) (= node1 node0)) (or (or (not (held node0)) (not (locked epoch3 node1))) (= node0 node1)) (or (or (not (held node1)) (not (locked epoch3 node1))) (= node1 node1)))))

; ===== Orbit Group F12 =====
; 20: forall N1,N0. ~held(N0) | ~transfer_epoch2(N1)
; 32: forall N1,N0. ~held(N0) | ~transfer_epoch3(N1)
(declare-fun orbit_group_F12 () Bool)
(assert (= orbit_group_F12 (and (or (not (held node0)) (not (transfer epoch2 node0))) (or (not (held node1)) (not (transfer epoch2 node0))) (or (not (held node0)) (not (transfer epoch2 node1))) (or (not (held node1)) (not (transfer epoch2 node1))) (or (not (held node0)) (not (transfer epoch3 node0))) (or (not (held node1)) (not (transfer epoch3 node0))) (or (not (held node0)) (not (transfer epoch3 node1))) (or (not (held node1)) (not (transfer epoch3 node1))))))

; ===== Orbit Group F13 =====
; 22: forall N1,N0. ~locked_epoch2(N0) | ~transfer_epoch2(N1)
; 36: forall N1,N0. ~locked_epoch3(N0) | ~transfer_epoch2(N1)
; 37: forall N1,N0. ~locked_epoch3(N0) | ~transfer_epoch3(N1)
(declare-fun orbit_group_F13 () Bool)
(assert (= orbit_group_F13 (and (or (not (locked epoch2 node0)) (not (transfer epoch2 node0))) (or (not (locked epoch2 node1)) (not (transfer epoch2 node0))) (or (not (locked epoch2 node0)) (not (transfer epoch2 node1))) (or (not (locked epoch2 node1)) (not (transfer epoch2 node1))) (or (not (locked epoch3 node0)) (not (transfer epoch2 node0))) (or (not (locked epoch3 node1)) (not (transfer epoch2 node0))) (or (not (locked epoch3 node0)) (not (transfer epoch2 node1))) (or (not (locked epoch3 node1)) (not (transfer epoch2 node1))) (or (not (locked epoch3 node0)) (not (transfer epoch3 node0))) (or (not (locked epoch3 node1)) (not (transfer epoch3 node0))) (or (not (locked epoch3 node0)) (not (transfer epoch3 node1))) (or (not (locked epoch3 node1)) (not (transfer epoch3 node1))))))

; ===== Orbit Group F14 =====
; 38: forall N. ~locked_epoch3(N) | ep_epoch3(N)
(declare-fun orbit_group_F14 () Bool)
(assert (= orbit_group_F14 (and (or (not (locked epoch3 node0)) (= (ep node0) epoch3)) (or (not (locked epoch3 node1)) (= (ep node1) epoch3)))))

; ===== Orbit Group F15 =====
; 39: forall N. ~locked_epoch3(N) | held(N)
(declare-fun orbit_group_F15 () Bool)
(assert (= orbit_group_F15 (and (or (not (locked epoch3 node0)) (held node0)) (or (not (locked epoch3 node1)) (held node1)))))

; ===== Orbit Group F16 =====
; 41: forall N1,N0. ~transfer_epoch2(N0) | ~transfer_epoch3(N1)
(declare-fun orbit_group_F16 () Bool)
(assert (= orbit_group_F16 (and (or (not (transfer epoch2 node0)) (not (transfer epoch3 node0))) (or (not (transfer epoch2 node1)) (not (transfer epoch3 node0))) (or (not (transfer epoch2 node0)) (not (transfer epoch3 node1))) (or (not (transfer epoch2 node1)) (not (transfer epoch3 node1))))))

; ===== Orbit Group E1 =====
; 4: exists N. ~ep_epoch0(N)
; 9: exists N. ~ep_epoch1(N)
; 12: exists N. ~ep_epoch2(N)
; 22: exists N. ~ep_epoch3(N)
(declare-fun orbit_group_E1 () Bool)
(assert (= orbit_group_E1 (and (or (not (= (ep node0) epoch0)) (not (= (ep node1) epoch0))) (or (not (= (ep node0) epoch1)) (not (= (ep node1) epoch1))) (or (not (= (ep node0) epoch2)) (not (= (ep node1) epoch2))) (or (not (= (ep node0) epoch3)) (not (= (ep node1) epoch3))))))

; ===== Orbit Group E2 =====
; 18: exists N. ~held(N)
(declare-fun orbit_group_E2 () Bool)
(assert (= orbit_group_E2 (or (not (held node0)) (not (held node1)))))

; ===== Orbit Group E3 =====
; 21: exists N. ~locked_epoch2(N)
; 35: exists N. ~locked_epoch3(N)
(declare-fun orbit_group_E3 () Bool)
(assert (= orbit_group_E3 (and (or (not (locked epoch2 node0)) (not (locked epoch2 node1))) (or (not (locked epoch3 node0)) (not (locked epoch3 node1))))))

; ===== Orbit Group E4 =====
; 25: exists N. ~transfer_epoch2(N)
; 42: exists N. ~transfer_epoch3(N)
(declare-fun orbit_group_E4 () Bool)
(assert (= orbit_group_E4 (and (or (not (transfer epoch2 node0)) (not (transfer epoch2 node1))) (or (not (transfer epoch3 node0)) (not (transfer epoch3 node1))))))

; ===== Orbit Group E5 =====
; 161: exists N. ep_epoch0(N) | ep_epoch1(N) | ep_epoch2(N)
; 162: exists N. ep_epoch0(N) | ep_epoch1(N) | ep_epoch3(N)
; 168: exists N. ep_epoch0(N) | ep_epoch2(N) | ep_epoch3(N)
; 180: exists N. ep_epoch1(N) | ep_epoch2(N) | ep_epoch3(N)
(declare-fun orbit_group_E5 () Bool)
(assert (= orbit_group_E5 (and (or (or (or (= (ep node0) epoch0) (= (ep node0) epoch1)) (= (ep node0) epoch2)) (or (or (= (ep node1) epoch0) (= (ep node1) epoch1)) (= (ep node1) epoch2))) (or (or (or (= (ep node0) epoch0) (= (ep node0) epoch1)) (= (ep node0) epoch3)) (or (or (= (ep node1) epoch0) (= (ep node1) epoch1)) (= (ep node1) epoch3))) (or (or (or (= (ep node0) epoch0) (= (ep node0) epoch2)) (= (ep node0) epoch3)) (or (or (= (ep node1) epoch0) (= (ep node1) epoch2)) (= (ep node1) epoch3))) (or (or (or (= (ep node0) epoch1) (= (ep node0) epoch2)) (= (ep node0) epoch3)) (or (or (= (ep node1) epoch1) (= (ep node1) epoch2)) (= (ep node1) epoch3))))))

; ===== Orbit Group E6 =====
; 155: exists N. ep_epoch0(N) | ep_epoch1(N) | held(N)
; 171: exists N. ep_epoch0(N) | ep_epoch2(N) | held(N)
; 183: exists N. ep_epoch1(N) | ep_epoch2(N) | held(N)
(declare-fun orbit_group_E6 () Bool)
(assert (= orbit_group_E6 (and (or (or (or (= (ep node0) epoch0) (= (ep node0) epoch1)) (held node0)) (or (or (= (ep node1) epoch0) (= (ep node1) epoch1)) (held node1))) (or (or (or (= (ep node0) epoch0) (= (ep node0) epoch2)) (held node0)) (or (or (= (ep node1) epoch0) (= (ep node1) epoch2)) (held node1))) (or (or (or (= (ep node0) epoch1) (= (ep node0) epoch2)) (held node0)) (or (or (= (ep node1) epoch1) (= (ep node1) epoch2)) (held node1))))))

; ===== Orbit Group E7 =====
; 57: exists N. ep_epoch0(N) | locked_epoch2(N)
; 63: exists N. ep_epoch1(N) | locked_epoch2(N)
; 167: exists N. ep_epoch0(N) | ep_epoch1(N) | locked_epoch3(N)
; 173: exists N. ep_epoch0(N) | ep_epoch2(N) | locked_epoch3(N)
; 185: exists N. ep_epoch1(N) | ep_epoch2(N) | locked_epoch3(N)
(declare-fun orbit_group_E7 () Bool)
(assert (= orbit_group_E7 (and (or (or (= (ep node0) epoch0) (locked epoch2 node0)) (or (= (ep node1) epoch0) (locked epoch2 node1))) (or (or (= (ep node0) epoch1) (locked epoch2 node0)) (or (= (ep node1) epoch1) (locked epoch2 node1))) (or (or (or (= (ep node0) epoch0) (= (ep node0) epoch1)) (locked epoch3 node0)) (or (or (= (ep node1) epoch0) (= (ep node1) epoch1)) (locked epoch3 node1))) (or (or (or (= (ep node0) epoch0) (= (ep node0) epoch2)) (locked epoch3 node0)) (or (or (= (ep node1) epoch0) (= (ep node1) epoch2)) (locked epoch3 node1))) (or (or (or (= (ep node0) epoch1) (= (ep node0) epoch2)) (locked epoch3 node0)) (or (or (= (ep node1) epoch1) (= (ep node1) epoch2)) (locked epoch3 node1))))))

; ===== Orbit Group E8 =====
; 192: exists N. held(N) | transfer_epoch0(N) | transfer_epoch1(N) | transfer_epoch2(N) | transfer_epoch3(N)
(declare-fun orbit_group_E8 () Bool)
(assert (= orbit_group_E8 (or (or (or (or (or (held node0) (transfer epoch0 node0)) (transfer epoch1 node0)) (transfer epoch2 node0)) (transfer epoch3 node0)) (or (or (or (or (held node1) (transfer epoch0 node1)) (transfer epoch1 node1)) (transfer epoch2 node1)) (transfer epoch3 node1)))))

; ===== Orbit Group F16 =====
; 100: locked(epoch0,node0) => transfer(epoch0,node0)
; 101: transfer(epoch0,node0) => locked(epoch0,node0)
; 102: locked(epoch0,node1) => transfer(epoch0,node1)
; 103: transfer(epoch0,node1) => locked(epoch0,node1)
; 104: locked(epoch1,node0) => transfer(epoch1,node0)
; 105: transfer(epoch1,node0) => locked(epoch1,node0)
; 106: locked(epoch1,node1) => transfer(epoch1,node1)
; 107: transfer(epoch1,node1) => locked(epoch1,node1)
(declare-fun orbit_group_F16 () Bool)
(assert (= orbit_group_F16 (and (or (not (locked epoch0 node0)) (transfer epoch0 node0)) (or (not (transfer epoch0 node0)) (locked epoch0 node0)) (or (not (locked epoch0 node1)) (transfer epoch0 node1)) (or (not (transfer epoch0 node1)) (locked epoch0 node1)) (or (not (locked epoch1 node0)) (transfer epoch1 node0)) (or (not (transfer epoch1 node0)) (locked epoch1 node0)) (or (not (locked epoch1 node1)) (transfer epoch1 node1)) (or (not (transfer epoch1 node1)) (locked epoch1 node1)))))

; ===== Orbit Group F17 =====
; 108: forall N0,N1. forall E0,E1. (held(N0) & ep(N0)=E0 & ep(N1)=E1) => le(E1,E0)
(declare-fun orbit_group_F17 () Bool)
(assert (= orbit_group_F17 (and (and (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node0) epoch0))) (le epoch0 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node0) epoch1))) (le epoch1 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node0) epoch2))) (le epoch2 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node0) epoch3))) (le epoch3 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node0) epoch0))) (le epoch0 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node0) epoch1))) (le epoch1 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node0) epoch2))) (le epoch2 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node0) epoch3))) (le epoch3 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node0) epoch0))) (le epoch0 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node0) epoch1))) (le epoch1 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node0) epoch2))) (le epoch2 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node0) epoch3))) (le epoch3 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node0) epoch0))) (le epoch0 epoch3)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node0) epoch1))) (le epoch1 epoch3)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node0) epoch2))) (le epoch2 epoch3)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node0) epoch3))) (le epoch3 epoch3))) (and (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node1) epoch0))) (le epoch0 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node1) epoch1))) (le epoch1 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node1) epoch2))) (le epoch2 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch0)) (= (ep node1) epoch3))) (le epoch3 epoch0)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node1) epoch0))) (le epoch0 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node1) epoch1))) (le epoch1 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node1) epoch2))) (le epoch2 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch1)) (= (ep node1) epoch3))) (le epoch3 epoch1)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node1) epoch0))) (le epoch0 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node1) epoch1))) (le epoch1 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node1) epoch2))) (le epoch2 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch2)) (= (ep node1) epoch3))) (le epoch3 epoch2)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node1) epoch0))) (le epoch0 epoch3)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node1) epoch1))) (le epoch1 epoch3)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node1) epoch2))) (le epoch2 epoch3)) (or (not (and (and (held node0) (= (ep node0) epoch3)) (= (ep node1) epoch3))) (le epoch3 epoch3))) (and (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node0) epoch0))) (le epoch0 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node0) epoch1))) (le epoch1 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node0) epoch2))) (le epoch2 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node0) epoch3))) (le epoch3 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node0) epoch0))) (le epoch0 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node0) epoch1))) (le epoch1 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node0) epoch2))) (le epoch2 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node0) epoch3))) (le epoch3 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node0) epoch0))) (le epoch0 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node0) epoch1))) (le epoch1 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node0) epoch2))) (le epoch2 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node0) epoch3))) (le epoch3 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node0) epoch0))) (le epoch0 epoch3)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node0) epoch1))) (le epoch1 epoch3)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node0) epoch2))) (le epoch2 epoch3)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node0) epoch3))) (le epoch3 epoch3))) (and (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node1) epoch0))) (le epoch0 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node1) epoch1))) (le epoch1 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node1) epoch2))) (le epoch2 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch0)) (= (ep node1) epoch3))) (le epoch3 epoch0)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node1) epoch0))) (le epoch0 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node1) epoch1))) (le epoch1 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node1) epoch2))) (le epoch2 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch1)) (= (ep node1) epoch3))) (le epoch3 epoch1)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node1) epoch0))) (le epoch0 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node1) epoch1))) (le epoch1 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node1) epoch2))) (le epoch2 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch2)) (= (ep node1) epoch3))) (le epoch3 epoch2)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node1) epoch0))) (le epoch0 epoch3)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node1) epoch1))) (le epoch1 epoch3)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node1) epoch2))) (le epoch2 epoch3)) (or (not (and (and (held node1) (= (ep node1) epoch3)) (= (ep node1) epoch3))) (le epoch3 epoch3))))))

; --- interpreted atoms begin: 30 constraints ---
; interpreted[0] (first=node0) = 1
(assert (= first node0))
; interpreted[1] (first=node1) = 0
(assert (not (= first node1)))
; interpreted[2] (firste=epoch0) = 0
(assert (not (= epoch1 epoch0)))
; interpreted[3] (firste=epoch1) = 1
(assert (= epoch1 epoch1))
; interpreted[4] (firste=epoch2) = 0
(assert (not (= epoch1 epoch2)))
; interpreted[5] (firste=epoch3) = 0
(assert (not (= epoch1 epoch3)))
; interpreted[6] le(epoch0,epoch0) = 1
(assert (le epoch0 epoch0))
; interpreted[7] le(epoch0,epoch1) = 1
(assert (le epoch0 epoch1))
; interpreted[8] le(epoch0,epoch2) = 1
(assert (le epoch0 epoch2))
; interpreted[9] le(epoch0,epoch3) = 1
(assert (le epoch0 epoch3))
; interpreted[10] le(epoch1,epoch0) = 0
(assert (not (le epoch1 epoch0)))
; interpreted[11] le(epoch1,epoch1) = 1
(assert (le epoch1 epoch1))
; interpreted[12] le(epoch1,epoch2) = 1
(assert (le epoch1 epoch2))
; interpreted[13] le(epoch1,epoch3) = 1
(assert (le epoch1 epoch3))
; interpreted[14] le(epoch2,epoch0) = 0
(assert (not (le epoch2 epoch0)))
; interpreted[15] le(epoch2,epoch1) = 0
(assert (not (le epoch2 epoch1)))
; interpreted[16] le(epoch2,epoch2) = 1
(assert (le epoch2 epoch2))
; interpreted[17] le(epoch2,epoch3) = 1
(assert (le epoch2 epoch3))
; interpreted[18] le(epoch3,epoch0) = 0
(assert (not (le epoch3 epoch0)))
; interpreted[19] le(epoch3,epoch1) = 0
(assert (not (le epoch3 epoch1)))
; interpreted[20] le(epoch3,epoch2) = 0
(assert (not (le epoch3 epoch2)))
; interpreted[21] le(epoch3,epoch3) = 1
(assert (le epoch3 epoch3))
; interpreted[22] (max=epoch0) = 0
(assert (not (= epoch3 epoch0)))
; interpreted[23] (max=epoch1) = 0
(assert (not (= epoch3 epoch1)))
; interpreted[24] (max=epoch2) = 0
(assert (not (= epoch3 epoch2)))
; interpreted[25] (max=epoch3) = 1
(assert (= epoch3 epoch3))
; interpreted[26] (zero=epoch0) = 1
(assert (= epoch0 epoch0))
; interpreted[27] (zero=epoch1) = 0
(assert (not (= epoch0 epoch1)))
; interpreted[28] (zero=epoch2) = 0
(assert (not (= epoch0 epoch2)))
; interpreted[29] (zero=epoch3) = 0
(assert (not (= epoch0 epoch3)))

; --- reachable state exclusions begin: excluding 24 reachable states ---
; reachable[0] bits: 00101000000000100000000001
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (not (= (ep node0) epoch2)) (= (ep node0) epoch3) (not (= (ep node1) epoch0)) (= (ep node1) epoch1) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (not (transfer epoch3 node1))))
; reachable[1] bits: 00011000100000101000000000
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (= (ep node0) epoch2) (not (= (ep node0) epoch3)) (not (= (ep node1) epoch0)) (= (ep node1) epoch1) (= (ep node1) epoch2) (= (ep node1) epoch3) (not (held node0)) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (not (locked epoch3 node0)) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[2] bits: 00010010100000011000000000
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (= (ep node0) epoch2) (not (= (ep node0) epoch3)) (= (ep node1) epoch0) (= (ep node1) epoch1) (not (= (ep node1) epoch2)) (= (ep node1) epoch3) (not (held node0)) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (not (locked epoch3 node0)) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[3] bits: 00100100100000100000000000
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (not (= (ep node0) epoch2)) (= (ep node0) epoch3) (= (ep node1) epoch0) (not (= (ep node1) epoch1)) (= (ep node1) epoch2) (= (ep node1) epoch3) (not (held node0)) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[4] bits: 10000001010000010100000000
(assert (or (not (= (ep node0) epoch0)) (= (ep node0) epoch1) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (= (ep node1) epoch2) (not (= (ep node1) epoch3)) (held node0) (not (held node1)) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (not (locked epoch3 node1)) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[5] bits: 00100100000000100000000010
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (not (= (ep node0) epoch2)) (= (ep node0) epoch3) (= (ep node1) epoch0) (not (= (ep node1) epoch1)) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (not (transfer epoch3 node0)) (transfer epoch3 node1)))
; reachable[6] bits: 01001000100000000000000000
(assert (or (= (ep node0) epoch0) (not (= (ep node0) epoch1)) (= (ep node0) epoch2) (= (ep node0) epoch3) (not (= (ep node1) epoch0)) (= (ep node1) epoch1) (= (ep node1) epoch2) (= (ep node1) epoch3) (not (held node0)) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[7] bits: 10000010000000010000000001
(assert (or (not (= (ep node0) epoch0)) (= (ep node0) epoch1) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (not (= (ep node1) epoch2)) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (not (transfer epoch3 node1))))
; reachable[8] bits: 10000100000000000000001000
(assert (or (not (= (ep node0) epoch0)) (= (ep node0) epoch1) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (not (= (ep node1) epoch1)) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (not (transfer epoch2 node0)) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[9] bits: 01000010000000010000000001
(assert (or (= (ep node0) epoch0) (not (= (ep node0) epoch1)) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (not (= (ep node1) epoch2)) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (not (transfer epoch3 node1))))
; reachable[10] bits: 00100001010000100100000000
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (not (= (ep node0) epoch2)) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (= (ep node1) epoch2) (not (= (ep node1) epoch3)) (held node0) (not (held node1)) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (locked epoch3 node0) (not (locked epoch3 node1)) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[11] bits: 01000001010000010100000000
(assert (or (= (ep node0) epoch0) (not (= (ep node0) epoch1)) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (= (ep node1) epoch2) (not (= (ep node1) epoch3)) (held node0) (not (held node1)) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (not (locked epoch3 node1)) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[12] bits: 00100100000000100000000001
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (not (= (ep node0) epoch2)) (= (ep node0) epoch3) (= (ep node1) epoch0) (not (= (ep node1) epoch1)) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (not (transfer epoch3 node1))))
; reachable[13] bits: 00010100100000101000000000
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (= (ep node0) epoch2) (not (= (ep node0) epoch3)) (= (ep node1) epoch0) (not (= (ep node1) epoch1)) (= (ep node1) epoch2) (= (ep node1) epoch3) (not (held node0)) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (not (locked epoch3 node0)) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[14] bits: 10000010010000010000000000
(assert (or (not (= (ep node0) epoch0)) (= (ep node0) epoch1) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (not (= (ep node1) epoch2)) (= (ep node1) epoch3) (held node0) (not (held node1)) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[15] bits: 01001000000000000000000100
(assert (or (= (ep node0) epoch0) (not (= (ep node0) epoch1)) (= (ep node0) epoch2) (= (ep node0) epoch3) (not (= (ep node1) epoch0)) (= (ep node1) epoch1) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (not (transfer epoch2 node1)) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[16] bits: 10000100010000000000000000
(assert (or (not (= (ep node0) epoch0)) (= (ep node0) epoch1) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (not (= (ep node1) epoch1)) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (not (held node1)) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[17] bits: 10000100000000000000000100
(assert (or (not (= (ep node0) epoch0)) (= (ep node0) epoch1) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (not (= (ep node1) epoch1)) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (not (transfer epoch2 node1)) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[18] bits: 01000010000000010000000010
(assert (or (= (ep node0) epoch0) (not (= (ep node0) epoch1)) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (not (= (ep node1) epoch2)) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (not (transfer epoch3 node0)) (transfer epoch3 node1)))
; reachable[19] bits: 10000010000000010000000010
(assert (or (not (= (ep node0) epoch0)) (= (ep node0) epoch1) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (not (= (ep node1) epoch2)) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (not (transfer epoch3 node0)) (transfer epoch3 node1)))
; reachable[20] bits: 01001000000000000000001000
(assert (or (= (ep node0) epoch0) (not (= (ep node0) epoch1)) (= (ep node0) epoch2) (= (ep node0) epoch3) (not (= (ep node1) epoch0)) (= (ep node1) epoch1) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (not (transfer epoch2 node0)) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[21] bits: 01000010010000010000000000
(assert (or (= (ep node0) epoch0) (not (= (ep node0) epoch1)) (= (ep node0) epoch2) (= (ep node0) epoch3) (= (ep node1) epoch0) (= (ep node1) epoch1) (not (= (ep node1) epoch2)) (= (ep node1) epoch3) (held node0) (not (held node1)) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (locked epoch2 node0) (not (locked epoch2 node1)) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[22] bits: 00101000100000100000000000
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (not (= (ep node0) epoch2)) (= (ep node0) epoch3) (not (= (ep node1) epoch0)) (= (ep node1) epoch1) (= (ep node1) epoch2) (= (ep node1) epoch3) (not (held node0)) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (transfer epoch3 node0) (transfer epoch3 node1)))
; reachable[23] bits: 00101000000000100000000010
(assert (or (= (ep node0) epoch0) (= (ep node0) epoch1) (not (= (ep node0) epoch2)) (= (ep node0) epoch3) (not (= (ep node1) epoch0)) (= (ep node1) epoch1) (= (ep node1) epoch2) (= (ep node1) epoch3) (held node0) (held node1) (locked epoch0 node0) (locked epoch0 node1) (locked epoch1 node0) (locked epoch1 node1) (not (locked epoch2 node0)) (locked epoch2 node1) (locked epoch3 node0) (locked epoch3 node1) (transfer epoch0 node0) (transfer epoch0 node1) (transfer epoch1 node0) (transfer epoch1 node1) (transfer epoch2 node0) (transfer epoch2 node1) (not (transfer epoch3 node0)) (transfer epoch3 node1)))

; --- orbit-group variables asserted true: 26 groups ---
(assert orbit_group_F1)
(assert orbit_group_F2)
(assert orbit_group_F3)
(assert orbit_group_F4)
(assert orbit_group_F5)
(assert orbit_group_F6)
(assert orbit_group_F7)
(assert orbit_group_F8)
(assert orbit_group_F9)
(assert orbit_group_F10)
(assert orbit_group_F11)
(assert orbit_group_F12)
(assert orbit_group_F13)
(assert orbit_group_F14)
(assert orbit_group_F15)
(assert orbit_group_F16)
(assert orbit_group_E1)
(assert orbit_group_E2)
(assert orbit_group_E3)
(assert orbit_group_E4)
(assert orbit_group_E5)
(assert orbit_group_E6)
(assert orbit_group_E7)
(assert orbit_group_E8)
(assert orbit_group_F16)
(assert orbit_group_F17)

(check-sat)
