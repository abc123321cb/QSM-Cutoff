(declare-datatypes () ((node n0 n1)))
; quantified formulas
forall NODE0. ~locked_epoch0(NODE0)
forall NODE0. ~transfer_epoch1(NODE0)
forall NODE0. ~ep_epoch1(NODE0) | ~ep_epoch0(NODE0)
forall NODE0. ~ep_epoch2(NODE0) | ~ep_epoch0(NODE0)
forall NODE0. ~ep_epoch0(NODE0) | ~ep_epoch3(NODE0)
forall NODE0. ~ep_epoch0(NODE0) | ~held(NODE0)
forall NODE0. ~ep_epoch0(NODE0) | ~locked_epoch1(NODE0)
forall NODE0. ~locked_epoch2(NODE0) | ~ep_epoch0(NODE0)
forall NODE0. ~ep_epoch0(NODE0) | ~locked_epoch3(NODE0)
forall NODE0,NODE1. locked_epoch1(NODE1) | ~ep_epoch0(NODE0) | NODE0 = NODE1
forall NODE0. ~ep_epoch1(NODE0) | ~ep_epoch2(NODE0)
forall NODE0. ~ep_epoch1(NODE0) | ~ep_epoch3(NODE0)
forall NODE0,NODE1. ~locked_epoch1(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0. ~locked_epoch2(NODE0) | ~ep_epoch1(NODE0)
forall NODE0. ~locked_epoch3(NODE0) | ~ep_epoch1(NODE0)
forall NODE0. locked_epoch1(NODE0) | ~ep_epoch1(NODE0)
forall NODE0. ~ep_epoch2(NODE0) | ~ep_epoch3(NODE0)
forall NODE0,NODE1. ~locked_epoch2(NODE1) | ~ep_epoch2(NODE0) | NODE0 = NODE1
forall NODE0. ~ep_epoch2(NODE0) | ~locked_epoch3(NODE0)
forall NODE0,NODE1. ~ep_epoch2(NODE0) | ~transfer_epoch2(NODE1)
forall NODE0. ~ep_epoch2(NODE0) | locked_epoch2(NODE0)
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ~held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ~locked_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ~transfer_epoch2(NODE1)
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ~transfer_epoch3(NODE1)
forall NODE0. held(NODE0) | ~ep_epoch3(NODE0)
forall NODE0. ~ep_epoch3(NODE0) | locked_epoch3(NODE0)
forall NODE0,NODE1. ~held(NODE0) | ~locked_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~held(NODE0) | ~transfer_epoch2(NODE1)
forall NODE0,NODE1. ~held(NODE0) | ~transfer_epoch3(NODE1)
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ~transfer_epoch2(NODE1)
forall NODE0,NODE1. ~transfer_epoch2(NODE1) | ~locked_epoch3(NODE0)
forall NODE0,NODE1. ~locked_epoch3(NODE0) | ~transfer_epoch3(NODE1)
forall NODE0. ep_epoch3(NODE0) | ~locked_epoch3(NODE0)
forall NODE0. held(NODE0) | ~locked_epoch3(NODE0)
forall NODE0,NODE1. ~transfer_epoch3(NODE1) | ~transfer_epoch2(NODE0)
forall NODE0,NODE1. ~held(NODE0) | ~ep_epoch2(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE1) | ~held(NODE0) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE1) | ~held(NODE0) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~held(NODE1) | ~ep_epoch2(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | ~held(NODE1) | ~ep_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~locked_epoch2(NODE1) | ~ep_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~locked_epoch2(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ~locked_epoch2(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE1) | ~held(NODE0) | locked_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | ~transfer_epoch2(NODE1) | ~locked_epoch1(NODE0)
forall NODE0,NODE1. ep_epoch2(NODE0) | ~locked_epoch3(NODE1) | ~locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ~transfer_epoch3(NODE1) | ~locked_epoch2(NODE0)
forall NODE0. ep_epoch3(NODE0) | ep_epoch2(NODE0) | ~locked_epoch2(NODE0)
forall NODE0. held(NODE0) | ep_epoch2(NODE0) | ~locked_epoch2(NODE0)
forall NODE0. ep_epoch2(NODE0) | locked_epoch3(NODE0) | ~locked_epoch2(NODE0)
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch0(NODE1) | ~transfer_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE1) | ~transfer_epoch2(NODE0) | ep_epoch1(NODE1)
forall NODE0,NODE1. locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~transfer_epoch2(NODE0)
forall NODE0,NODE1. ep_epoch1(NODE0) | ~transfer_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~ep_epoch0(NODE0) | ep_epoch3(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~ep_epoch0(NODE0) | held(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch3(NODE1) | ~ep_epoch0(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ~ep_epoch0(NODE0) | ep_epoch3(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ~ep_epoch0(NODE0) | locked_epoch2(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch3(NODE1) | ~ep_epoch0(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch3(NODE1) | ~held(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch3(NODE1) | ~held(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ep_epoch3(NODE1) | ~held(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch3(NODE1) | ~held(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch3(NODE1) | ep_epoch0(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | held(NODE1) | ep_epoch0(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch3(NODE1) | ep_epoch0(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ep_epoch3(NODE1) | ep_epoch0(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ep_epoch0(NODE1) | locked_epoch2(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch3(NODE1) | ep_epoch0(NODE1) | ~ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch1(NODE0) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~held(NODE0) | ~ep_epoch2(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ~held(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE0) | ~held(NODE0) | ~ep_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch1(NODE0) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch1(NODE1) | ~ep_epoch2(NODE0) | ep_epoch3(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ~ep_epoch2(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | ~ep_epoch2(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ep_epoch3(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~ep_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE0) | ~ep_epoch2(NODE0) | ep_epoch3(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | locked_epoch1(NODE0) | ~ep_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | locked_epoch1(NODE0) | ~ep_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ~locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ~locked_epoch2(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~ep_epoch3(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | locked_epoch2(NODE1) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | ~locked_epoch2(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch1(NODE1) | ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch1(NODE1) | ~ep_epoch3(NODE0) | ep_epoch0(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~ep_epoch3(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~ep_epoch3(NODE0) | locked_epoch2(NODE1) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~held(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ep_epoch0(NODE1) | ~held(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ~held(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~held(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ~held(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ~held(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ~held(NODE0) | ~locked_epoch1(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch2(NODE0) | ~held(NODE0) | ~locked_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ~held(NODE0) | locked_epoch3(NODE0) | ~locked_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | locked_epoch2(NODE0) | ~held(NODE0) | ~locked_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE0) | locked_epoch3(NODE0) | ~held(NODE0) | ~locked_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ~held(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~held(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ep_epoch0(NODE1) | ~held(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch2(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | locked_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~held(NODE0) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0. ep_epoch3(NODE0) | ep_epoch1(NODE0) | ep_epoch2(NODE0) | ~held(NODE0)
forall NODE0. ep_epoch1(NODE0) | ep_epoch2(NODE0) | ~held(NODE0) | locked_epoch3(NODE0)
forall NODE0. ep_epoch3(NODE0) | ep_epoch1(NODE0) | ~held(NODE0) | locked_epoch2(NODE0)
forall NODE0. ep_epoch1(NODE0) | locked_epoch3(NODE0) | ~held(NODE0) | locked_epoch2(NODE0)
forall NODE0,NODE1. ep_epoch2(NODE1) | ~held(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ~held(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ~held(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ~held(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0. ep_epoch3(NODE0) | ep_epoch2(NODE0) | ~held(NODE0) | locked_epoch1(NODE0)
forall NODE0. ep_epoch2(NODE0) | ~held(NODE0) | locked_epoch1(NODE0) | locked_epoch3(NODE0)
forall NODE0. ep_epoch3(NODE0) | ~held(NODE0) | locked_epoch1(NODE0) | locked_epoch2(NODE0)
forall NODE0. locked_epoch3(NODE0) | ~held(NODE0) | locked_epoch1(NODE0) | locked_epoch2(NODE0)
forall NODE0,NODE1. ~locked_epoch3(NODE0) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ~locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | ~locked_epoch2(NODE1) | ~locked_epoch1(NODE0) | ~locked_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch1(NODE0) | ~locked_epoch2(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch1(NODE0) | ~locked_epoch2(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | held(NODE0) | ~locked_epoch2(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | ~locked_epoch2(NODE1) | locked_epoch3(NODE0) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ~locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ~locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | ep_epoch2(NODE0) | ~locked_epoch1(NODE0) | ~locked_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | locked_epoch2(NODE0) | ~locked_epoch1(NODE0) | ~locked_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | ep_epoch2(NODE0) | ~locked_epoch1(NODE0) | ~transfer_epoch3(NODE1)
forall NODE0,NODE1. ep_epoch1(NODE0) | locked_epoch2(NODE0) | ~locked_epoch1(NODE0) | ~transfer_epoch3(NODE1)
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch3(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ep_epoch0(NODE1) | locked_epoch2(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch3(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0. ep_epoch3(NODE0) | ep_epoch1(NODE0) | ep_epoch2(NODE0) | ~locked_epoch1(NODE0)
forall NODE0. ep_epoch1(NODE0) | held(NODE0) | ep_epoch2(NODE0) | ~locked_epoch1(NODE0)
forall NODE0. ep_epoch1(NODE0) | ep_epoch2(NODE0) | locked_epoch3(NODE0) | ~locked_epoch1(NODE0)
forall NODE0. ep_epoch3(NODE0) | ep_epoch1(NODE0) | locked_epoch2(NODE0) | ~locked_epoch1(NODE0)
forall NODE0. locked_epoch2(NODE0) | ep_epoch1(NODE0) | held(NODE0) | ~locked_epoch1(NODE0)
forall NODE0. ep_epoch1(NODE0) | locked_epoch2(NODE0) | locked_epoch3(NODE0) | ~locked_epoch1(NODE0)
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch3(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | locked_epoch1(NODE0) | ~locked_epoch3(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch2(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ep_epoch3(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ep_epoch2(NODE0) | ep_epoch0(NODE1) | ~locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | locked_epoch1(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | locked_epoch1(NODE1) | ~locked_epoch2(NODE0) | ep_epoch0(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ~locked_epoch2(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ~locked_epoch2(NODE0) | locked_epoch1(NODE0) | ep_epoch3(NODE1) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. held(NODE1) | ~locked_epoch2(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE1) | ~locked_epoch2(NODE0) | locked_epoch1(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~locked_epoch3(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | ep_epoch0(NODE1) | ~locked_epoch3(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~locked_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~locked_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch1(NODE0) | ~locked_epoch3(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch1(NODE0) | ~locked_epoch3(NODE0) | ep_epoch1(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~transfer_epoch3(NODE0) | ep_epoch1(NODE1)
forall NODE0,NODE1. locked_epoch2(NODE1) | ep_epoch0(NODE1) | ~transfer_epoch3(NODE0) | ep_epoch1(NODE1)
forall NODE0,NODE1. ep_epoch2(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~transfer_epoch3(NODE0)
forall NODE0,NODE1. locked_epoch2(NODE1) | locked_epoch1(NODE1) | ep_epoch0(NODE1) | ~transfer_epoch3(NODE0)
forall NODE0. ep_epoch2(NODE0) | ep_epoch0(NODE0) | ep_epoch3(NODE0) | ep_epoch1(NODE0)
forall NODE0. ep_epoch1(NODE0) | ep_epoch0(NODE0) | held(NODE0) | ep_epoch2(NODE0)
forall NODE0. ep_epoch1(NODE0) | ep_epoch0(NODE0) | ep_epoch2(NODE0) | locked_epoch3(NODE0)
forall NODE0. ep_epoch1(NODE0) | ep_epoch0(NODE0) | ep_epoch3(NODE0) | locked_epoch2(NODE0)
forall NODE0. ep_epoch1(NODE0) | ep_epoch0(NODE0) | held(NODE0) | locked_epoch2(NODE0)
forall NODE0. ep_epoch1(NODE0) | ep_epoch0(NODE0) | locked_epoch3(NODE0) | locked_epoch2(NODE0)
forall NODE0. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch2(NODE0) | locked_epoch1(NODE0)
forall NODE0. ep_epoch0(NODE0) | held(NODE0) | ep_epoch2(NODE0) | locked_epoch1(NODE0)
forall NODE0. ep_epoch0(NODE0) | ep_epoch2(NODE0) | locked_epoch1(NODE0) | locked_epoch3(NODE0)
forall NODE0. ep_epoch3(NODE0) | ep_epoch0(NODE0) | locked_epoch1(NODE0) | locked_epoch2(NODE0)
forall NODE0. ep_epoch0(NODE0) | held(NODE0) | locked_epoch1(NODE0) | locked_epoch2(NODE0)
forall NODE0. ep_epoch0(NODE0) | locked_epoch3(NODE0) | locked_epoch1(NODE0) | locked_epoch2(NODE0)
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch1(NODE0) | locked_epoch1(NODE1) | ep_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE0) | ep_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | locked_epoch1(NODE1) | ep_epoch2(NODE0) | locked_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch1(NODE0) | locked_epoch1(NODE1) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE0) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE0) | locked_epoch1(NODE1) | locked_epoch3(NODE0) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch0(NODE0) | ~ep_epoch2(NODE1) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch0(NODE0) | ~locked_epoch2(NODE1) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch0(NODE0) | ep_epoch1(NODE1) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch2(NODE1) | ~ep_epoch1(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch1(NODE0) | ~locked_epoch2(NODE1) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ep_epoch0(NODE1) | ~ep_epoch1(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch2(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch2(NODE0) | held(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | locked_epoch3(NODE1) | ~ep_epoch2(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ep_epoch1(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ep_epoch1(NODE0) | held(NODE1) | held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | locked_epoch3(NODE1) | ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | held(NODE0) | ~locked_epoch2(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | held(NODE1) | held(NODE0) | ~locked_epoch2(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | locked_epoch3(NODE1) | held(NODE0) | ~locked_epoch2(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | ~transfer_epoch3(NODE0) | ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch0(NODE1) | ~transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch0(NODE1) | ~transfer_epoch3(NODE0) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch1(NODE1) | ~transfer_epoch3(NODE0) | ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch1(NODE1) | ~transfer_epoch3(NODE0) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch1(NODE1) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch1(NODE1) | locked_epoch1(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch1(NODE1) | held(NODE1) | held(NODE0) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch1(NODE1) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | locked_epoch3(NODE0) | ep_epoch1(NODE1) | locked_epoch3(NODE1) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~ep_epoch0(NODE0) | transfer_epoch2(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | transfer_epoch3(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | held(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | locked_epoch3(NODE0) | ep_epoch0(NODE1) | ~locked_epoch1(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~locked_epoch1(NODE0) | ep_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~locked_epoch1(NODE0) | ep_epoch1(NODE0) | held(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ~locked_epoch1(NODE0) | locked_epoch3(NODE1) | ep_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch2(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | locked_epoch3(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | locked_epoch3(NODE0) | ep_epoch0(NODE1) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch0(NODE1) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch0(NODE1) | locked_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch2(NODE0) | ep_epoch2(NODE1) | locked_epoch3(NODE0) | ep_epoch0(NODE1) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch2(NODE0) | ep_epoch0(NODE1) | locked_epoch2(NODE1) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch2(NODE1) | ep_epoch0(NODE1) | locked_epoch2(NODE0) | held(NODE1) | held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | ep_epoch2(NODE0) | locked_epoch3(NODE0) | ep_epoch0(NODE1) | locked_epoch3(NODE1) | locked_epoch2(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch0(NODE1) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch0(NODE0) | ep_epoch0(NODE1) | locked_epoch3(NODE1) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | locked_epoch3(NODE0) | ep_epoch0(NODE1) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | ep_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | ep_epoch1(NODE0) | held(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | locked_epoch3(NODE1) | ep_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | locked_epoch1(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | held(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | locked_epoch3(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch1(NODE1) | locked_epoch3(NODE1) | ep_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch2(NODE1) | ep_epoch1(NODE1) | locked_epoch3(NODE1) | ep_epoch1(NODE0) | held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch2(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | held(NODE1) | held(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch2(NODE0) | locked_epoch3(NODE0) | ep_epoch1(NODE1) | locked_epoch3(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. locked_epoch3(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE1) | locked_epoch2(NODE0) | held(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | locked_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | locked_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | locked_epoch1(NODE1) | locked_epoch3(NODE1) | ep_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | ep_epoch2(NODE1) | ep_epoch0(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | ep_epoch2(NODE1) | ep_epoch0(NODE1) | locked_epoch3(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | ep_epoch0(NODE1) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch3(NODE1) | ep_epoch0(NODE1) | locked_epoch3(NODE1) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | transfer_epoch3(NODE1) | ep_epoch2(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ep_epoch2(NODE0) | locked_epoch3(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | transfer_epoch3(NODE1) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | locked_epoch3(NODE0) | ep_epoch1(NODE1) | ep_epoch1(NODE0) | locked_epoch2(NODE0) | held(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | ep_epoch2(NODE1) | transfer_epoch2(NODE0) | ~ep_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | ep_epoch2(NODE1) | transfer_epoch2(NODE0) | ~ep_epoch1(NODE0) | locked_epoch3(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | transfer_epoch2(NODE0) | ~ep_epoch1(NODE0) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | transfer_epoch2(NODE0) | ~ep_epoch1(NODE0) | locked_epoch3(NODE1) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | ep_epoch2(NODE1) | transfer_epoch2(NODE0) | ~locked_epoch1(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | ep_epoch2(NODE1) | transfer_epoch2(NODE0) | ~locked_epoch1(NODE0) | locked_epoch3(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | transfer_epoch2(NODE0) | ~locked_epoch1(NODE0) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | transfer_epoch2(NODE0) | ~locked_epoch1(NODE0) | locked_epoch3(NODE1) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch2(NODE1) | transfer_epoch3(NODE1) | ep_epoch2(NODE1) | transfer_epoch2(NODE0) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch2(NODE1) | transfer_epoch3(NODE1) | ep_epoch2(NODE1) | transfer_epoch2(NODE0) | locked_epoch3(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch2(NODE1) | transfer_epoch3(NODE1) | transfer_epoch2(NODE0) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | ep_epoch3(NODE1) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch0(NODE0) | transfer_epoch2(NODE1) | transfer_epoch3(NODE1) | transfer_epoch2(NODE0) | locked_epoch3(NODE1) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | transfer_epoch3(NODE1) | ep_epoch2(NODE0) | transfer_epoch2(NODE0) | ep_epoch1(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ep_epoch2(NODE0) | transfer_epoch2(NODE0) | locked_epoch3(NODE0) | ep_epoch1(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | transfer_epoch3(NODE1) | transfer_epoch2(NODE0) | ep_epoch1(NODE0) | locked_epoch2(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | transfer_epoch2(NODE0) | locked_epoch3(NODE0) | ep_epoch1(NODE0) | locked_epoch2(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | transfer_epoch3(NODE1) | ep_epoch2(NODE0) | transfer_epoch2(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. transfer_epoch3(NODE1) | ep_epoch2(NODE0) | transfer_epoch2(NODE0) | locked_epoch3(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE0,NODE1. ep_epoch3(NODE0) | transfer_epoch3(NODE1) | transfer_epoch2(NODE0) | locked_epoch2(NODE0) | held(NODE1) | transfer_epoch2(NODE1) | transfer_epoch3(NODE0) | locked_epoch1(NODE0) | NODE0 = NODE1
forall NODE1,NODE0. locked_epoch1(NODE1) | transfer_epoch2(NODE0) | transfer_epoch3(NODE0) | locked_epoch3(NODE1) | locked_epoch2(NODE1) | held(NODE0) | transfer_epoch3(NODE1) | transfer_epoch2(NODE1) | NODE0 = NODE1

; truth table
ep_epoch0(node0) ep_epoch1(node0) ep_epoch2(node0) ep_epoch3(node0) ep_epoch0(node1) ep_epoch1(node1) ep_epoch2(node1) ep_epoch3(node1) held(node0) held(node1) locked_epoch0(node0) locked_epoch0(node1) locked_epoch1(node0) locked_epoch1(node1) locked_epoch2(node0) locked_epoch2(node1) locked_epoch3(node0) locked_epoch3(node1) transfer_epoch0(node0) transfer_epoch0(node1) transfer_epoch1(node0) transfer_epoch1(node1) transfer_epoch2(node0) transfer_epoch2(node1) transfer_epoch3(node0) transfer_epoch3(node1)
01001000100010000000000000
10000100010001000000000000
01001000000010000000001000
10000100000001000000000100
00101000100010100000000000
10000010010001010000000000
00101000000010100000000010
10000010000001010000000001
00011000100010101000000000
10000001010001010100000000
00101000000010100000000001
10000010000001010000000010
00100001010010100100000000
00010010100001011000000000
01001000000010000000000010
10000100000001000000000001
00011000100010001000000000
10000001010001000100000000
01001000000010000000000100
10000100000001000000001000
01000010010010010000000000
00100100100001100000000000
01000010000010010000000010
00100100000001100000000001
00010010100010011000000000
00100001010001100100000000
01000010000010010000000001
00100100000001100000000010
01000001010010010100000000
00010100100001101000000000
01001000000010000000000001
10000100000001000000000010
01000001010010000100000000
00010100100001001000000000

; Check equivalence
(assert (not (= R S)))
(check-sat)