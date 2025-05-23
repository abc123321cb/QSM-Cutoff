; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1) (value2))))
 (declare-datatypes ((node 0)) ((node (node0) (node1) (node2) (node3) (node4))))
 (declare-datatypes ((quorum 0)) ((quorum (quorum__node0_node1_node2) (quorum__node0_node1_node3) (quorum__node0_node1_node4) (quorum__node0_node2_node3) (quorum__node0_node2_node4) (quorum__node0_node3_node4) (quorum__node1_node2_node3) (quorum__node1_node2_node4) (quorum__node1_node3_node4) (quorum__node2_node3_node4))))
 (declare-fun |VALUE2:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |VALUE1:value| () value)
(declare-fun |NODE2:node| () node)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun member (node quorum) Bool)
(assert
 (let (($x110 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x111 (not $x110)))
 (let (($x104 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x109 (not $x104)))
 (let (($x106 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x107 (not $x106)))
 (let (($x97 (= |NODE1:node| |NODE2:node|)))
 (let (($x98 (not $x97)))
 (let (($x95 (= |NODE0:node| |NODE2:node|)))
 (let (($x96 (not $x95)))
 (let (($x92 (= |NODE0:node| |NODE1:node|)))
 (let (($x93 (not $x92)))
 (let (($x113 (or (and $x93 $x96 $x98 $x104 $x107) (and $x93 $x96 $x98 $x107 $x109 $x111))))
 (and (member node0 quorum__node0_node1_node2) (member node1 quorum__node0_node1_node2) (member node2 quorum__node0_node1_node2) (not (member node3 quorum__node0_node1_node2)) (not (member node4 quorum__node0_node1_node2)) (member node0 quorum__node0_node1_node3) (member node1 quorum__node0_node1_node3) (not (member node2 quorum__node0_node1_node3)) (member node3 quorum__node0_node1_node3) (not (member node4 quorum__node0_node1_node3)) (member node0 quorum__node0_node1_node4) (member node1 quorum__node0_node1_node4) (not (member node2 quorum__node0_node1_node4)) (not (member node3 quorum__node0_node1_node4)) (member node4 quorum__node0_node1_node4) (member node0 quorum__node0_node2_node3) (not (member node1 quorum__node0_node2_node3)) (member node2 quorum__node0_node2_node3) (member node3 quorum__node0_node2_node3) (not (member node4 quorum__node0_node2_node3)) (member node0 quorum__node0_node2_node4) (not (member node1 quorum__node0_node2_node4)) (member node2 quorum__node0_node2_node4) (not (member node3 quorum__node0_node2_node4)) (member node4 quorum__node0_node2_node4) (member node0 quorum__node0_node3_node4) (not (member node1 quorum__node0_node3_node4)) (not (member node2 quorum__node0_node3_node4)) (member node3 quorum__node0_node3_node4) (member node4 quorum__node0_node3_node4) (not (member node0 quorum__node1_node2_node3)) (member node1 quorum__node1_node2_node3) (member node2 quorum__node1_node2_node3) (member node3 quorum__node1_node2_node3) (not (member node4 quorum__node1_node2_node3)) (not (member node0 quorum__node1_node2_node4)) (member node1 quorum__node1_node2_node4) (member node2 quorum__node1_node2_node4) (not (member node3 quorum__node1_node2_node4)) (member node4 quorum__node1_node2_node4) (not (member node0 quorum__node1_node3_node4)) (member node1 quorum__node1_node3_node4) (not (member node2 quorum__node1_node3_node4)) (member node3 quorum__node1_node3_node4) (member node4 quorum__node1_node3_node4) (not (member node0 quorum__node2_node3_node4)) (not (member node1 quorum__node2_node3_node4)) (member node2 quorum__node2_node3_node4) (member node3 quorum__node2_node3_node4) (member node4 quorum__node2_node3_node4) (not $x113))))))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x106 (= |VALUE0:value| |VALUE1:value|)))
 (not $x106)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x110 (= |VALUE0:value| |VALUE2:value|)))
 (not $x110)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x104 (= |VALUE1:value| |VALUE2:value|)))
 (not $x104)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x92 (= |NODE0:node| |NODE1:node|)))
 (not $x92)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x95 (= |NODE0:node| |NODE2:node|)))
 (not $x95)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x97 (= |NODE1:node| |NODE2:node|)))
 (not $x97)))
(check-sat)
