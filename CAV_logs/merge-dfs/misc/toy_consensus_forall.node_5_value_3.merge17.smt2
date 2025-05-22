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
 (let (($x37 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x38 (not $x37)))
 (let (($x33 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x36 (not $x33)))
 (let (($x34 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x90 (not $x34)))
 (let (($x27 (= |NODE1:node| |NODE2:node|)))
 (let (($x28 (not $x27)))
 (let (($x26 (= |NODE0:node| |NODE2:node|)))
 (let (($x11 (not $x26)))
 (let (($x24 (= |NODE0:node| |NODE1:node|)))
 (let (($x9 (not $x24)))
 (let (($x40 (or (and $x9 $x11 $x28 $x33 $x90) (and $x9 $x11 $x28 $x90 $x36 $x38))))
 (and (member node0 quorum__node0_node1_node2) (member node1 quorum__node0_node1_node2) (member node2 quorum__node0_node1_node2) (not (member node3 quorum__node0_node1_node2)) (not (member node4 quorum__node0_node1_node2)) (member node0 quorum__node0_node1_node3) (member node1 quorum__node0_node1_node3) (not (member node2 quorum__node0_node1_node3)) (member node3 quorum__node0_node1_node3) (not (member node4 quorum__node0_node1_node3)) (member node0 quorum__node0_node1_node4) (member node1 quorum__node0_node1_node4) (not (member node2 quorum__node0_node1_node4)) (not (member node3 quorum__node0_node1_node4)) (member node4 quorum__node0_node1_node4) (member node0 quorum__node0_node2_node3) (not (member node1 quorum__node0_node2_node3)) (member node2 quorum__node0_node2_node3) (member node3 quorum__node0_node2_node3) (not (member node4 quorum__node0_node2_node3)) (member node0 quorum__node0_node2_node4) (not (member node1 quorum__node0_node2_node4)) (member node2 quorum__node0_node2_node4) (not (member node3 quorum__node0_node2_node4)) (member node4 quorum__node0_node2_node4) (member node0 quorum__node0_node3_node4) (not (member node1 quorum__node0_node3_node4)) (not (member node2 quorum__node0_node3_node4)) (member node3 quorum__node0_node3_node4) (member node4 quorum__node0_node3_node4) (not (member node0 quorum__node1_node2_node3)) (member node1 quorum__node1_node2_node3) (member node2 quorum__node1_node2_node3) (member node3 quorum__node1_node2_node3) (not (member node4 quorum__node1_node2_node3)) (not (member node0 quorum__node1_node2_node4)) (member node1 quorum__node1_node2_node4) (member node2 quorum__node1_node2_node4) (not (member node3 quorum__node1_node2_node4)) (member node4 quorum__node1_node2_node4) (not (member node0 quorum__node1_node3_node4)) (member node1 quorum__node1_node3_node4) (not (member node2 quorum__node1_node3_node4)) (member node3 quorum__node1_node3_node4) (member node4 quorum__node1_node3_node4) (not (member node0 quorum__node2_node3_node4)) (not (member node1 quorum__node2_node3_node4)) (member node2 quorum__node2_node3_node4) (member node3 quorum__node2_node3_node4) (member node4 quorum__node2_node3_node4) (not $x40))))))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x34 (= |VALUE0:value| |VALUE1:value|)))
 (not $x34)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x37 (= |VALUE0:value| |VALUE2:value|)))
 (not $x37)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x33 (= |VALUE1:value| |VALUE2:value|)))
 (not $x33)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x24 (= |NODE0:node| |NODE1:node|)))
 (not $x24)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x26 (= |NODE0:node| |NODE2:node|)))
 (not $x26)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x27 (= |NODE1:node| |NODE2:node|)))
 (not $x27)))
(check-sat)
