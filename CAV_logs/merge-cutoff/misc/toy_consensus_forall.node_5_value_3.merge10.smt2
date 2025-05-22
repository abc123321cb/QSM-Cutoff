; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1) (value2))))
 (declare-datatypes ((node 0)) ((node (node0) (node1) (node2) (node3) (node4))))
 (declare-datatypes ((quorum 0)) ((quorum (quorum__node0_node1_node2) (quorum__node0_node1_node3) (quorum__node0_node1_node4) (quorum__node0_node2_node3) (quorum__node0_node2_node4) (quorum__node0_node3_node4) (quorum__node1_node2_node3) (quorum__node1_node2_node4) (quorum__node1_node3_node4) (quorum__node2_node3_node4))))
 (declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |VALUE2:value| () value)
(declare-fun |NODE2:node| () node)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun member (node quorum) Bool)
(assert
 (let (($x68 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x17 (not $x68)))
 (let (($x66 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x72 (not $x66)))
 (let (($x70 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x71 (not $x70)))
 (let (($x60 (= |NODE1:node| |NODE2:node|)))
 (let (($x61 (not $x60)))
 (let (($x58 (= |NODE0:node| |NODE1:node|)))
 (let (($x59 (not $x58)))
 (let (($x55 (= |NODE0:node| |NODE2:node|)))
 (let (($x56 (not $x55)))
 (let (($x74 (or (and $x56 $x59 $x61 $x66 $x17) (and $x56 $x59 $x61 $x71 $x72 $x17))))
 (and (member node0 quorum__node0_node1_node2) (member node1 quorum__node0_node1_node2) (member node2 quorum__node0_node1_node2) (not (member node3 quorum__node0_node1_node2)) (not (member node4 quorum__node0_node1_node2)) (member node0 quorum__node0_node1_node3) (member node1 quorum__node0_node1_node3) (not (member node2 quorum__node0_node1_node3)) (member node3 quorum__node0_node1_node3) (not (member node4 quorum__node0_node1_node3)) (member node0 quorum__node0_node1_node4) (member node1 quorum__node0_node1_node4) (not (member node2 quorum__node0_node1_node4)) (not (member node3 quorum__node0_node1_node4)) (member node4 quorum__node0_node1_node4) (member node0 quorum__node0_node2_node3) (not (member node1 quorum__node0_node2_node3)) (member node2 quorum__node0_node2_node3) (member node3 quorum__node0_node2_node3) (not (member node4 quorum__node0_node2_node3)) (member node0 quorum__node0_node2_node4) (not (member node1 quorum__node0_node2_node4)) (member node2 quorum__node0_node2_node4) (not (member node3 quorum__node0_node2_node4)) (member node4 quorum__node0_node2_node4) (member node0 quorum__node0_node3_node4) (not (member node1 quorum__node0_node3_node4)) (not (member node2 quorum__node0_node3_node4)) (member node3 quorum__node0_node3_node4) (member node4 quorum__node0_node3_node4) (not (member node0 quorum__node1_node2_node3)) (member node1 quorum__node1_node2_node3) (member node2 quorum__node1_node2_node3) (member node3 quorum__node1_node2_node3) (not (member node4 quorum__node1_node2_node3)) (not (member node0 quorum__node1_node2_node4)) (member node1 quorum__node1_node2_node4) (member node2 quorum__node1_node2_node4) (not (member node3 quorum__node1_node2_node4)) (member node4 quorum__node1_node2_node4) (not (member node0 quorum__node1_node3_node4)) (member node1 quorum__node1_node3_node4) (not (member node2 quorum__node1_node3_node4)) (member node3 quorum__node1_node3_node4) (member node4 quorum__node1_node3_node4) (not (member node0 quorum__node2_node3_node4)) (not (member node1 quorum__node2_node3_node4)) (member node2 quorum__node2_node3_node4) (member node3 quorum__node2_node3_node4) (member node4 quorum__node2_node3_node4) (not $x74))))))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x68 (= |VALUE0:value| |VALUE1:value|)))
 (not $x68)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x70 (= |VALUE0:value| |VALUE2:value|)))
 (not $x70)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x66 (= |VALUE1:value| |VALUE2:value|)))
 (not $x66)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x58 (= |NODE0:node| |NODE1:node|)))
 (not $x58)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x55 (= |NODE0:node| |NODE2:node|)))
 (not $x55)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x60 (= |NODE1:node| |NODE2:node|)))
 (not $x60)))
(check-sat)
