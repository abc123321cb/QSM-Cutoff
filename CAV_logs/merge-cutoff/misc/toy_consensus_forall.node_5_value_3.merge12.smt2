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
 (let (($x107 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x54 (not $x107)))
 (let (($x105 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x149 (not $x105)))
 (let (($x163 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x164 (not $x163)))
 (let (($x135 (= |NODE1:node| |NODE2:node|)))
 (let (($x161 (not $x135)))
 (let (($x106 (= |NODE0:node| |NODE1:node|)))
 (let (($x109 (not $x106)))
 (let (($x143 (= |NODE0:node| |NODE2:node|)))
 (let (($x156 (not $x143)))
 (let (($x162 (and $x156 $x109 $x161 $x105 $x54)))
 (and (member node0 quorum__node0_node1_node2) (member node1 quorum__node0_node1_node2) (member node2 quorum__node0_node1_node2) (not (member node3 quorum__node0_node1_node2)) (not (member node4 quorum__node0_node1_node2)) (member node0 quorum__node0_node1_node3) (member node1 quorum__node0_node1_node3) (not (member node2 quorum__node0_node1_node3)) (member node3 quorum__node0_node1_node3) (not (member node4 quorum__node0_node1_node3)) (member node0 quorum__node0_node1_node4) (member node1 quorum__node0_node1_node4) (not (member node2 quorum__node0_node1_node4)) (not (member node3 quorum__node0_node1_node4)) (member node4 quorum__node0_node1_node4) (member node0 quorum__node0_node2_node3) (not (member node1 quorum__node0_node2_node3)) (member node2 quorum__node0_node2_node3) (member node3 quorum__node0_node2_node3) (not (member node4 quorum__node0_node2_node3)) (member node0 quorum__node0_node2_node4) (not (member node1 quorum__node0_node2_node4)) (member node2 quorum__node0_node2_node4) (not (member node3 quorum__node0_node2_node4)) (member node4 quorum__node0_node2_node4) (member node0 quorum__node0_node3_node4) (not (member node1 quorum__node0_node3_node4)) (not (member node2 quorum__node0_node3_node4)) (member node3 quorum__node0_node3_node4) (member node4 quorum__node0_node3_node4) (not (member node0 quorum__node1_node2_node3)) (member node1 quorum__node1_node2_node3) (member node2 quorum__node1_node2_node3) (member node3 quorum__node1_node2_node3) (not (member node4 quorum__node1_node2_node3)) (not (member node0 quorum__node1_node2_node4)) (member node1 quorum__node1_node2_node4) (member node2 quorum__node1_node2_node4) (not (member node3 quorum__node1_node2_node4)) (member node4 quorum__node1_node2_node4) (not (member node0 quorum__node1_node3_node4)) (member node1 quorum__node1_node3_node4) (not (member node2 quorum__node1_node3_node4)) (member node3 quorum__node1_node3_node4) (member node4 quorum__node1_node3_node4) (not (member node0 quorum__node2_node3_node4)) (not (member node1 quorum__node2_node3_node4)) (member node2 quorum__node2_node3_node4) (member node3 quorum__node2_node3_node4) (member node4 quorum__node2_node3_node4) (not (or $x162 $x162 $x162 (and $x156 $x109 $x161 $x164 $x149 $x54))))))))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x107 (= |VALUE0:value| |VALUE1:value|)))
 (not $x107)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x163 (= |VALUE0:value| |VALUE2:value|)))
 (not $x163)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x105 (= |VALUE1:value| |VALUE2:value|)))
 (not $x105)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x106 (= |NODE0:node| |NODE1:node|)))
 (not $x106)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x143 (= |NODE0:node| |NODE2:node|)))
 (not $x143)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x135 (= |NODE1:node| |NODE2:node|)))
 (not $x135)))
(check-sat)
