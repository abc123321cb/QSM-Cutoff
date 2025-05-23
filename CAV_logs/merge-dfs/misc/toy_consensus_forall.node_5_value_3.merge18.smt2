; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((node (node0) (node1) (node2) (node3) (node4))))
 (declare-datatypes ((value 0)) ((value (value0) (value1) (value2))))
 (declare-datatypes ((quorum 0)) ((quorum (quorum__node0_node1_node2) (quorum__node0_node1_node3) (quorum__node0_node1_node4) (quorum__node0_node2_node3) (quorum__node0_node2_node4) (quorum__node0_node3_node4) (quorum__node1_node2_node3) (quorum__node1_node2_node4) (quorum__node1_node3_node4) (quorum__node2_node3_node4))))
 (declare-fun |QUORUM0:quorum| () quorum)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun |VALUE2:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |VALUE1:value| () value)
(declare-fun member (node quorum) Bool)
(assert
 (let (($x162 (member |NODE1:node| |QUORUM0:quorum|)))
 (let (($x54 (not $x162)))
 (let (($x98 (member |NODE0:node| |QUORUM0:quorum|)))
 (let (($x145 (not $x98)))
 (let (($x149 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x111 (not $x149)))
 (let (($x133 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x164 (not $x133)))
 (let (($x107 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x93 (not $x107)))
 (let (($x143 (= |NODE0:node| |NODE1:node|)))
 (let (($x156 (not $x143)))
 (let (($x166 (or (and $x156 $x133 $x93 $x145 $x54) (and $x156 $x93 $x164 $x111 $x145 $x54))))
 (and (member node0 quorum__node0_node1_node2) (member node1 quorum__node0_node1_node2) (member node2 quorum__node0_node1_node2) (not (member node3 quorum__node0_node1_node2)) (not (member node4 quorum__node0_node1_node2)) (member node0 quorum__node0_node1_node3) (member node1 quorum__node0_node1_node3) (not (member node2 quorum__node0_node1_node3)) (member node3 quorum__node0_node1_node3) (not (member node4 quorum__node0_node1_node3)) (member node0 quorum__node0_node1_node4) (member node1 quorum__node0_node1_node4) (not (member node2 quorum__node0_node1_node4)) (not (member node3 quorum__node0_node1_node4)) (member node4 quorum__node0_node1_node4) (member node0 quorum__node0_node2_node3) (not (member node1 quorum__node0_node2_node3)) (member node2 quorum__node0_node2_node3) (member node3 quorum__node0_node2_node3) (not (member node4 quorum__node0_node2_node3)) (member node0 quorum__node0_node2_node4) (not (member node1 quorum__node0_node2_node4)) (member node2 quorum__node0_node2_node4) (not (member node3 quorum__node0_node2_node4)) (member node4 quorum__node0_node2_node4) (member node0 quorum__node0_node3_node4) (not (member node1 quorum__node0_node3_node4)) (not (member node2 quorum__node0_node3_node4)) (member node3 quorum__node0_node3_node4) (member node4 quorum__node0_node3_node4) (not (member node0 quorum__node1_node2_node3)) (member node1 quorum__node1_node2_node3) (member node2 quorum__node1_node2_node3) (member node3 quorum__node1_node2_node3) (not (member node4 quorum__node1_node2_node3)) (not (member node0 quorum__node1_node2_node4)) (member node1 quorum__node1_node2_node4) (member node2 quorum__node1_node2_node4) (not (member node3 quorum__node1_node2_node4)) (member node4 quorum__node1_node2_node4) (not (member node0 quorum__node1_node3_node4)) (member node1 quorum__node1_node3_node4) (not (member node2 quorum__node1_node3_node4)) (member node3 quorum__node1_node3_node4) (member node4 quorum__node1_node3_node4) (not (member node0 quorum__node2_node3_node4)) (not (member node1 quorum__node2_node3_node4)) (member node2 quorum__node2_node3_node4) (member node3 quorum__node2_node3_node4) (member node4 quorum__node2_node3_node4) (not $x166))))))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x107 (= |VALUE0:value| |VALUE1:value|)))
 (not $x107)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x149 (= |VALUE0:value| |VALUE2:value|)))
 (not $x149)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x133 (= |VALUE1:value| |VALUE2:value|)))
 (not $x133)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x143 (= |NODE0:node| |NODE1:node|)))
 (not $x143)))
(assert
 (member |NODE1:node| |QUORUM0:quorum|))
(assert
 (let (($x162 (member |NODE1:node| |QUORUM0:quorum|)))
 (not $x162)))
(assert
 (member |NODE0:node| |QUORUM0:quorum|))
(assert
 (let (($x98 (member |NODE0:node| |QUORUM0:quorum|)))
 (not $x98)))
(check-sat)
