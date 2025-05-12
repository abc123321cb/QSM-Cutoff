; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((node (node0) (node1) (node2) (node3) (node4))))
 (declare-datatypes ((value 0)) ((value (value0) (value1) (value2))))
 (declare-datatypes ((quorum 0)) ((quorum (quorum__node0_node1_node2) (quorum__node0_node1_node3) (quorum__node0_node1_node4) (quorum__node0_node2_node3) (quorum__node0_node2_node4) (quorum__node0_node3_node4) (quorum__node1_node2_node3) (quorum__node1_node2_node4) (quorum__node1_node3_node4) (quorum__node2_node3_node4))))
 (declare-fun |QUORUM0:quorum| () quorum)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |VALUE2:value| () value)
(declare-fun member (node quorum) Bool)
(assert
 (let (($x106 (member |NODE1:node| |QUORUM0:quorum|)))
 (let (($x107 (not $x106)))
 (let (($x104 (member |NODE0:node| |QUORUM0:quorum|)))
 (let (($x105 (not $x104)))
 (let (($x101 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x102 (not $x101)))
 (let (($x99 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x111 (not $x99)))
 (let (($x109 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x110 (not $x109)))
 (let (($x92 (= |NODE0:node| |NODE1:node|)))
 (let (($x93 (not $x92)))
 (let (($x113 (or (and $x93 $x99 $x102 $x105 $x107) (and $x93 $x110 $x111 $x102 $x105 $x107))))
 (and (member node0 quorum__node0_node1_node2) (member node1 quorum__node0_node1_node2) (member node2 quorum__node0_node1_node2) (not (member node3 quorum__node0_node1_node2)) (not (member node4 quorum__node0_node1_node2)) (member node0 quorum__node0_node1_node3) (member node1 quorum__node0_node1_node3) (not (member node2 quorum__node0_node1_node3)) (member node3 quorum__node0_node1_node3) (not (member node4 quorum__node0_node1_node3)) (member node0 quorum__node0_node1_node4) (member node1 quorum__node0_node1_node4) (not (member node2 quorum__node0_node1_node4)) (not (member node3 quorum__node0_node1_node4)) (member node4 quorum__node0_node1_node4) (member node0 quorum__node0_node2_node3) (not (member node1 quorum__node0_node2_node3)) (member node2 quorum__node0_node2_node3) (member node3 quorum__node0_node2_node3) (not (member node4 quorum__node0_node2_node3)) (member node0 quorum__node0_node2_node4) (not (member node1 quorum__node0_node2_node4)) (member node2 quorum__node0_node2_node4) (not (member node3 quorum__node0_node2_node4)) (member node4 quorum__node0_node2_node4) (member node0 quorum__node0_node3_node4) (not (member node1 quorum__node0_node3_node4)) (not (member node2 quorum__node0_node3_node4)) (member node3 quorum__node0_node3_node4) (member node4 quorum__node0_node3_node4) (not (member node0 quorum__node1_node2_node3)) (member node1 quorum__node1_node2_node3) (member node2 quorum__node1_node2_node3) (member node3 quorum__node1_node2_node3) (not (member node4 quorum__node1_node2_node3)) (not (member node0 quorum__node1_node2_node4)) (member node1 quorum__node1_node2_node4) (member node2 quorum__node1_node2_node4) (not (member node3 quorum__node1_node2_node4)) (member node4 quorum__node1_node2_node4) (not (member node0 quorum__node1_node3_node4)) (member node1 quorum__node1_node3_node4) (not (member node2 quorum__node1_node3_node4)) (member node3 quorum__node1_node3_node4) (member node4 quorum__node1_node3_node4) (not (member node0 quorum__node2_node3_node4)) (not (member node1 quorum__node2_node3_node4)) (member node2 quorum__node2_node3_node4) (member node3 quorum__node2_node3_node4) (member node4 quorum__node2_node3_node4) (not $x113))))))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x101 (= |VALUE0:value| |VALUE1:value|)))
 (not $x101)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x109 (= |VALUE0:value| |VALUE2:value|)))
 (not $x109)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x99 (= |VALUE1:value| |VALUE2:value|)))
 (not $x99)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x92 (= |NODE0:node| |NODE1:node|)))
 (not $x92)))
(assert
 (member |NODE0:node| |QUORUM0:quorum|))
(assert
 (let (($x104 (member |NODE0:node| |QUORUM0:quorum|)))
 (not $x104)))
(assert
 (member |NODE1:node| |QUORUM0:quorum|))
(assert
 (let (($x106 (member |NODE1:node| |QUORUM0:quorum|)))
 (not $x106)))
(check-sat)
