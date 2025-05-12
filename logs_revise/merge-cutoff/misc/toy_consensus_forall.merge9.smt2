; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((node (node0) (node1) (node2) (node3) (node4))))
 (declare-datatypes ((value 0)) ((value (value0) (value1) (value2))))
 (declare-datatypes ((quorum 0)) ((quorum (quorum__node0_node1_node2) (quorum__node0_node1_node3) (quorum__node0_node1_node4) (quorum__node0_node2_node3) (quorum__node0_node2_node4) (quorum__node0_node3_node4) (quorum__node1_node2_node3) (quorum__node1_node2_node4) (quorum__node1_node3_node4) (quorum__node2_node3_node4))))
 (declare-fun |QUORUM0:quorum| () quorum)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun |VALUE2:value| () value)
(declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun member (node quorum) Bool)
(assert
 (let (($x68 (member |NODE1:node| |QUORUM0:quorum|)))
 (let (($x17 (not $x68)))
 (let (($x66 (member |NODE0:node| |QUORUM0:quorum|)))
 (let (($x67 (not $x66)))
 (let (($x16 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x72 (not $x16)))
 (let (($x63 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x64 (not $x63)))
 (let (($x70 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x71 (not $x70)))
 (let (($x55 (= |NODE0:node| |NODE1:node|)))
 (let (($x56 (not $x55)))
 (let (($x74 (or (and $x56 $x16 $x64 $x67 $x17) (and $x56 $x71 $x64 $x72 $x67 $x17))))
 (and (member node0 quorum__node0_node1_node2) (member node1 quorum__node0_node1_node2) (member node2 quorum__node0_node1_node2) (not (member node3 quorum__node0_node1_node2)) (not (member node4 quorum__node0_node1_node2)) (member node0 quorum__node0_node1_node3) (member node1 quorum__node0_node1_node3) (not (member node2 quorum__node0_node1_node3)) (member node3 quorum__node0_node1_node3) (not (member node4 quorum__node0_node1_node3)) (member node0 quorum__node0_node1_node4) (member node1 quorum__node0_node1_node4) (not (member node2 quorum__node0_node1_node4)) (not (member node3 quorum__node0_node1_node4)) (member node4 quorum__node0_node1_node4) (member node0 quorum__node0_node2_node3) (not (member node1 quorum__node0_node2_node3)) (member node2 quorum__node0_node2_node3) (member node3 quorum__node0_node2_node3) (not (member node4 quorum__node0_node2_node3)) (member node0 quorum__node0_node2_node4) (not (member node1 quorum__node0_node2_node4)) (member node2 quorum__node0_node2_node4) (not (member node3 quorum__node0_node2_node4)) (member node4 quorum__node0_node2_node4) (member node0 quorum__node0_node3_node4) (not (member node1 quorum__node0_node3_node4)) (not (member node2 quorum__node0_node3_node4)) (member node3 quorum__node0_node3_node4) (member node4 quorum__node0_node3_node4) (not (member node0 quorum__node1_node2_node3)) (member node1 quorum__node1_node2_node3) (member node2 quorum__node1_node2_node3) (member node3 quorum__node1_node2_node3) (not (member node4 quorum__node1_node2_node3)) (not (member node0 quorum__node1_node2_node4)) (member node1 quorum__node1_node2_node4) (member node2 quorum__node1_node2_node4) (not (member node3 quorum__node1_node2_node4)) (member node4 quorum__node1_node2_node4) (not (member node0 quorum__node1_node3_node4)) (member node1 quorum__node1_node3_node4) (not (member node2 quorum__node1_node3_node4)) (member node3 quorum__node1_node3_node4) (member node4 quorum__node1_node3_node4) (not (member node0 quorum__node2_node3_node4)) (not (member node1 quorum__node2_node3_node4)) (member node2 quorum__node2_node3_node4) (member node3 quorum__node2_node3_node4) (member node4 quorum__node2_node3_node4) (not $x74))))))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x63 (= |VALUE0:value| |VALUE1:value|)))
 (not $x63)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x70 (= |VALUE0:value| |VALUE2:value|)))
 (not $x70)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x16 (= |VALUE1:value| |VALUE2:value|)))
 (not $x16)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x55 (= |NODE0:node| |NODE1:node|)))
 (not $x55)))
(assert
 (member |NODE1:node| |QUORUM0:quorum|))
(assert
 (let (($x68 (member |NODE1:node| |QUORUM0:quorum|)))
 (not $x68)))
(assert
 (member |NODE0:node| |QUORUM0:quorum|))
(assert
 (let (($x66 (member |NODE0:node| |QUORUM0:quorum|)))
 (not $x66)))
(check-sat)
