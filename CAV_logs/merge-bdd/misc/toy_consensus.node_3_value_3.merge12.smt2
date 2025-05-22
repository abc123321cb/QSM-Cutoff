; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1) (value2))))
 (declare-datatypes ((node 0)) ((node (node0) (node1) (node2))))
 (declare-datatypes ((quorum 0)) ((quorum (quorum__node0_node1) (quorum__node0_node2) (quorum__node1_node2))))
 (declare-fun |VALUE2:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |VALUE1:value| () value)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun member (node quorum) Bool)
(assert
 (let (($x38 (= |VALUE0:value| |VALUE2:value|)))
 (let (($x39 (not $x38)))
 (let (($x34 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x35 (not $x34)))
 (let (($x32 (= |VALUE1:value| |VALUE2:value|)))
 (let (($x37 (not $x32)))
 (let (($x25 (= |NODE0:node| |NODE1:node|)))
 (let (($x26 (not $x25)))
 (and (member node0 quorum__node0_node1) (member node1 quorum__node0_node1) (not (member node2 quorum__node0_node1)) (member node0 quorum__node0_node2) (not (member node1 quorum__node0_node2)) (member node2 quorum__node0_node2) (not (member node0 quorum__node1_node2)) (member node1 quorum__node1_node2) (member node2 quorum__node1_node2) (not (or (and $x26 $x32 $x35) (and $x26 $x37 $x35 $x39)))))))))))))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x34 (= |VALUE0:value| |VALUE1:value|)))
 (not $x34)))
(assert
 (= |VALUE0:value| |VALUE2:value|))
(assert
 (let (($x38 (= |VALUE0:value| |VALUE2:value|)))
 (not $x38)))
(assert
 (= |VALUE1:value| |VALUE2:value|))
(assert
 (let (($x32 (= |VALUE1:value| |VALUE2:value|)))
 (not $x32)))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x25 (= |NODE0:node| |NODE1:node|)))
 (not $x25)))
(check-sat)
