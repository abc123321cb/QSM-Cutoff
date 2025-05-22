; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1))))
 (declare-datatypes ((node 0)) ((node (node0) (node1) (node2))))
 (declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(assert
 (let (($x26 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x58 (not $x26)))
 (let (($x7 (= |NODE0:node| |NODE1:node|)))
 (let (($x6 (not $x7)))
 (and (not (or (and $x6 $x26) (and $x7 $x58) (and $x6 $x58)))))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x7 (= |NODE0:node| |NODE1:node|)))
 (not $x7)))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x26 (= |VALUE0:value| |VALUE1:value|)))
 (not $x26)))
(check-sat)
