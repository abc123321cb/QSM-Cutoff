; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1))))
 (declare-datatypes ((node 0)) ((node (node0) (node1) (node2))))
 (declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(assert
 (let (($x6 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x5 (not $x6)))
 (let (($x13 (= |NODE0:node| |NODE1:node|)))
 (let (($x26 (not $x13)))
 (and (not (or (and $x13 $x5) (and $x26 $x6) (and $x26 $x5)))))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x13 (= |NODE0:node| |NODE1:node|)))
 (not $x13)))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x6 (= |VALUE0:value| |VALUE1:value|)))
 (not $x6)))
(check-sat)
