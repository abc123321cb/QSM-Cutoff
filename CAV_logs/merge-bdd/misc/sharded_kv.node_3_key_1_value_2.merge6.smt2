; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1))))
 (declare-datatypes ((node 0)) ((node (node0) (node1) (node2))))
 (declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(assert
 (let (($x5 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x58 (not $x5)))
 (let (($x16 (= |NODE0:node| |NODE1:node|)))
 (let (($x60 (not (or (and (not $x16) $x5) (and (not $x16) $x58) (and $x16 $x58)))))
 (and $x60))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x16 (= |NODE0:node| |NODE1:node|)))
 (not $x16)))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x5 (= |VALUE0:value| |VALUE1:value|)))
 (not $x5)))
(check-sat)
