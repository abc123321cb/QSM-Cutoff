; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1))))
 (declare-datatypes ((node 0)) ((node (node0) (node1))))
 (declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(assert
 (let (($x5 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x16 (not $x5)))
 (let (($x11 (= |NODE0:node| |NODE1:node|)))
 (let (($x31 (not (or (and (not $x11) $x16) (and (not $x11) $x5) (and $x11 $x16)))))
 (and $x31))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x11 (= |NODE0:node| |NODE1:node|)))
 (not $x11)))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x5 (= |VALUE0:value| |VALUE1:value|)))
 (not $x5)))
(check-sat)
