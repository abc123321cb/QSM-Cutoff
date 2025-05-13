; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((value (value0) (value1))))
 (declare-datatypes ((node 0)) ((node (node0) (node1))))
 (declare-fun |VALUE1:value| () value)
(declare-fun |VALUE0:value| () value)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(assert
 (let (($x49 (= |VALUE0:value| |VALUE1:value|)))
 (let (($x52 (= |NODE0:node| |NODE1:node|)))
 (let (($x15 (not $x52)))
 (let (($x12 (not (or (and $x15 (not $x49)) (and $x52 (not $x49)) (and $x15 $x49)))))
 (and $x12))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x52 (= |NODE0:node| |NODE1:node|)))
 (not $x52)))
(assert
 (= |VALUE0:value| |VALUE1:value|))
(assert
 (let (($x49 (= |VALUE0:value| |VALUE1:value|)))
 (not $x49)))
(check-sat)
