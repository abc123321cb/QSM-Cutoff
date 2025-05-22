; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((node (node0) (node1))))
 (declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun |NODE2:node| () node)
(declare-fun |NODE3:node| () node)
(assert
 (let (($x15 (= |NODE0:node| |NODE1:node|)))
 (let (($x16 (not $x15)))
 (let (($x18 (= |NODE1:node| |NODE2:node|)))
 (let (($x20 (= |NODE0:node| |NODE3:node|)))
 (let (($x38 (or (and (= |NODE0:node| |NODE2:node|) (= |NODE1:node| |NODE3:node|) $x16) (and (= |NODE1:node| |NODE3:node|) $x18 $x16) (and $x20 (= |NODE0:node| |NODE2:node|) $x16) (and $x20 $x15 (not (= |NODE0:node| |NODE2:node|))) (and $x15 (= |NODE0:node| |NODE2:node|) (not $x20)) (and $x20 $x18 $x16))))
 (and (not $x38))))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x15 (= |NODE0:node| |NODE1:node|)))
 (not $x15)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x11 (= |NODE0:node| |NODE2:node|)))
 (not $x11)))
(assert
 (= |NODE0:node| |NODE3:node|))
(assert
 (let (($x20 (= |NODE0:node| |NODE3:node|)))
 (not $x20)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x18 (= |NODE1:node| |NODE2:node|)))
 (not $x18)))
(assert
 (= |NODE1:node| |NODE3:node|))
(assert
 (let (($x14 (= |NODE1:node| |NODE3:node|)))
 (not $x14)))
(assert
 (= |NODE2:node| |NODE3:node|))
(assert
 (let (($x65 (= |NODE2:node| |NODE3:node|)))
 (not $x65)))
(check-sat)
