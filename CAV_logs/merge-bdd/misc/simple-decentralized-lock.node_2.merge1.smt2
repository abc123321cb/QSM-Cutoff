; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((node (node0) (node1))))
 (declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun |NODE3:node| () node)
(declare-fun |NODE2:node| () node)
(assert
 (let (($x9 (= |NODE0:node| |NODE1:node|)))
 (let (($x18 (not $x9)))
 (let (($x21 (= |NODE1:node| |NODE3:node|)))
 (let (($x13 (= |NODE0:node| |NODE2:node|)))
 (let (($x25 (or (and $x9 (= |NODE0:node| |NODE3:node|) (not $x13)) (and $x9 $x13 (not (= |NODE0:node| |NODE3:node|))) (and (= |NODE0:node| |NODE3:node|) $x13 $x18) (and (= |NODE1:node| |NODE2:node|) $x21 $x18) (and (= |NODE0:node| |NODE3:node|) (= |NODE1:node| |NODE2:node|) $x18) (and $x13 $x21 $x18))))
 (and (not $x25))))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x9 (= |NODE0:node| |NODE1:node|)))
 (not $x9)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x13 (= |NODE0:node| |NODE2:node|)))
 (not $x13)))
(assert
 (= |NODE0:node| |NODE3:node|))
(assert
 (let (($x11 (= |NODE0:node| |NODE3:node|)))
 (not $x11)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x20 (= |NODE1:node| |NODE2:node|)))
 (not $x20)))
(assert
 (= |NODE1:node| |NODE3:node|))
(assert
 (let (($x21 (= |NODE1:node| |NODE3:node|)))
 (not $x21)))
(assert
 (= |NODE2:node| |NODE3:node|))
(assert
 (let (($x61 (= |NODE2:node| |NODE3:node|)))
 (not $x61)))
(check-sat)
