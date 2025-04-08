; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((node (node0) (node1) (node2))))
 (declare-fun |NODE1:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun |NODE2:node| () node)
(declare-fun |NODE3:node| () node)
(assert
 (let (($x17 (= |NODE0:node| |NODE1:node|)))
 (let (($x18 (not $x17)))
 (let (($x13 (= |NODE0:node| |NODE2:node|)))
 (let (($x24 (not $x13)))
 (let (($x20 (= |NODE1:node| |NODE2:node|)))
 (let (($x34 (not $x20)))
 (let (($x40 (= |NODE2:node| |NODE3:node|)))
 (let (($x16 (= |NODE1:node| |NODE3:node|)))
 (let (($x41 (not $x16)))
 (let (($x22 (= |NODE0:node| |NODE3:node|)))
 (let (($x6 (not $x22)))
 (let (($x33 (or (and $x13 $x16 $x18) (and $x16 $x20 $x18) (and $x22 $x13 $x18) (and $x22 $x17 $x24) (and $x17 $x13 $x6) (and $x22 $x20 $x18) (and $x16 $x34 $x24 $x18) (and $x13 $x6 $x41 $x18) (and $x17 $x6 $x24 (not $x40)) (and $x22 $x34 $x24 $x18) (and $x20 $x6 $x41 $x18) (and $x40 $x34 $x24 $x18))))
 (and (not $x33)))))))))))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x17 (= |NODE0:node| |NODE1:node|)))
 (not $x17)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x13 (= |NODE0:node| |NODE2:node|)))
 (not $x13)))
(assert
 (= |NODE0:node| |NODE3:node|))
(assert
 (let (($x22 (= |NODE0:node| |NODE3:node|)))
 (not $x22)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x20 (= |NODE1:node| |NODE2:node|)))
 (not $x20)))
(assert
 (= |NODE1:node| |NODE3:node|))
(assert
 (let (($x16 (= |NODE1:node| |NODE3:node|)))
 (not $x16)))
(assert
 (= |NODE2:node| |NODE3:node|))
(assert
 (let (($x40 (= |NODE2:node| |NODE3:node|)))
 (not $x40)))
(check-sat)
