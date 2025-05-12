; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((node (node0) (node1) (node2))))
 (declare-fun |NODE2:node| () node)
(declare-fun |NODE0:node| () node)
(declare-fun |NODE1:node| () node)
(declare-fun |NODE3:node| () node)
(assert
 (let (($x10 (= |NODE0:node| |NODE2:node|)))
 (let (($x21 (not $x10)))
 (let (($x17 (= |NODE1:node| |NODE2:node|)))
 (let (($x26 (not $x17)))
 (let (($x14 (= |NODE0:node| |NODE1:node|)))
 (let (($x15 (not $x14)))
 (let (($x30 (= |NODE2:node| |NODE3:node|)))
 (let (($x19 (= |NODE0:node| |NODE3:node|)))
 (let (($x23 (not $x19)))
 (let (($x13 (= |NODE1:node| |NODE3:node|)))
 (let (($x28 (not $x13)))
 (let (($x36 (or (and $x10 $x13 $x15) (and $x17 $x13 $x15) (and $x19 $x10 $x15) (and $x14 $x19 $x21) (and $x14 $x10 $x23) (and $x19 $x17 $x15) (and $x13 $x15 $x26 $x21) (and $x10 $x15 $x28 $x23) (and $x14 $x21 (not $x30) $x23) (and $x19 $x15 $x26 $x21) (and $x17 $x15 $x28 $x23) (and $x30 $x15 $x26 $x21))))
 (and (not $x36)))))))))))))))
(assert
 (= |NODE0:node| |NODE1:node|))
(assert
 (let (($x14 (= |NODE0:node| |NODE1:node|)))
 (not $x14)))
(assert
 (= |NODE0:node| |NODE2:node|))
(assert
 (let (($x10 (= |NODE0:node| |NODE2:node|)))
 (not $x10)))
(assert
 (= |NODE0:node| |NODE3:node|))
(assert
 (let (($x19 (= |NODE0:node| |NODE3:node|)))
 (not $x19)))
(assert
 (= |NODE1:node| |NODE2:node|))
(assert
 (let (($x17 (= |NODE1:node| |NODE2:node|)))
 (not $x17)))
(assert
 (= |NODE1:node| |NODE3:node|))
(assert
 (let (($x13 (= |NODE1:node| |NODE3:node|)))
 (not $x13)))
(assert
 (= |NODE2:node| |NODE3:node|))
(assert
 (let (($x30 (= |NODE2:node| |NODE3:node|)))
 (not $x30)))
(check-sat)
