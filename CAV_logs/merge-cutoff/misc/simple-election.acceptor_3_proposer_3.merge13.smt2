; benchmark generated from python API
(set-info :status unknown)
(declare-datatypes () ((proposer (proposer0) (proposer1) (proposer2))))
 (declare-datatypes ((acceptor 0)) ((acceptor (acceptor0) (acceptor1) (acceptor2))))
 (declare-datatypes ((quorum 0)) ((quorum (quorum__acceptor0_acceptor1) (quorum__acceptor0_acceptor2) (quorum__acceptor1_acceptor2))))
 (declare-fun |PROPOSER2:proposer| () proposer)
(declare-fun |PROPOSER1:proposer| () proposer)
(declare-fun |PROPOSER0:proposer| () proposer)
(declare-fun |ACCEPTOR1:acceptor| () acceptor)
(declare-fun |ACCEPTOR0:acceptor| () acceptor)
(declare-fun member (acceptor quorum) Bool)
(assert
 (let (($x32 (= |PROPOSER1:proposer| |PROPOSER2:proposer|)))
 (let (($x39 (not $x32)))
 (let (($x37 (= |PROPOSER0:proposer| |PROPOSER2:proposer|)))
 (let (($x38 (not $x37)))
 (let (($x34 (= |PROPOSER0:proposer| |PROPOSER1:proposer|)))
 (let (($x35 (not $x34)))
 (let (($x25 (= |ACCEPTOR0:acceptor| |ACCEPTOR1:acceptor|)))
 (let (($x26 (not $x25)))
 (and (member acceptor0 quorum__acceptor0_acceptor1) (member acceptor1 quorum__acceptor0_acceptor1) (not (member acceptor2 quorum__acceptor0_acceptor1)) (member acceptor0 quorum__acceptor0_acceptor2) (not (member acceptor1 quorum__acceptor0_acceptor2)) (member acceptor2 quorum__acceptor0_acceptor2) (not (member acceptor0 quorum__acceptor1_acceptor2)) (member acceptor1 quorum__acceptor1_acceptor2) (member acceptor2 quorum__acceptor1_acceptor2) (not (or (and $x26 $x32 $x35) (and $x26 $x35 $x38 $x39)))))))))))))
(assert
 (= |PROPOSER0:proposer| |PROPOSER1:proposer|))
(assert
 (let (($x34 (= |PROPOSER0:proposer| |PROPOSER1:proposer|)))
 (not $x34)))
(assert
 (= |PROPOSER0:proposer| |PROPOSER2:proposer|))
(assert
 (let (($x37 (= |PROPOSER0:proposer| |PROPOSER2:proposer|)))
 (not $x37)))
(assert
 (= |PROPOSER1:proposer| |PROPOSER2:proposer|))
(assert
 (let (($x32 (= |PROPOSER1:proposer| |PROPOSER2:proposer|)))
 (not $x32)))
(assert
 (= |ACCEPTOR0:acceptor| |ACCEPTOR1:acceptor|))
(assert
 (let (($x25 (= |ACCEPTOR0:acceptor| |ACCEPTOR1:acceptor|)))
 (not $x25)))
(check-sat)
