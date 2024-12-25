sym_path='ivybench/sym/ivy/'
sym_quorum_path='ivybench/sym_quorum/ivy/'
sym_ring_path='ivybench/sym_ring/ivy/'
yaml_path='yamls/'
Timeout=36000

declare -a sym_instances=(
    "Consensus"
    "TCommit"
    "Ricart-Agrawala"
    "lock_server"
    "sharded_kv"
    "sharded_kv_no_lost_keys"
    "simple-decentralized-lock"
    "firewall"
    "lockserv"
    "lockserv_automaton"
    "client_server_ae"
    "TwoPhase"
)

declare -a sym_quorum_instances=(
    "toy_consensus"
    "toy_consensus_epr"
    "naive_consensus"
    "simple-election"
    "consensus_epr"
    "toy_consensus_forall"
#    "quorum-leader-election-wo-maj" need -m
)

declare -a hard_sym_instances=(
    "learning_switch_forallexists"
    "client_server_db_ae"
    "learning_switch"
    "two_phase_commit"
)

declare -a hard_sym_quorum_instances=(
    "consensus_forall"
    "consensus_wo_decide"
)

declare -a hard_sym_ring_instances=(
    "Simple"
    "SimpleRegular"
    "chord_ring_maintenance"
)

timeout ${Timeout} python3 qrm.py ${sym_path}Consensus.ivy                 -s value=2                      -v 5 -w -k -l ${sym_path}Consensus.log
timeout ${Timeout} python3 qrm.py ${sym_path}Consensus.ivy                 -s value=3                      -v 5 -w -k -l ${sym_path}Consensus.log
timeout ${Timeout} python3 qrm.py ${sym_path}Consensus.ivy                 -s value=4                      -v 5 -w -k -l ${sym_path}Consensus.log
timeout ${Timeout} python3 qrm.py ${sym_path}TCommit.ivy                   -s resource_manager=1           -v 5 -w -k -l ${sym_path}TCommit.log 
timeout ${Timeout} python3 qrm.py ${sym_path}TCommit.ivy                   -s resource_manager=2           -v 5 -w -k -l ${sym_path}TCommit.log 
timeout ${Timeout} python3 qrm.py ${sym_path}TCommit.ivy                   -s resource_manager=3           -v 5 -w -k -l ${sym_path}TCommit.log 
timeout ${Timeout} python3 qrm.py ${sym_path}Ricart-Agrawala.ivy           -s node=1                       -v 5 -w -k -l ${sym_path}Ricart-Agrawala.log 
timeout ${Timeout} python3 qrm.py ${sym_path}Ricart-Agrawala.ivy           -s node=2                       -v 5 -w -k -l ${sym_path}Ricart-Agrawala.log 
timeout ${Timeout} python3 qrm.py ${sym_path}Ricart-Agrawala.ivy           -s node=3                       -v 5 -w -k -l ${sym_path}Ricart-Agrawala.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=1,client=1            -v 5 -w -k -l ${sym_path}lock_server.log                                python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=1,client=2            -v 5 -w -k -l ${sym_path}lock_server.log                                python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=1,client=3            -v 5 -w -k -l ${sym_path}lock_server.log                                python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=2,client=1            -v 5 -w -k -l ${sym_path}lock_server.log                                python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=2,client=2            -v 5 -w -k -l ${sym_path}lock_server.log                                python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=2,client=3            -v 5 -w -k -l ${sym_path}lock_server.log                                python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=2,client=4            -v 5 -w -k -l ${sym_path}lock_server.log                                python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log

timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv.ivy                -s node=1,key=1,value=1         -v 5 -w -k -l ${sym_path}sharded_kv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv.ivy                -s node=3,key=2,value=2         -v 5 -w -k -l ${sym_path}sharded_kv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv_no_lost_keys.ivy   -s node=1,key=1,value=1         -v 5 -w -k -l ${sym_path}sharded_kv_no_lost_keys.log 
timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv_no_lost_keys.ivy   -s node=3,key=2,value=2         -v 5 -w -k -l ${sym_path}sharded_kv_no_lost_keys.log 
timeout ${Timeout} python3 qrm.py ${sym_path}simple-decentralized-lock.ivy -s node=1                       -v 5 -w -k -l ${sym_path}simple-decentralized-lock.log 
timeout ${Timeout} python3 qrm.py ${sym_path}simple-decentralized-lock.ivy -s node=2                       -v 5 -w -k -l ${sym_path}simple-decentralized-lock.log 
timeout ${Timeout} python3 qrm.py ${sym_path}simple-decentralized-lock.ivy -s node=3                       -v 5 -w -k -l ${sym_path}simple-decentralized-lock.log 
timeout ${Timeout} python3 qrm.py ${sym_path}simple-decentralized-lock.ivy -s node=4                       -v 5 -w -k -l ${sym_path}simple-decentralized-lock.log 
timeout ${Timeout} python3 qrm.py ${sym_path}firewall.ivy                  -s node=1                       -v 5 -w -k -l ${sym_path}firewall.log 
timeout ${Timeout} python3 qrm.py ${sym_path}firewall.ivy                  -s node=2                       -v 5 -w -k -l ${sym_path}firewall.log 
timeout ${Timeout} python3 qrm.py ${sym_path}firewall.ivy                  -s node=3                       -v 5 -w -k -l ${sym_path}firewall.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv.ivy                  -s node=1                       -v 5 -w -k -l ${sym_path}lockserv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv.ivy                  -s node=2                       -v 5 -w -k -l ${sym_path}lockserv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv.ivy                  -s node=3                       -v 5 -w -k -l ${sym_path}lockserv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv.ivy                  -s node=4                       -v 5 -w -k -l ${sym_path}lockserv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv_automaton.ivy        -s node=1                       -v 5 -w -k -l ${sym_path}lockserv_automaton.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv_automaton.ivy        -s node=2                       -v 5 -w -k -l ${sym_path}lockserv_automaton.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv_automaton.ivy        -s node=3                       -v 5 -w -k -l ${sym_path}lockserv_automaton.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv_automaton.ivy        -s node=4                       -v 5 -w -k -l ${sym_path}lockserv_automaton.log 
timeout ${Timeout} python3 qrm.py ${sym_path}client_server_ae.ivy          -s node=1,request=1,response=1  -v 5 -w -k -l ${sym_path}client_server_ae.log 
timeout ${Timeout} python3 qrm.py ${sym_path}client_server_ae.ivy          -s node=2,request=2,response=2  -v 5 -w -k -l ${sym_path}client_server_ae.log 
timeout ${Timeout} python3 qrm.py ${sym_path}TwoPhase.ivy                  -s resource_manager=1           -v 5 -w -k -l ${sym_path}TwoPhase.log
timeout ${Timeout} python3 qrm.py ${sym_path}TwoPhase.ivy                  -s resource_manager=2           -v 5 -w -k -l ${sym_path}TwoPhase.log
timeout ${Timeout} python3 qrm.py ${sym_path}TwoPhase.ivy                  -s resource_manager=3           -v 5 -w -k -l ${sym_path}TwoPhase.log


timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus.ivy                 -s node=1,value=1        -v 5 -w -k -l ${sym_quorum_path}toy_consensus.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus.ivy                 -s node=2,value=2        -v 5 -w -k -l ${sym_quorum_path}toy_consensus.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus.ivy                 -s node=3,value=3        -v 5 -w -k -l ${sym_quorum_path}toy_consensus.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus.ivy                 -s node=4,value=4        -v 5 -w -k -l ${sym_quorum_path}toy_consensus.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=1,value=1        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=2,value=2        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=3,value=3        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=4,value=4        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}naive_consensus.ivy               -s node=1,value=1        -v 5 -w -k -l ${sym_quorum_path}naive_consensus.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}naive_consensus.ivy               -s node=2,value=2        -v 5 -w -k -l ${sym_quorum_path}naive_consensus.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}naive_consensus.ivy               -s node=3,value=3        -v 5 -w -k -l ${sym_quorum_path}naive_consensus.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}naive_consensus.ivy               -s node=4,value=4        -v 5 -w -k -l ${sym_quorum_path}naive_consensus.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=1,value=1        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_forall.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=2,value=2        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_forall.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=3,value=3        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_forall.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=4,value=3        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_forall.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=5,value=3        -v 5 -w -k -l ${sym_quorum_path}toy_consensus_forall.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}consensus_epr.ivy                 -s node=1,value=1        -v 5 -w -k -l ${sym_quorum_path}consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}consensus_epr.ivy                 -s node=2,value=2        -v 5 -w -k -l ${sym_quorum_path}consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}consensus_epr.ivy                 -s node=3,value=2        -v 5 -w -k -l ${sym_quorum_path}consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}simple-election.ivy               -s acceptor=1,proposer=1 -v 5 -w -k -l ${sym_quorum_path}simple-election.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}simple-election.ivy               -s acceptor=2,proposer=2 -v 5 -w -k -l ${sym_quorum_path}simple-election.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}simple-election.ivy               -s acceptor=3,proposer=3 -v 5 -w -k -l ${sym_quorum_path}simple-election.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=1                -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=2                -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=3                -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=4                -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=5                -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log