sym_path='ivybench/sym/ivy/'
sym_quorum_path='ivybench/sym_quorum/ivy/'
sym_ring_path='ivybench/sym_ring/ivy/'
yaml_path='yamls/'
Timeout=6000

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

timeout ${Timeout} python3 qrm.py ${sym_path}Consensus.ivy                 -s value=3                      -e -v 5 -w -l ${sym_path}Consensus.cutoff.log
timeout ${Timeout} python3 qrm.py ${sym_path}TCommit.ivy                   -s resource_manager=2           -e -v 5 -w -l ${sym_path}TCommit.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}Ricart-Agrawala.ivy           -s node=2                       -e -v 5 -w -l ${sym_path}Ricart-Agrawala.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=1,client=3            -e -v 5 -w -l ${sym_path}lock_server.cutoff.log                                
timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv.ivy                -s node=3,key=1,value=2         -e -v 5 -w -l ${sym_path}sharded_kv.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv_no_lost_keys.ivy   -s node=3,key=1,value=2         -e -v 5 -w -l ${sym_path}sharded_kv_no_lost_keys.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}simple-decentralized-lock.ivy -s node=3                       -e -v 5 -w -l ${sym_path}simple-decentralized-lock.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}firewall.ivy                  -s node=3                          -v 5 -w -l ${sym_path}firewal.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv.ivy                  -s node=3                       -e -v 5 -w -l ${sym_path}lockserv.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv_automaton.ivy        -s node=3                       -e -v 5 -w -l ${sym_path}lockserv_automaton.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}client_server_ae.ivy          -s node=1,request=1,response=1  -e -v 5 -w -l ${sym_path}client_server_ae.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_path}TwoPhase.ivy                  -s resource_manager=1           -e -v 5 -w -l ${sym_path}TwoPhase.cutoff.log

timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus.ivy                 -s node=3,value=3           -e -v 5 -w -l ${sym_quorum_path}toy_consensus.cutoff.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=3,value=3           -e -v 5 -w -l ${sym_quorum_path}toy_consensus_epr.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}naive_consensus.ivy               -s node=3,value=3           -e -v 5 -w -l ${sym_quorum_path}naive_consensus.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}simple-election.ivy               -s acceptor=3,proposer=3    -e -v 5 -w -l ${sym_quorum_path}simple-election.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=3,value=3           -e -v 5 -w -l ${sym_quorum_path}toy_consensus_forall.cutoff.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=5                      -v 5 -w -l ${sym_quorum_path}quorum-leader-election-wo-maj.cutoff.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}consensus_epr.ivy                 -s node=3,value=2              -v 5 -w -l ${sym_quorum_path}consensus_epr.cutoff.log 
