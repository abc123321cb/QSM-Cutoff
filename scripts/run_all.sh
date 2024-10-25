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

# running until cut-off
for instance in ${sym_instances[@]}; do
    log=${sym_path}${instance}.log
    yaml=${yaml_path}${instance}.yaml
    python3 run_all.py $yaml -v 5 -w -l $log
done
for instance in ${sym_quorum_instances[@]}; do
    log=${sym_quorum_path}${instance}.log
    yaml=${yaml_path}${instance}.yaml
    python3 run_all.py $yaml -v 5 -w -l $log
done
python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -l ${sym_quorum_path}quorum-leader-election-wo-maj.log

# running <= cut-off
timeout ${Timeout} python3 qrm.py ${sym_path}Consensus.ivy                 -s value=4                      -v 5 -w -l ${sym_path}Consensus.log
timeout ${Timeout} python3 qrm.py ${sym_path}TCommit.ivy                   -s resource_manager=3           -v 5 -w -l ${sym_path}TCommit.log 
timeout ${Timeout} python3 qrm.py ${sym_path}Ricart-Agrawala.ivy           -s node=3                       -v 5 -w -l ${sym_path}Ricart-Agrawala.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lock_server.ivy               -s server=2,client=4            -v 5 -w -l ${sym_path}lock_server.log 
timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv.ivy                -s node=4,key=3,value=3         -v 5 -w -l ${sym_path}sharded_kv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}sharded_kv_no_lost_keys.ivy   -s node=4,key=3,value=3         -v 5 -w -l ${sym_path}sharded_kv_no_lost_keys.log 
timeout ${Timeout} python3 qrm.py ${sym_path}simple-decentralized-lock.ivy -s node=4                       -v 5 -w -l ${sym_path}simple-decentralized-lock.log 
timeout ${Timeout} python3 qrm.py ${sym_path}firewall.ivy                  -s node=4                       -v 5 -w -l ${sym_path}firewall.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv.ivy                  -s node=4                       -v 5 -w -l ${sym_path}lockserv.log 
timeout ${Timeout} python3 qrm.py ${sym_path}lockserv_automaton.ivy        -s node=4                       -v 5 -w -l ${sym_path}lockserv_automaton.log 
timeout ${Timeout} python3 qrm.py ${sym_path}client_server_ae.ivy          -s node=2,request=2,response=2  -v 5 -w -l ${sym_path}client_server_ae.log 
timeout ${Timeout} python3 qrm.py ${sym_path}TwoPhase.ivy                  -s resource_manager=3           -v 5 -w -l ${sym_path}TwoPhase.log

# running one-size > cut-off
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus.ivy                 -s node=4,value=4        -v 5 -w -l ${sym_quorum_path}toy_consensus.log
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=4,value=4        -v 5 -w -l ${sym_quorum_path}toy_consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}naive_consensus.ivy               -s node=4,value=4        -v 5 -w -l ${sym_quorum_path}naive_consensus.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}simple-election.ivy               -s acceptor=4,proposer=4 -v 5 -w -l ${sym_quorum_path}simple-election.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}consensus_epr.ivy                 -s node=4,value=3        -v 5 -w -l ${sym_quorum_path}consensus_epr.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=6,value=4        -v 5 -w -l ${sym_quorum_path}toy_consensus_forall.log 
timeout ${Timeout} python3 qrm.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=6                -m -v 5 -w -l ${sym_quorum_path}quorum-leader-election-wo-maj.log