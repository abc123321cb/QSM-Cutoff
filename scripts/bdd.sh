sym_path='ivybench/sym/ivy/'
sym_quorum_path='ivybench/sym_quorum/ivy/'
sym_ring_path='ivybench/sym_ring/ivy/'
yaml_path='yamls/'
Timeout=2000
Memout=15000 #15GB

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
#for instance in ${sym_instances[@]}; do
#    log=${sym_path}${instance}.log
#    yaml=${yaml_path}${instance}.yaml
#    python3 run_all.py $yaml -v 5 -w -l $log
#done
#for instance in ${sym_quorum_instances[@]}; do
#    log=${sym_quorum_path}${instance}.log
#    yaml=${yaml_path}${instance}.yaml
#    python3 run_all.py $yaml -v 5 -w -l $log
#done
#python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -l ${sym_quorum_path}quorum-leader-election-wo-maj.log

./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}Consensus.ivy                            -s value=4                         -v 5 -w -l ${sym_path}Consensus.bdd.log                            2> ${sym_path}Consensus.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}TCommit.ivy                              -s resource_manager=3              -v 5 -w -l ${sym_path}TCommit.bdd.log                              2> ${sym_path}TCommit.bdd.runlim.log                                            
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}Ricart-Agrawala.ivy                      -s node=3                          -v 5 -w -l ${sym_path}Ricart-Agrawala.bdd.log                      2> ${sym_path}Ricart-Agrawala.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}lock_server.ivy                          -s server=2,client=4               -v 5 -w -l ${sym_path}lock_server.bdd.log                          2> ${sym_path}lock_server.bdd.runlim.log                                     
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}sharded_kv.ivy                           -s node=4,key=2,value=3            -v 5 -w -l ${sym_path}sharded_kv.bdd.log                           2> ${sym_path}sharded_kv.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}sharded_kv_no_lost_keys.ivy              -s node=4,key=2,value=3            -v 5 -w -l ${sym_path}sharded_kv_no_lost_keys.bdd.log              2> ${sym_path}sharded_kv_no_lost_keys.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}simple-decentralized-lock.ivy            -s node=4                          -v 5 -w -l ${sym_path}simple-decentralized-lock.bdd.log            2> ${sym_path}simple-decentralized-lock.bdd.runlim.log 
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}firewall.ivy                             -s node=4                          -v 5 -w -l ${sym_path}firewall.bdd.log                             2> ${sym_path}firewall.bdd.runlim.log 
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}lockserv.ivy                             -s node=4                          -v 5 -w -l ${sym_path}lockserv.bdd.log                             2> ${sym_path}lockserv.bdd.runlim.log 
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}lockserv_automaton.ivy                   -s node=4                          -v 5 -w -l ${sym_path}lockserv_automaton.bdd.log                   2> ${sym_path}lockserv_automaton.bdd.runlim.log 
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}TwoPhase.ivy                             -s resource_manager=2              -v 5 -w -l ${sym_path}TwoPhase.bdd.log                             2> ${sym_path}TwoPhase.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_path}client_server_ae.ivy                     -s node=2,request=2,response=2     -v 5 -w -l ${sym_path}client_server_ae.bdd.log                     2> ${sym_path}client_server_ae.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_quorum_path}naive_consensus.ivy               -s node=4,quorum=4,value=4         -v 5 -w -l ${sym_quorum_path}naive_consensus.bdd.log               2> ${sym_path}naive_consensus.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_quorum_path}toy_consensus.ivy                 -s node=4,quorum=4,value=4         -v 5 -w -l ${sym_quorum_path}toy_consensus.bdd.log                 2> ${sym_path}toy_consensus.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_quorum_path}toy_consensus_epr.ivy             -s node=4,quorum=4,value=4         -v 5 -w -l ${sym_quorum_path}toy_consensus_epr.bdd.log             2> ${sym_path}toy_consensus_epr.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_quorum_path}simple-election.ivy               -s acceptor=4,quorum=4,proposer=4  -v 5 -w -l ${sym_quorum_path}simple-election.bdd.log               2> ${sym_path}simple-election.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_quorum_path}consensus_epr.ivy                 -s node=4,quorum=4,value=3         -v 5 -w -l ${sym_quorum_path}consensus_epr.bdd.log                 2> ${sym_path}consensus_epr.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_quorum_path}toy_consensus_forall.ivy          -s node=4,quorum=4,value=4         -v 5 -w -l ${sym_quorum_path}toy_consensus_forall.bdd.log          2> ${sym_path}toy_consensus_forall.bdd.runlim.log
./runlim --time-limit=${Timeout} --space-limit=${Memout} python3 qrm.py -i ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=6,nset=15                  -v 5 -w -l ${sym_quorum_path}quorum-leader-election-wo-maj.bdd.log 2> ${sym_path}quorum-leader-election-wo-maj.bdd.runlim.log
