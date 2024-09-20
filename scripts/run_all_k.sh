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
    python3 run_all.py $yaml -v 5 -w -k -l $log
done
for instance in ${sym_quorum_instances[@]}; do
    log=${sym_quorum_path}${instance}.log
    yaml=${yaml_path}${instance}.yaml
    python3 run_all.py $yaml -v 5 -w -k -l $log
done
python3 run_all.py ${yaml_path}quorum-leader-election-wo-maj.yaml -m -v 5 -w -k -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
