declare -a instances=(
 "Consensus"
 "naive_consensus"
 "toy_consensus"
 "toy_consensus_forall"
 "toy_consensus_epr"
 "consensus_epr"
 "lock_server"
 "lockserv"
 "lockserv_automaton"
 "simple-decentralized-lock"
 "client_server_ae"
 "Ricart-Agrawala"
 "sharded_kv"
 "sharded_kv_no_lost_keys"
 "firewall"
 "TCommit"
 "TwoPhase"
 "simple-election"
 "quorum-leader-election-wo-maj"

)

for case in "${instances[@]}"; do
    grep -r "CUTOFF"  ./${case}.log
done 

echo ""

for case in "${instances[@]}"; do
    tail -n 2  ./${case}.log
done 
