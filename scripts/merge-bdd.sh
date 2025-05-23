sym_path='ivybench/sym/ivy/'
sym_quorum_path='ivybench/sym_quorum/ivy/'
Timeout=6000

timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}Consensus.ivy                            -s value=1                          -b  -e  -v 5 -w -l ${sym_path}Consensus.log
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}TCommit.ivy                              -s resource_manager=1               -b  -e  -v 5 -w -l ${sym_path}TCommit.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}Ricart-Agrawala.ivy                      -s node=1                           -b  -e  -v 5 -w -l ${sym_path}Ricart-Agrawala.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}lock_server.ivy                          -s server=1,client=1                -b  -e  -v 5 -w -l ${sym_path}lock_server.log                                
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}sharded_kv.ivy                           -s node=1,key=1,value=1             -b  -e  -v 5 -w -l ${sym_path}sharded_kv.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}sharded_kv_no_lost_keys.ivy              -s node=1,key=1,value=1             -b  -e  -v 5 -w -l ${sym_path}sharded_kv_no_lost_keys.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}simple-decentralized-lock.ivy            -s node=1                           -b  -e  -v 5 -w -l ${sym_path}simple-decentralized-lock.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}firewall.ivy                             -s node=1                           -b      -v 5 -w -l ${sym_path}firewall.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}lockserv.ivy                             -s node=1                           -b  -e  -v 5 -w -l ${sym_path}lockserv.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}lockserv_automaton.ivy                   -s node=1                           -b  -e  -v 5 -w -l ${sym_path}lockserv_automaton.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}client_server_ae.ivy                     -s node=1,request=1,response=1      -b  -e  -v 5 -w -l ${sym_path}client_server_ae.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}TwoPhase.ivy                             -s resource_manager=1               -b  -e  -v 5 -w -l ${sym_path}TwoPhase.log

timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}toy_consensus.ivy                 -s node=2,value=1                   -b  -e -v 5 -w -l ${sym_quorum_path}toy_consensus.log
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=2,value=1                   -b  -e -v 5 -w -l ${sym_quorum_path}toy_consensus_epr.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}naive_consensus.ivy               -s node=2,value=1                   -b  -e -v 5 -w -l ${sym_quorum_path}naive_consensus.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}simple-election.ivy               -s acceptor=2,proposer=1            -b  -e -v 5 -w -l ${sym_quorum_path}simple-election.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=2,value=1                   -b  -e -v 5 -w -l ${sym_quorum_path}toy_consensus_forall.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=2                           -b      -v 5 -w -l ${sym_quorum_path}quorum-leader-election-wo-maj.log
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}consensus_epr.ivy                 -s node=2,value=1                   -b      -v 5 -w -l ${sym_quorum_path}consensus_epr.log 
