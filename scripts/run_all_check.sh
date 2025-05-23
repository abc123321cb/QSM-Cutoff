sym_path='ivybench/sym/ivy/'
sym_quorum_path='ivybench/sym_quorum/ivy/'
Timeout=36000

timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}Consensus.ivy                            -s value=1                            -e -t -k -v 5 -w -l ${sym_path}Consensus.check.log
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}TCommit.ivy                              -s resource_manager=1                 -e -t -k -v 5 -w -l ${sym_path}TCommit.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}Ricart-Agrawala.ivy                      -s node=1                             -e -t -k -v 5 -w -l ${sym_path}Ricart-Agrawala.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}lock_server.ivy                          -s server=1,client=1                  -e -t -k -v 5 -w -l ${sym_path}lock_server.check.log                                
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}sharded_kv.ivy                           -s node=1,key=1,value=1               -e -t -k -v 5 -w -l ${sym_path}sharded_kv.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}sharded_kv_no_lost_keys.ivy              -s node=1,key=1,value=1               -e -t -k -v 5 -w -l ${sym_path}sharded_kv_no_lost_keys.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}simple-decentralized-lock.ivy            -s node=1                             -e -t -k -v 5 -w -l ${sym_path}simple-decentralized-lock.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}firewall.ivy                             -s node=1                                -t -k -v 5 -w -l ${sym_path}firewall.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}lockserv.ivy                             -s node=1                             -e -t -k -v 5 -w -l ${sym_path}lockserv.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}lockserv_automaton.ivy                   -s node=1                             -e -t -k -v 5 -w -l ${sym_path}lockserv_automaton.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}client_server_ae.ivy                     -s node=1,request=1,response=1        -e -t -k -v 5 -w -l ${sym_path}client_server_ae.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_path}TwoPhase.ivy                             -s resource_manager=1                 -e -t -k -v 5 -w -l ${sym_path}TwoPhase.check.log
                                                                                                                                  
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}toy_consensus.ivy                 -s node=2,value=1                     -e -t -k -v 5 -w -l ${sym_quorum_path}toy_consensus.check.log
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}toy_consensus_epr.ivy             -s node=2,value=1                     -e -t -k -v 5 -w -l ${sym_quorum_path}toy_consensus_epr.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}naive_consensus.ivy               -s node=2,value=1                     -e -t -k -v 5 -w -l ${sym_quorum_path}naive_consensus.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}toy_consensus_forall.ivy          -s node=2,value=1                     -e -t -k -v 5 -w -l ${sym_quorum_path}toy_consensus_forall.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}simple-election.ivy               -s acceptor=2,proposer=1              -e -t -k -v 5 -w -l ${sym_quorum_path}simple-election.check.log 
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}quorum-leader-election-wo-maj.ivy -s node=2                                -t -k -v 5 -w -l ${sym_quorum_path}quorum-leader-election-wo-maj.check.log
timeout ${Timeout} python3 QSM-Cutoff.py ${sym_quorum_path}consensus_epr.ivy                 -s node=2,value=1                   -b   -t -k -v 5 -w -l ${sym_quorum_path}consensus_epr.check.log 
