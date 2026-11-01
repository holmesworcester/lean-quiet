import ops.connection.DiscoveryStorage
import ops.connection.DiscoveryProgress
#print axioms Connection.Winner.choose_comm
#print axioms Connection.Winner.choose_stable
#print axioms Connection.Winner.exactly_one
#print axioms Connection.DiscoveryLaws.kept_pair
#print axioms Connection.DiscoveryLaws.both_choose_same
#print axioms Connection.DiscoveryLaws.single_survivor
#print axioms Connection.DiscoveryLaws.no_flapping
#print axioms Connection.DiscoveryLaws.publication_auth
#print axioms Connection.DiscoveryLaws.candidate_cap
#print axioms Connection.DiscoveryLaws.retry_eventually_due
#print axioms Connection.DiscoveryLaws.candidate_visited
#print axioms Endpoint.bounded_cap
#print axioms Endpoint.delay_bounded
#print axioms Endpoint.fresh_expires

#print axioms Connection.DiscoveryProgress.plan_ready
#print axioms Connection.DiscoveryProgress.plan_backoff
#print axioms Connection.DiscoveryProgress.plan_after_backoff

#print axioms Connection.DiscoveryStorage.dial_reads
#print axioms Connection.DiscoveryStorage.readOnly
#print axioms Connection.DiscoveryStorage.step_moves
#print axioms Connection.DiscoveryStorage.step_retains
#print axioms Connection.DiscoveryStorage.step_settled

#print axioms Connection.DiscoveryStorage.setup_readOnly
