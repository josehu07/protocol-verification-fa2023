// Midterm Project: Distributed lock server
// Build a distributed lock server. Define how a host implements your
// protocol in host.v.dfy; write your safety spec and proof here.

// This challenge differs from LockServer (from chapters 03 and 04) in two
// ways. First, there is no central server that coordinates the activity.
// Second, the hosts can communicate only via asynchronous messages; a single
// state machine transition cannot simultaneously read or update the state of
// two hosts.
//
// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1, while all other nodes with an epoch of 0 (and not
// holding the lock). A node that holds the lock can "grant" it to another
// node by sending them a "Grant" message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’s
// epoch number.

// You'll first need to modify 'host.v.dfy' to define the protocol message
// format and the host behavior.
// Then come back here to define the safety condition and prove that the
// distributed system made from that protocol maintains it.

// The ".t.dfy" extension in network.t.dfy and distributed_system.t.dfy
// indicates these files are _trusted_: they are assumed correct. In contrast,
// the ".v.dfy" in host.v.dfy indicates that the code in that file is verified.
// This file (exercise01.dfy) doesn't have an extension. It mixes some trusted
// code (your safety specification and the statement of the safety theorem) and
// untrusted, verified code (your inductive invariant). We mix these only to
// make navigating your code a bit simpler.

include "distributed_system.t.dfy"

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // Define this predicate to be true if idx is a valid host ID and that host's
  // Variables indicates that it holds the lock.
  ghost predicate HostHoldsLock(v:DistributedSystem.Variables, idx: int) {
    && v.WF()
       // DONE: fill in here (solution: 4 lines)
    && v.ValidHostId(idx)
    && v.hosts[idx].holdsLock
       // END EDIT
  }

  // No two hosts think they hold the lock simultaneously.
  ghost predicate Safety(v:DistributedSystem.Variables) {
    // DONE: fill in here (solution: 4 lines)
    forall h1:HostId, h2:HostId | && v.ValidHostId(h1)
                                  && v.ValidHostId(h2)
                                  && HostHoldsLock(v, h1)
                                  && HostHoldsLock(v, h2)
      :: h1 == h2
         // END EDIT
  }
}

module Proof {
  import opened HostIdentifiers
  import Host
  import opened DistributedSystem
  import opened SafetySpec

  // Here's a predicate that will be very useful in constructing inviariant
  // conjuncts. Your job is to figure out what this predicate should say about
  // the message, especially about epoch numbers: intuitively, an in-flight
  // message might be received, but a not-in-flight message will always be
  // ignored by hosts.
  ghost predicate InFlight(v:Variables, message:Host.Message) {
    && v.WF()
    && message in v.network.sentMsgs
                  // DONE: fill in here (solution: 2 lines)
    && v.ValidHostId(message.dest)
    && v.hosts[message.dest].epoch < message.epoch
       // END EDIT
  }

  ghost predicate InFlightMsgHighestEpoch(v:Variables) {
    forall m | m in v.network.sentMsgs && InFlight(v, m)
      :: forall mm | mm in v.network.sentMsgs && mm != m
           :: mm.epoch < m.epoch
  }

  ghost predicate AtMostOneInFlightMsg(v:Variables) {
    forall m1, m2 | && m1 in v.network.sentMsgs
                    && m2 in v.network.sentMsgs
                    && InFlight(v, m1)
                    && InFlight(v, m2)
      :: m1 == m2
  }

  ghost predicate NoInFlightMsgsWhenHeld(v:Variables) {
    forall h | v.ValidHostId(h) && v.hosts[h].holdsLock
      :: forall m | m in v.network.sentMsgs :: !InFlight(v, m)
  }

  ghost predicate NoLocksHeldWhenInFlight(v:Variables) {
    forall m | m in v.network.sentMsgs && InFlight(v, m)
      :: forall h | v.ValidHostId(h) :: !v.hosts[h].holdsLock
  }

  ghost predicate LockGrantedByLatestMsg(v:Variables) {
    forall h | v.ValidHostId(h) && v.hosts[h].holdsLock
      :: || (&& h == 0
             && v.hosts[h].epoch == 1
             && v.network.sentMsgs == {})
         || (&& Host.Grant(h, v.hosts[h].epoch) in v.network.sentMsgs
             && forall m | m in v.network.sentMsgs && m != Host.Grant(h, v.hosts[h].epoch)
                  :: m.epoch < v.hosts[h].epoch)
  }

  ghost predicate Inv(v:Variables) {
    // DONE: fill in here (solution: 13 lines)
    && InFlightMsgHighestEpoch(v)
    && AtMostOneInFlightMsg(v)
    && NoInFlightMsgsWhenHeld(v)
    && NoLocksHeldWhenInFlight(v)
    && LockGrantedByLatestMsg(v)
       // END EDIT
  }

  lemma InitImpliesInv(v:Variables)
    requires Init(v)
    ensures Inv(v)
  {
    assert Inv(v);
  }

  lemma InvInductive(v:Variables, v':Variables)
    requires Inv(v) && Next(v, v')
    ensures Inv(v')
  {
    // Develop any necessary proof here.
    // DONE: fill in here (solution: 17 lines)
    var step :| NextStep(v, v', step);
    var h := step.id;
    var msgOps := step.msgOps;
    var hstep :| Host.NextStep(v.hosts[h], v'.hosts[h], msgOps, hstep);
    match hstep {
      case DoGrantStep(recipient) => {
        assert InFlightMsgHighestEpoch(v');
        assert AtMostOneInFlightMsg(v');
        assert NoInFlightMsgsWhenHeld(v');
        assert NoLocksHeldWhenInFlight(v');
        assert LockGrantedByLatestMsg(v');
        assert Inv(v');
      }
      case DoAcceptStep => {
        assert InFlightMsgHighestEpoch(v');
        assert AtMostOneInFlightMsg(v');
        assert NoInFlightMsgsWhenHeld(v');
        assert NoLocksHeldWhenInFlight(v');
        assert LockGrantedByLatestMsg(v');
        assert Inv(v');
      }
    }
    // END EDIT
  }

  lemma InvImpliesSafety(v:Variables)
    requires Inv(v)
    ensures Safety(v)
  {
    assert Safety(v);
  }

  lemma SafetyProof(v:Variables, v':Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {
    // Develop any necessary proof here.
    // DONE: fill in here (solution: 3 lines)
    if Init(v) {
      InitImpliesInv(v);
    }
    if Inv(v) && Next(v, v') {
      InvInductive(v, v');
    }
    if Inv(v) {
      InvImpliesSafety(v);
    }
    // END EDIT
  }
}
