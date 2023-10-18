// Host protocol
// Define the host state machine here: message type, state machine for executing one
// host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.t.dfy"

module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message =
    Grant(dest:HostId, epoch:nat)

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId)

  datatype Variables = Variables(
    c: Constants,
    holdsLock:bool, epoch:nat
  )

  // You can assume in Init below that the initial constants are set by the
  // DistributedSystem composite state machine, since we assume the host state
  // machine knows the correct total number of hosts and its own ID.

  ghost predicate Init(v:Variables) {
    && v.holdsLock == (v.c.myId == 0)
    && v.epoch == if v.c.myId == 0 then 1 else 0
  }

  ghost predicate DoGrant(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, recipient:HostId)
  {
    && msgOps.recv.None?
    && v.holdsLock == true
    && ValidHostId(v.c.numHosts, recipient)
    && msgOps.send == Some(Grant(recipient, v.epoch + 1))
    && v'.holdsLock == false
    && v'.epoch == v.epoch
  }

  ghost predicate DoAccept(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && msgOps.recv.Some?
    && msgOps.recv.value.dest == v.c.myId
    && msgOps.recv.value.epoch > v.epoch
    && msgOps.send.None?
    && v'.holdsLock == true
    && v'.epoch == msgOps.recv.value.epoch
  }

  // JayNF
  datatype Step =
    | DoGrantStep(recipient: HostId)
    | DoAcceptStep

  ghost predicate NextStep(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    && v'.c == v.c
    && match step
       case DoGrantStep(recipient) => DoGrant(v, v', msgOps, recipient)
       case DoAcceptStep => DoAccept(v, v', msgOps)
  }

  lemma NextStepDeterministic(v: Variables, v'1: Variables, v'2: Variables, msgOps: Network.MessageOps<Message>, step: Step)
    requires NextStep(v, v'1, msgOps, step)
    requires NextStep(v, v'2, msgOps, step)
    ensures v'1 == v'2
  {}

  ghost predicate Next(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(v, v', msgOps, step)
  }
}
