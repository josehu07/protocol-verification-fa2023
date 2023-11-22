include "UtilitiesLibrary.t.dfy"
include "IMapHelpers.t.dfy"
include "Types.t.dfy"
include "MessageType.v.dfy"
include "Network.t.dfy"

// You'll need protocol steps for Get and Put that respond to requests if
// they're hosted locally, much like in the atomic version of this protocol
// (AtomicKV, seen in the chapter06 demos). These need to set the event to
// GetEvent and PutEvent appropriately: otherwise, you're claiming the key-value
// store implementation always does nothing and never returns results to the
// client. (Such an implementation is technically safe but totally useless and
// not in the spirit of the assignment; to be clear, it's not a real solution.)
//
// In addition, you should capture the idea that keys "live" on different hosts
// *and can move around* from host to host. So, in addition to implementing
// client-visible actions as described in AtomicKV, each host should have a way
// to send part of its state to another host, and to receive the corresponding
// message from another sender. (The messages can move a batch of key-value
// pairs, or a single pair at a time; neither is particularly harder than the
// other.)
//
// Obviously, the hosts must be aware of which fraction of the keyspace they
// own at any given time, so that a host doesn't try to service a Get or Put
// request when the "real state" is off at some other host right now.
//

module Host {
  import opened UtilitiesLibrary
  import opened IMapHelpers
  import opened Types
  import opened MessageType
  import Network

  type HostId = Network.HostId

  datatype Variables = Variables(myId: HostId, m: imap<int, int>)
  {
    ghost predicate GroupWF(assignedId: HostId) {
      && this.myId == assignedId
    }
  }

  ghost predicate Init(v: Variables) {
    // hint: look at IMapHelpers for some tools to write this
    // DONE: fill in here (solution: 2 lines)
    && if v.myId == 0 then v.m == ZeroMap() else v.m == EmptyMap()
    // END EDIT
  }

  datatype Step =
      // DONE: fill in here (solution: 4 lines)
    | ServeGetStep
    | ServePutStep
    | SendMigrateStep
    | RecvMigrateStep
      // END EDIT

  // Write a predicate for each step here.
  // DONE: fill in here (solution: 53 lines)
  ghost predicate ServeGet(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event) {
    && msgOps.recv.None?
    && event.GetEvent?
    && event.key in v.m
    && msgOps.send.None?
    && v' == v
    && event.value == v.m[event.key]
  }

  ghost predicate ServePut(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event) {
    && msgOps.recv.None?
    && event.PutEvent?
    && event.key in v.m
    && msgOps.send.None?
    && v' == v.(m := v.m[event.key := event.value])
  }

  ghost predicate SendMigrate(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event) {
    && msgOps.recv.None?
    && event.NoOpEvent?
    && msgOps.send.Some?
    && var chunk := msgOps.send.value.chunk;
    && chunk.Keys <= v.m.Keys
    && v' == v.(m := MapRemove(v.m, chunk.Keys))
  }

  ghost predicate RecvMigrate(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event) {
    && msgOps.recv.Some?
    && var chunk := msgOps.recv.value.chunk;
    && event.NoOpEvent?
    && msgOps.send.None?
    && v' == v.(m := IMapUnionPreferLeft(chunk, v.m))
  }
  // END EDIT

  ghost predicate NextStep(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event, step: Step)
  {
    match step {
      // boilerplate that dispatches to each of your step's predicates
      // DONE: fill in here (solution: 4 lines)
      case ServePutStep => ServePut(v, v', msgOps, event)
      case ServeGetStep => ServeGet(v, v', msgOps, event)
      case SendMigrateStep => SendMigrate(v, v', msgOps, event)
      case RecvMigrateStep => RecvMigrate(v, v', msgOps, event)
      // END EDIT
    }
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
  {
    exists step: Step :: NextStep(v, v', msgOps, event, step)
  }
}
