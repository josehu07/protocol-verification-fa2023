// Refinement proof for 2PC
// Show that Two Phase Commit refines the Atomic Commit sate machine spec.

// This proof shouldn't be terribly brutal, since you have a roadmap for the
// relevant invariants from chapter05. You can discard the AC properties (since
// those are proven about the spec in exercise03, and therefore about any state
// machine that refines the spec).

include "exercise01.dfy"

// We have provided you with a copy of our solution to chapter05 exercises
// here. We're building on its state machine, so of course we need its definition.
// The Safety property that chapter 05 considered a "spec" is no longer a spec since
// we're going to use an abstract spec that the protocol refines; however,
// it's still really useful as an invariant, so we'll incorporate that
// property and its proof here as well.
include "ch05exercise03.dfy"

// This Dafny "abstract module" establishes the proof obligations for the
// refinement: later in the file you will be obligated to fill in the function
// and lemma bodies in a module that `refines` this one.
// (This structure is a nice way to separate the statement of the theorem from
// its proof.)
abstract module RefinementTheorem {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened TwoPCInvariantProof
  import AtomicCommit

  ghost function VariablesAbstraction(v: DistributedSystem.Variables) : AtomicCommit.Variables
    requires v.WF()

  ghost predicate Inv(v: DistributedSystem.Variables)

  lemma RefinementInit(v: DistributedSystem.Variables)
    requires DistributedSystem.Init(v)
    ensures Inv(v)
    ensures AtomicCommit.Init(VariablesAbstraction(v))

  lemma RefinementNext(v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    requires DistributedSystem.Next(v, v', event)
    requires Inv(v)
    ensures Inv(v')
    ensures AtomicCommit.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event) ||
            (VariablesAbstraction(v) == VariablesAbstraction(v') && event == NoOpEvent)

}

module RefinementProof refines RefinementTheorem {
  // No imports needed because we inherited them from the abstract module RefinementTheorem
  import opened Obligations
  import opened CoordinatorHost

  // Here are some handy accessor functions for dereferencing the coordinator
  // and the participants out of the sequence in Hosts.
  ghost function CoordinatorVars(v: DistributedSystem.Variables) : CoordinatorHost.Variables
    requires v.WF()
  {
    Last(v.hosts).coordinator
  }

  ghost function ParticipantVars(v: DistributedSystem.Variables, i: HostId) : ParticipantHost.Variables
    requires v.WF()
    requires i < |v.hosts| - 1
  {
    v.hosts[i].participant
  }

  // Here's a handy function to save you some typing.
  ghost function ParticipantCount(v: DistributedSystem.Variables) : nat
    requires v.WF()
  {
    CoordinatorVars(v).c.participantCount
  }

  // The main challenge of setting up a refinement: abstracting from the
  // low-level (protocol) state to the high-level (spec) state.
  ghost function Preferences(v: DistributedSystem.Variables) : seq<Vote>
    requires v.WF()
  {
    // DONE: fill in here (solution: 1 line)
    seq(|v.hosts| - 1,
    i => if 0 <= i < |v.hosts| - 1
      then ParticipantVars(v, i).c.preference
      else Yes // anything
        )
        // END EDIT
  }

  ghost function Decisions(v: DistributedSystem.Variables) : seq<Option<Decision>>
    requires v.WF()
  {
    seq(|v.hosts| - 1,
    i => if 0 <= i < |v.hosts| - 1
      then ParticipantVars(v, i).decision
      else None // anything
        )
  }

  ghost function VariablesAbstraction(v: DistributedSystem.Variables) : AtomicCommit.Variables
  {
    // DONE: fill in here (solution: 3 lines)
    AtomicCommit.Variables(Preferences(v), Decisions(v))
    // END EDIT
  }

  ghost predicate Inv(v: DistributedSystem.Variables)
  {
    // Just point at the invariant from the chapter05 proof (in exercise03).
    // Be certain to fully-qualify the invariant name (mention its module
    // explicitly) to avoid inadvertently referring to the shadowing definition
    // RefinementTheorem.Inv.
    // DONE: fill in here (solution: 1 line)
    TwoPCInvariantProof.Inv(v)
    // END EDIT
  }

  lemma RefinementInit(v: DistributedSystem.Variables)
    // Obligations inherited from RefinementTheorem.RefinementInit
    // requires DistributedSystem.Init(v)
    // ensures Inv(v)
    // ensures AtomicCommit.Init(VariablesAbstraction(v))
  {
  }

  lemma RefinementNext(v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    // Obligations inherited from RefinementTheorem.RefinementNext
    // requires DistributedSystem.Next(v, v', event)
    // requires Inv(v)
    // ensures Inv(v')
    // ensures AtomicCommit.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    // Advice: appeal to the existing proof to get Inv(v')!
    assert Inv(v') by {
      // DONE: fill in here (solution: 1 line)
      InvInductive(v, v', event);
      // END EDIT
    }

    // The "new" part of this proof is to explain which AtomicCommit
    // (spec-level) action happened in response to each 2PC (protocol-level)
    // action. So the general strategy is: use skolemization (var :|) to "learn"
    // which thing happened in the DistributedSystem, split the cases, and
    // assert the right AtomicCommit.NextStep() predicate. Mostly, Dafny needs
    // those asserts because they're witnesses to the `exists` in AtomicCommit.Next().
    // DONE: fill in here (solution: 51 lines)
    var systemStep :| DistributedSystem.NextStep(v, v', event, systemStep);
    var hostId := systemStep.hostId;
    var msgOps := systemStep.msgOps;
    if hostId == |v.hosts| - 1 {
      // coordinator step
      return;
    } else {
      // participant step
      assert ValidParticipantId(v, hostId);
      var participantStep, event :| ParticipantHost.NextStep(ParticipantVars(v, hostId), ParticipantVars(v', hostId), participantStep, msgOps, event);
      match participantStep {
        case VoteStep => {
          // participant hostId took Vote step
          if ParticipantVars(v, hostId).c.preference.Yes? {
            assert VariablesAbstraction(v) == VariablesAbstraction(v');
          } else {
            if ParticipantVars(v, hostId).decision.Some? {
              assert DecisionMsg(Commit) !in v.network.sentMsgs;
              assert ParticipantVars(v, hostId).decision == Some(Abort);
              assert ParticipantVars(v', hostId).decision == Some(Abort);
              assert VariablesAbstraction(v) == VariablesAbstraction(v');
            } else {
              assert event.ParticipantLearnsEvent?;
              assert event.idx == hostId;
              assert ParticipantVars(v', hostId).decision == Some(Abort);
              assert VariablesAbstraction(v).preferences[hostId].No?;
              assert AtomicCommit.UltimateDecision(VariablesAbstraction(v).preferences).Abort?;
              assert AtomicCommit.NextStep(VariablesAbstraction(v), VariablesAbstraction(v'), event, AtomicCommit.ParticipantLearnsStep);
            }
          }
        }
        case LearnDecisionStep => {
          // participant hostId took LearnDecision step
          assert msgOps.recv.Some?;
          assert msgOps.recv.value.DecisionMsg?;
          var msgDecision := msgOps.recv.value.decision;
          if ParticipantVars(v, hostId).decision.Some? {
            if ParticipantVars(v, hostId).decision.value.Commit? {
              assert DecisionMsg(Commit) in v.network.sentMsgs;
              assert msgDecision.Commit?;
            } else if ParticipantVars(v, hostId).c.preference.No? {
              assert msgDecision.Abort?;
            } else {
              assert DecisionMsg(Abort) in v.network.sentMsgs;
              assert msgDecision.Abort?;
            }
            assert VariablesAbstraction(v) == VariablesAbstraction(v');
          } else {
            assert event.ParticipantLearnsEvent?;
            assert event.idx == hostId;
            if msgDecision.Commit? {
              assert CoordinatorVars(v).decision == Some(Commit);
              assert CoordinatorDecisionReflectsPreferences(v);
              assert forall p:HostId | ValidParticipantId(v, p) :: ParticipantVars(v, p).c.preference.Yes?;
              assert forall p:HostId | ValidParticipantId(v, p) :: VariablesAbstraction(v).preferences[p].Yes?;
              assert AtomicCommit.UltimateDecision(VariablesAbstraction(v).preferences).Commit?;
            } else {
              assert CoordinatorVars(v).decision == Some(Abort);
              assert CoordinatorDecisionReflectsPreferences(v);
              assert |v.hosts| > 1;
              var p:HostId :| ValidParticipantId(v, p) && ParticipantVars(v, p).c.preference.No?;
              assert VariablesAbstraction(v).preferences[p].No?;
              assert AtomicCommit.UltimateDecision(VariablesAbstraction(v).preferences).Abort?;
            }
            assert AtomicCommit.UltimateDecision(VariablesAbstraction(v).preferences) == msgDecision;
            assert AtomicCommit.NextStep(VariablesAbstraction(v), VariablesAbstraction(v'), event, AtomicCommit.ParticipantLearnsStep);
          }
        }
      }
    }
    // END EDIT
  }
}
