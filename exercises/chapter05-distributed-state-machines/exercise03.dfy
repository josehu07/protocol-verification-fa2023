// Two Phase Commit Safety Proof
// Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  ghost predicate DecisionMsgsAgreeWithDecision(v: Variables)
    requires v.WF()
  {
    // DONE: fill in here (solution: 5 lines)
    && (forall p | ValidParticipantId(v, p) ::
          ParticipantVars(v, p).decision == Some(Commit) ==> Decide(Commit) in v.network.sentMsgs)
    && (CoordinatorVars(v).decision == Some(Abort)) == (Decide(Abort) in v.network.sentMsgs)
    && (CoordinatorVars(v).decision == Some(Commit)) == (Decide(Commit) in v.network.sentMsgs)
       // END EDIT
  }

  // We use this block of code to define additional invariants. We recommend you
  // define predicates for the individual parts of your invariant, to make
  // debugging easier.
  // DONE: fill in here (solution: 20 lines)
  ghost predicate DecisionMsgsReflectVotes(v: Variables)
    requires v.WF()
  {
    && (Decide(Abort) in v.network.sentMsgs ==> exists p:nat | ValidParticipantId(v, p) :: CoordinatorVars(v).votes[p] == Some(No))
    && (Decide(Commit) in v.network.sentMsgs ==> forall p:nat | ValidParticipantId(v, p) :: CoordinatorVars(v).votes[p] == Some(Yes))
  }

  ghost predicate VotesMadeByVoteMsgs(v: Variables)
    requires v.WF()
  {
    forall p:nat, vote:Vote | ValidParticipantId(v, p)::
      CoordinatorVars(v).votes[p] == Some(vote) ==> Vote(p, vote) in v.network.sentMsgs
  }

  ghost predicate VoteMsgsAgreeWithPreferences(v: Variables)
    requires v.WF()
  {
    forall p:nat, vote:Vote | ValidParticipantId(v, p) ::
      Vote(p, vote) in v.network.sentMsgs ==> ParticipantVars(v, p).c.preference == vote
  }
  // END EDIT


  ghost predicate Inv(v: Variables)
  {
    && v.WF()
       // DONE: fill in here (solution: 2 lines)
       // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(v)
       // ...but you'll need more.
    && DecisionMsgsReflectVotes(v)
    && VotesMadeByVoteMsgs(v)
    && VoteMsgsAgreeWithPreferences(v)
    && Safety(v)
  }

  lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    // DONE: fill in here (solution: 3 lines)
    assert DecisionMsgsAgreeWithDecision(v);
    assert DecisionMsgsReflectVotes(v);
    assert VotesMadeByVoteMsgs(v);
    assert VoteMsgsAgreeWithPreferences(v);
    // END EDIT
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
  {
    //(not all of the below but much of it)
    // DONE: fill in here (solution: 59 lines)
    var step :| NextStep(v, v', step);
    if step.hostId == |v.hosts|-1 {
      // coordinator step
      var cstep :| CoordinatorHost.NextStep(CoordinatorVars(v), CoordinatorVars(v'), cstep, step.msgOps);
      match cstep {
        case RequestVotesStep => {
          assert CoordinatorVars(v).decision.None?;
          assert CoordinatorVars(v').decision.None?;
          forall p | ValidParticipantId(v, p)
            ensures ParticipantVars(v, p).decision == ParticipantVars(v', p).decision
          {}
          assert DecisionMsgsAgreeWithDecision(v');
          assert DecisionMsgsReflectVotes(v');
          assert VotesMadeByVoteMsgs(v');
          assert VoteMsgsAgreeWithPreferences(v');
          assert Inv(v');
        }
        case ReceiveVoteStep => {
          assert CoordinatorVars(v).decision.None?;
          assert CoordinatorVars(v').decision.None?;
          forall p | ValidParticipantId(v, p)
            ensures ParticipantVars(v, p).decision == ParticipantVars(v', p).decision
          {}
          assert DecisionMsgsAgreeWithDecision(v');
          assert DecisionMsgsReflectVotes(v');
          assert VotesMadeByVoteMsgs(v');
          assert VoteMsgsAgreeWithPreferences(v');
          assert Inv(v');
        }
        case MakeDecisionStep => {
          assert CoordinatorVars(v).decision.None?;
          assert CoordinatorVars(v').decision.Some?;
          if CoordinatorVars(v').decision.value == Commit {
            assert Decide(Commit) in v'.network.sentMsgs;
          } else {
            assert Decide(Abort) in v'.network.sentMsgs;
          }
          forall p | ValidParticipantId(v, p)
            ensures ParticipantVars(v, p).decision == ParticipantVars(v', p).decision
          {}
          assert DecisionMsgsAgreeWithDecision(v');
          assert DecisionMsgsReflectVotes(v');
          assert VotesMadeByVoteMsgs(v');
          assert VoteMsgsAgreeWithPreferences(v');
          assert Inv(v');
        }
      }
    } else {
      // participant step
      var pstep :| ParticipantHost.NextStep(ParticipantVars(v, step.hostId), ParticipantVars(v', step.hostId), pstep, step.msgOps);
      match pstep {
        case ReplyVoteStep => {
          assert ParticipantVars(v, step.hostId).decision.None?;
          if ParticipantVars(v', step.hostId).decision == Some(Abort) {
            assert ParticipantVars(v', step.hostId).c.preference.No?;
          } else {
            assert ParticipantVars(v', step.hostId).decision.None?;
          }
          forall p | ValidParticipantId(v', p) && p != step.hostId
            ensures ParticipantVars(v, p).decision == ParticipantVars(v', p).decision
          {}
          assert DecisionMsgsAgreeWithDecision(v');
          assert DecisionMsgsReflectVotes(v');
          assert VotesMadeByVoteMsgs(v');
          assert VoteMsgsAgreeWithPreferences(v');
          assert Inv(v');
        }
        case ReceiveDecisionStep => {
          assert ParticipantVars(v, step.hostId).c.preference.Yes?;
          assert ParticipantVars(v, step.hostId).decision.None?;
          assert ParticipantVars(v', step.hostId).decision.Some?;
          if ParticipantVars(v', step.hostId).decision.value == Commit {
            assert Decide(Commit) in v'.network.sentMsgs;
          } else {
            assert Decide(Abort) in v'.network.sentMsgs;
          }
          forall p | ValidParticipantId(v', p) && p != step.hostId
            ensures ParticipantVars(v, p).decision == ParticipantVars(v', p).decision
          {}
          assert DecisionMsgsAgreeWithDecision(v');
          assert DecisionMsgsReflectVotes(v');
          assert VotesMadeByVoteMsgs(v');
          assert VoteMsgsAgreeWithPreferences(v');
          assert Inv(v');
        }
      }
    }
    // END EDIT
  }

  lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
