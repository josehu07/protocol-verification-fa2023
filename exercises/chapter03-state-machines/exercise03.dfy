
// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

// DONE: fill in here (solution: 13 lines)
datatype Variables = Variables(numClients:nat,
                               serverHolds:bool,
                               serverFlags:seq<bool>,
                               clientHolds:seq<bool>)
{
  ghost predicate WellFormed() {
    |serverFlags| == |clientHolds| == numClients
  }
}
// END EDIT

ghost predicate Init(v:Variables) {
  && v.WellFormed()
     // DONE: fill in here (solution: 3 lines)
  && v.serverHolds == true
  && v.serverFlags == seq(v.numClients, i => false)
  && v.clientHolds == seq(v.numClients, i => false)
     // END EDIT
}

// DONE: fill in here (solution: 23 lines)
ghost predicate AcquireLock(v:Variables, v':Variables, clientIndex:nat) {
  && v.WellFormed()
  && clientIndex < v.numClients
  && !v.clientHolds[clientIndex]
  && v.serverHolds
  && v' == Variables(v.numClients,
                     false,
                     v.serverFlags[clientIndex := true],
                     v.clientHolds[clientIndex := true])
}

ghost predicate ReleaseLock(v:Variables, v':Variables, clientIndex:nat) {
  && v.WellFormed()
  && clientIndex < v.numClients
  && v.clientHolds[clientIndex]
  && v.serverFlags[clientIndex]
  && v' == Variables(v.numClients,
                     true,
                     v.serverFlags[clientIndex := false],
                     v.clientHolds[clientIndex := false])
}
// END EDIT

// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
    // DONE: fill in here (solution: 2 lines)
  | AcquireLockStep(idx:nat)
  | ReleaseLockStep(idx:nat)
    // END EDIT

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // DONE: fill in here (solution: 2 lines)
  case AcquireLockStep(idx) => AcquireLock(v, v', idx)
  case ReleaseLockStep(idx) => ReleaseLock(v, v', idx)
  // END EDIT
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(v:Variables) {
  // DONE: fill in here (solution: 10 lines)
  && v.WellFormed()
  && (forall c1:nat, c2:nat | c1 < v.numClients && c2 < v.numClients ::
        v.clientHolds[c1] && v.clientHolds[c2] ==> c1 == c2)
  && (forall i:nat | i < v.numClients :: v.serverFlags[i] == v.clientHolds[i])
     // END EDIT
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  // DONE: fill in here (solution: 1 line)
  clientIndex < v.numClients && v.clientHolds[clientIndex]
  // END EDIT
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (behavior:seq<Variables>)
  requires clientA == 2
  requires clientB == 0
  ensures 2 <= |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i]) // Behavior always satisfies the Safety predicate
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling ClientHoldsLock
  ensures ClientHoldsLock(behavior[1], clientA) // first clientA acquires lock
  ensures ClientHoldsLock(behavior[|behavior|-1], clientB) // eventually clientB acquires lock
{
  // DONE: fill in here (solution: 9 lines)
  var state0 := Variables(3, true, seq(3, i => false), seq(3, i => false));
  var state1 := Variables(3, false, seq(3, i => i == clientA), seq(3, i => i == clientA));
  var state2 := Variables(3, true, seq(3, i => false), seq(3, i => false));
  var state3 := Variables(3, false, seq(3, i => i == clientB), seq(3, i => i == clientB));
  behavior := [state0, state1, state2, state3];
  assert NextStep(state0, state1, AcquireLockStep(clientA));
  assert NextStep(state1, state2, ReleaseLockStep(clientA));
  assert NextStep(state2, state3, AcquireLockStep(clientB));
  // END EDIT
}
