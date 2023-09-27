
// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table.
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step).
//
// (Nota bene: The dining philosophers problem is used to illustrate deadlocks
// and deadlock-freedom. We're not doing any of that here, just using the
// example to teach you to set up a state machine model.)

// Define all the relevant state in this datatype.
// DONE: fill in here (solution: 8 lines)
datatype Variables = Variables(tableSize:nat,
                               leftHands: seq<bool>,
                               rightHands: seq<bool>)
{
  ghost predicate WellFormed() {
    && 1 < tableSize
    && |leftHands| == |rightHands| == tableSize
    && forall i:nat | i < tableSize :: !(rightHands[i] && leftHands[rightIndex(tableSize, i)])
  }
}
// END EDIT

ghost predicate Init(v:Variables) {
  // DONE: fill in here (solution: 3 lines)
  && v.tableSize > 1
  && v.leftHands == seq(v.tableSize, i => false)
  && v.rightHands == seq(v.tableSize, i => false)
     // END EDIT
}

// DONE: fill in here (solution: 11 lines)
ghost function rightIndex(tableSize:nat, idx:nat) : (res:nat)
  requires tableSize > 1
  requires 0 <= idx < tableSize
{
  (idx + 1) % tableSize
}

ghost function leftIndex(tableSize:nat, idx:nat) : (res:nat)
  requires tableSize > 1
  requires 0 <= idx < tableSize
  ensures (res + 1) % tableSize == idx
{
  if idx == 0 then tableSize - 1 else idx - 1
}
// END EDIT

// Philosopher with index philosopherIndex acquires left chopstick
ghost predicate AcquireLeft(v:Variables, v':Variables, philosopherIndex:nat) {
  // DONE: fill in here (solution: 5 lines)
  && v.WellFormed()
  && philosopherIndex < v.tableSize
  && !v.leftHands[philosopherIndex]
  && !v.rightHands[leftIndex(v.tableSize, philosopherIndex)]
  && v' == Variables(v.tableSize,
                     v.leftHands[philosopherIndex := true],
                     v.rightHands)
     // END EDIT
}

// Philosopher with index philosopherIndex acquires right chopstick
ghost predicate AcquireRight(v:Variables, v':Variables, philosopherIndex:nat) {
  // DONE: fill in here (solution: 5 lines)
  && v.WellFormed()
  && philosopherIndex < v.tableSize
  && !v.rightHands[philosopherIndex]
  && !v.leftHands[rightIndex(v.tableSize, philosopherIndex)]
  && v' == Variables(v.tableSize,
                     v.leftHands,
                     v.rightHands[philosopherIndex := true])
     // END EDIT
}

// Philosopher with index philosopherIndex releases both chopsticks
ghost predicate ReleaseBoth(v:Variables, v':Variables, philosopherIndex:nat) {
  // DONE: fill in here (solution: 5 lines)
  && v.WellFormed()
  && philosopherIndex < v.tableSize
  && v.leftHands[philosopherIndex]
  && v.rightHands[philosopherIndex]
  && v' == Variables(v.tableSize,
                     v.leftHands[philosopherIndex := false],
                     v.rightHands[philosopherIndex := false])
     // END EDIT
}

datatype Step =
    // DONE: fill in here (solution: 3 lines)
  | AcquireLeftStep(idx:nat)
  | AcquireRightStep(idx:nat)
  | ReleaseBothStep(idx:nat)
    // END EDIT

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // DONE: fill in here (solution: 3 lines)
  case AcquireLeftStep(idx) => AcquireLeft(v, v', idx)
  case AcquireRightStep(idx) => AcquireRight(v, v', idx)
  case ReleaseBothStep(idx) => ReleaseBoth(v, v', idx)
  // END EDIT
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// This predicate should be true if and only if no philosopher holds a
// chopstick.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate NoSticksAcquired(v: Variables)
  requires v.WellFormed()
{
  // DONE: fill in here (solution: 8 lines)
  forall i:nat | i < v.tableSize ::
    && !v.leftHands[i]
    && !v.rightHands[i]
       // END EDIT
}

// Change this predicate to be true if and only if philosopher
// `philosopherIndex` holds both of their chopsticks.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate BothSticksAcquired(v: Variables, philosopherIndex: nat)
  requires philosopherIndex < v.tableSize
  requires v.WellFormed()
{
  // DONE: fill in here (solution: 6 lines)
  v.leftHands[philosopherIndex] && v.rightHands[philosopherIndex]
  // END EDIT
}

// Show that, in the Init state, no philosopher has chopsticks.
lemma InitProperty(v: Variables, philosopherIndex:nat)
  requires Init(v)
  ensures NoSticksAcquired(v)
{
  // DONE: fill in here (solution: 0 lines)
  // END EDIT
}


// Show a behavior that evolves from the init state to one where a philosopher
// has completed acquiring both chopsticks.
lemma PseudoLiveness(philosopherIndex:nat) returns (behavior:seq<Variables>)
  requires philosopherIndex == 1
  ensures 0 < |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: behavior[i].tableSize == 3
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling BothSticksAcquired
  ensures BothSticksAcquired(behavior[|behavior|-1], philosopherIndex)  // Behavior ultimately achieves acquisition for philosopherIndex
{
  // DONE: fill in here (solution: 6 lines)
  var state0 := Variables(3, seq(3, i => false), seq(3, i => false));
  var state1 := Variables(3, seq(3, i => i == philosopherIndex), seq(3, i => false));
  var state2 := Variables(3, seq(3, i => i == philosopherIndex), seq(3, i => i == philosopherIndex));
  behavior := [state0, state1, state2];
  assert NextStep(state0, state1, AcquireLeftStep(philosopherIndex));
  assert NextStep(state1, state2, AcquireRightStep(philosopherIndex));
  // END EDIT
}
