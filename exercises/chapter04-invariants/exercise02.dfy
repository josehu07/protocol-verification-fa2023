// Single-Server Lock Service Proof

// We provide a correct spec for the lock server here, but leave you
// to define the Safety property to be proven.
// You are welcome to prove correct your own model from chapter03,
// but note that may be too hard or too easy if your spec is broken.

// Copy your solution for chapter03/exercise03 into the current directory with
// this name:
include "ch03exercise03.dfy"

// DONE: fill in here (solution: 11 lines)
ghost predicate Inv(v:Variables) {
  && v.WellFormed()
  && (v.server.Unlocked? ==> forall c | v.ValidIdx(c) :: v.clients[c].Released?)
  && (v.server.Client? ==> && v.ValidIdx(v.server.id)
                           && v.clients[v.server.id].Acquired?
                           && forall c | v.ValidIdx(c) && c != v.server.id
                                :: v.clients[c].Released?)
}
// END EDIT

// lemma InitHolds(v:Variables)
//   requires Init(v)
//   ensures Inv(v)
// {}

// lemma InductiveOnAcquire(v:Variables, v':Variables, id:int)
//   requires Inv(v)
//   requires v.ValidIdx(id)
//   requires NextStep(v, v', AcquireStep(id))
//   ensures Inv(v')
// {}

// lemma InductiveOnRelease(v:Variables, v':Variables, id:int)
//   requires Inv(v)
//   requires v.ValidIdx(id)
//   requires NextStep(v, v', ReleaseStep(id))
//   ensures Inv(v')
// {}

// lemma ImpliesSafety(v:Variables)
//   requires Inv(v)
//   ensures Safety(v)
// {}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(v:Variables, v':Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  // DONE: fill in here (solution: 10 lines)
  // Comment: It seems that with the above Inv, Dafny is able to prove
  //          this lemma by itself?
  // END EDIT
}
