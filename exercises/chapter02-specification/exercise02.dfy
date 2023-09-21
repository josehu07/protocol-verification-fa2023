// Specifying and implementing IsPrime

/*{*//*}
*/
ghost predicate IsPrimeSpec(candidate:nat)
{
  // DONE: fill in here (solution: 3 lines)
  && candidate > 1
  && forall n | 1 < n < candidate :: candidate % n != 0
                                     // END EDIT
}

// illustrate IsPrimeSpec on a few examples (note that the verifier is able to
// check these only with some help to find divisors for non-prime numbers)
lemma ConstantObligations()
  ensures !IsPrimeSpec(0)
  ensures !IsPrimeSpec(1)
  ensures IsPrimeSpec(2)
  ensures IsPrimeSpec(3)
  ensures !IsPrimeSpec(4)
  ensures !IsPrimeSpec(6)
  ensures IsPrimeSpec(7)
  ensures !IsPrimeSpec(9)
{
  // DONE: fill in here (solution: 3 lines)
  assert 4 % 2 == 0;
  assert 6 % 2 == 0;
  assert 9 % 3 == 0;
  // END EDIT
}

lemma CompositeIsntPrime(p: nat)
  requires 1 < p
  ensures !IsPrimeSpec(p*66)
{
  // DONE: fill in here (solution: 1 line)
  assert p*66 % 66 == 0;
  // END EDIT
}


// ================================================
// Implementing a check for IsPrime
// ================================================

// Let's try "implementing" (with a recursive function) a check for
// primeness.

// A recursive implementation of IsPrime. The function HasDivisorBelow should
// check if n is divisible by something between 1 and limit (including limit,
// not including 1).
function
  HasDivisorBelow(n:nat, limit:nat): bool
  requires limit >= 1
{
  // DONE: fill in here (solution: 3 lines)
  if limit == 1 then false else
  if n % limit == 0 then true
  else HasDivisorBelow(n, limit-1)
       // END EDIT
}

function IsPrime(n: nat): bool {
  if n <= 1 then false else
  !HasDivisorBelow(n, n-1)
}

// You'll now prove IsPrime(n) == IsPrimeSpec(n). This will require a helper
// lemma to deal with the recursion.

// An intermediate spec for what HasDivisorBelow returns. The solution is
// expressed using an exists; you may find it more natural to write a forall.
//
// We add {:induction false} to avoid Dafny doing some extra work
// automatically. This forces you to write a proof which is more instructive in
// this case (and is needed in more complex examples).
lemma {:induction false} HasDivisorBelow_ok(n: nat, limit: nat)
  requires 1 <= limit
  // DONE: fill in here (solution: 3 lines)
  decreases limit
  ensures HasDivisorBelow(n, limit) <==>
          exists d | 1 < d <= limit :: n % d == 0
  // END EDIT
{
  // DONE: fill in here (solution: 5 lines)
  if limit > 1 {
    HasDivisorBelow_ok(n, limit-1);
    assert HasDivisorBelow(n, limit) == if n % limit == 0 then true
                                        else HasDivisorBelow(n, limit-1);
  }
  // END EDIT
}

lemma IsPrime_ok(n: nat)
  ensures IsPrime(n) == IsPrimeSpec(n)
{
  // DONE: fill in here (solution: 4 lines)
  // This proof should work if your postcondition for HasDivisorBelow_ok is
  // correct, but you can change it if needed.
  if n <= 2 {
    return;
  }
  HasDivisorBelow_ok(n, n-1);
  // END EDIT
}
