// Introduction to Dafny

lemma IntegerOrdering()
{
  // An assertion is a **static** check of a boolean expression -- a mathematical truth.
  // This boolean expression is about (mathematical) literal integers.
  // See the red squiggle on the incorrect statement? Replace it with something true.
  // DONE: fill in here (solution: 1 line)
  assert 3 < 5;
  // END EDIT
}

lemma BooleanLogic()
{
  // This boolean expression is about a boolean implication.
  // Fix the error on the following line.
  // DONE: fill in here (solution: 1 line)
  assert true ==> true;
  // END EDIT
}

// ==========================================================
// Functions
// ==========================================================

// A `function` is a mathematical function.
// This one has a domain and range of the integers. Again, `int` is the entire
// type of mathematical integers.

ghost function Double(val:int) : int
{
  // The body of a function is an expression context. No semicolon
  // at the end.
  2 * val
}

// A lemma is like a C++ method or C function (hence the statement context).
// The proof it contains is like a program: a sequence of statements.
// As in C, statements terminate with semicolons and can be grouped into blocks
// with braces.
lemma DoubleIsLikePlus()
{
  assert Double(6) == 6 + 6;
  {
    // DONE: fill in here (solution: 1 line)
    assert Double(-2) == -4;
    // END EDIT
  }
}

// A lemma can take arguments. This is one way to prove a statement about
// *any* value, not just a particular literal.
lemma foo4(val:int)
{
  // DONE: fill in here (solution: 1 line)
  assert Double(val) == val + val;
  // END EDIT
}

// ==========================================================
// Predicates
// ==========================================================

// A common thing you'll want is a function with a boolean result.
ghost function AtLeastTwiceAsBigFunction(a:int, b:int) : bool
{
  a >= 2*b
}

// It's so fantastically common that there's a shorthand for it: `predicate`.
ghost predicate AtLeastTwiceAsBigPredicate(a:int, b:int)
{
  a >= 2*b
}

lemma TheseTwoPredicatesAreEquivalent(x:int, y:int)
{
  assert AtLeastTwiceAsBigFunction(x, y) == AtLeastTwiceAsBigPredicate(x, y);
}

// Add a 'requires' precondition to make this lemma verify.
// Keep it as simple as possible (e.g. avoid named predicates).
lemma FourTimesIsPrettyBig(x:int)
  // DONE: fill in here (solution: 1 line)
  requires x >= 0
  // END EDIT
{
  assert AtLeastTwiceAsBigPredicate(Double(Double(x)), x);
}
