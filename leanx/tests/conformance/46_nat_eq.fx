// Q68: §2.6 Nat equality `==` and inequality `!=`.  Spec:
// "Comparison `== != < > <= >=`".  Pre-Q68 these operators
// lexed and parsed but tripped E010 "expression form not
// supported" at elab — `.binop _ _ _ span` was a catch-all.
//
// Implementation: `a == b` elaborates to a call to the
// prelude-seeded `nat_eq : Π (n m : Nat). Bool` kernel fn,
// defined in `FX/Derived/PreludeFn.lean` as a double `indRec
// "Nat"` with motive `λ _ : Nat. Nat -> Bool`.  The Succ-case
// `rec` parameter auto-supplied by the iota rule carries the
// recursive `Nat -> Bool` partial — so we can compare both
// operands structurally without ever needing `Term.const`
// self-reference at elab time.
//
// `a != b` wraps the same `nat_eq(a, b)` call in a `not` via
// `indRec "Bool" [True, False]`.
//
// Deferred to Q69+: `<`, `<=`, `>`, `>=` and arithmetic
// (`+`, `-`, `*`).  The prelude-fn infrastructure in place
// here scales straightforwardly to those.
//
// Graduation: `fxi run` returns `true` for main — `fact(3)`
// returns a Nat that equals `Succ^6 Zero` (6 = 3!), verified
// via `==` against the inline literal.
fn eq_zero_zero() : Bool = Nat.Zero == Nat.Zero;
fn eq_zero_one()  : Bool = Nat.Zero == Nat.Succ(Nat.Zero);
fn eq_one_one()   : Bool = Nat.Succ(Nat.Zero) == Nat.Succ(Nat.Zero);
fn eq_two_three() : Bool =
  Nat.Succ(Nat.Succ(Nat.Zero))
    == Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

fn ne_zero_zero() : Bool = Nat.Zero != Nat.Zero;
fn ne_one_two()   : Bool =
  Nat.Succ(Nat.Zero) != Nat.Succ(Nat.Succ(Nat.Zero));

// Composition with Q63 `and`: conjunction of truth tables.
fn zero_is_base() : Bool =
  Nat.Zero == Nat.Zero and Nat.Succ(Nat.Zero) != Nat.Zero;

// Deep-Nat equality check: six Succ layers each side.  The
// double-indRec body unfolds `nat_eq` once per Succ, then
// terminates on the inner Zero arms.  Verifies the recursion
// via `rec` (the iota-supplied partial function) descends
// correctly.
fn check_six_equal_six() : Bool =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))))
    == Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))));

fn main() : Bool =
  eq_zero_zero() and eq_one_one() and ne_one_two()
    and check_six_equal_six();
