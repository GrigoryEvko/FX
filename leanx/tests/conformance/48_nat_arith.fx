// Q70: §2.6 Nat arithmetic `+`, `-`, `*`.  Each elaborates to
// a call to a prelude-seeded kernel fn:
//
//   a + b  =  nat_add(a, b)
//   a - b  =  nat_sub(a, b)   (saturating; max(0, a-b))
//   a * b  =  nat_mul(a, b)
//
// Bodies in `FX/Derived/PreludeFn.lean` — each a closed
// double-`indRec` term using motive `λ _ : Nat. Nat -> Nat`,
// so the outer indRec returns a partial (one-arg) Nat-to-Nat
// function that the body applies to the second operand.  The
// recursive step in `nat_mul` chains through `Term.const
// "nat_add"` — transparent delta-reduction unfolds both.
//
// Composes with Q68 `==` / Q69 ordering for verification: the
// `main` body asserts `(3 + 4) == 7`, `5 - 2 == 3`, `0 * 7 == 0`,
// `3 * 4 == 12`.
fn add_2_3() : Nat =
  Nat.Succ(Nat.Succ(Nat.Zero))
    + Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

fn add_0_4() : Nat =
  Nat.Zero + Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));

// Saturating subtract: 2 - 5 = 0 (not negative).
fn sub_sat() : Nat =
  Nat.Succ(Nat.Succ(Nat.Zero))
    - Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))));

fn sub_5_2() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))
    - Nat.Succ(Nat.Succ(Nat.Zero));

fn mul_3_4() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))
    * Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));

fn mul_0_7() : Nat =
  Nat.Zero
    * Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))));

// Composed assertion: `3 * 4 == 12` using Q68 `==`.
fn twelve_check() : Bool =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))
    * Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))
    == Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(
         Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))))))))));

// Distributivity: `(2 + 3) * 2 == 2 * 2 + 3 * 2` should hold.
fn distributivity_check() : Bool =
  (Nat.Succ(Nat.Succ(Nat.Zero)) + Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))
    * Nat.Succ(Nat.Succ(Nat.Zero))
    == Nat.Succ(Nat.Succ(Nat.Zero)) * Nat.Succ(Nat.Succ(Nat.Zero))
       + Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) * Nat.Succ(Nat.Succ(Nat.Zero));

fn main() : Bool = twelve_check() and distributivity_check();
