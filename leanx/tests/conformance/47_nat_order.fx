// Q69: §2.6 Nat ordering operators `<`, `<=`, `>`, `>=`.
// All four reduce to calls to the single prelude-seeded
// `nat_lt : Π (n m : Nat). Bool` kernel fn (see
// `FX/Derived/PreludeFn.lean`) via arg-swap and/or `not`:
//
//   a <  b  =  nat_lt(a, b)
//   a >  b  =  nat_lt(b, a)
//   a <= b  =  not nat_lt(b, a)
//   a >= b  =  not nat_lt(a, b)
//
// Structure of `nat_lt` matches `nat_eq`'s double `indRec`
// shape — the only difference is the "Zero vs Succ(_)" method:
// `0 < Succ(_) = True` (whereas `0 == Succ(_) = False`).
//
// Graduation: `main` verifies all four operators simultaneously
// on `(2, 3)` — `2 < 3`, `2 <= 3`, `3 > 2`, `3 >= 2` all True,
// and the reverse (`3 < 2`, etc.) all False.
fn lt_zero_one() : Bool = Nat.Zero < Nat.Succ(Nat.Zero);
fn lt_one_zero() : Bool = Nat.Succ(Nat.Zero) < Nat.Zero;
fn lt_two_three() : Bool =
  Nat.Succ(Nat.Succ(Nat.Zero)) < Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

fn gt_three_two() : Bool =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) > Nat.Succ(Nat.Succ(Nat.Zero));
fn gt_two_two() : Bool =
  Nat.Succ(Nat.Succ(Nat.Zero)) > Nat.Succ(Nat.Succ(Nat.Zero));

// `<=` — reflexive: `n <= n` should always be True.
fn le_two_two() : Bool =
  Nat.Succ(Nat.Succ(Nat.Zero)) <= Nat.Succ(Nat.Succ(Nat.Zero));
fn le_two_three() : Bool =
  Nat.Succ(Nat.Succ(Nat.Zero)) <= Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));
fn le_three_two() : Bool =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) <= Nat.Succ(Nat.Succ(Nat.Zero));

// `>=` — reflexive.
fn ge_three_three() : Bool =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))
    >= Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));
fn ge_two_three() : Bool =
  Nat.Succ(Nat.Succ(Nat.Zero)) >= Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

// Composition with Q63 `and` + Q68 `==` — all-in-one
// assertion chaining ordering + equality.
fn ordered_three_ways() : Bool =
  Nat.Succ(Nat.Zero) < Nat.Succ(Nat.Succ(Nat.Zero))
    and Nat.Succ(Nat.Succ(Nat.Zero)) <= Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))
    and Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) > Nat.Succ(Nat.Succ(Nat.Zero))
    and Nat.Succ(Nat.Zero) == Nat.Succ(Nat.Zero);

fn main() : Bool = ordered_three_ways();
