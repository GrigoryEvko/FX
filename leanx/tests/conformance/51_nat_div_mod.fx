// Q73: §2.6 Nat `/` (integer division) and `%` (modulus) via
// the `nat_div` / `nat_mod` prelude fns.
//
// `nat_div` is built on a fuel-bounded helper: the outer
// `indRec "Nat"` structurally recurses on fuel while the
// inner body performs `nat_sub a b` and recurses on the
// remainder.  An explicit `b == 0 → 0` guard wraps the helper
// so division by zero returns 0 (matching Lean's Nat).
//
// `nat_mod` is derived — `a % b = a - (a/b)*b` — with no new
// recursion: composes `nat_sub`, `nat_mul`, and `nat_div`.
// Consequently `a % 0 = a - 0*0 = a`.

// --- Basic division, classical Peano cases --------------

// 0 / anything = 0 (helper starts with fuel=0, emits Zero)
fn zero_div_one() : Nat = Nat.Zero / Nat.Succ(Nat.Zero);
fn zero_div_three() : Nat =
  Nat.Zero / Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

// 1 / 1 = 1 (one fuel step: a=1 not less than b=1, Succ(rec (0) 1))
fn one_div_one() : Nat = Nat.Succ(Nat.Zero) / Nat.Succ(Nat.Zero);

// 6 / 2 = 3 (three fuel-steps emit Succ before a < b)
fn six_div_two() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))) /
    Nat.Succ(Nat.Succ(Nat.Zero));

// 5 / 3 = 1 (one step emits Succ, then 2 < 3 returns Zero)
fn five_div_three() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))) /
    Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

// 5 / 1 = 5 (five fuel-steps)
fn five_div_one() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))) /
    Nat.Succ(Nat.Zero);

// 7 / 4 = 1 (7-4=3 < 4)
fn seven_div_four() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))))) /
    Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));

// --- Divide-by-zero guard --------------------------------

// a / 0 = 0 via the outer Bool guard.
fn three_div_zero() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) / Nat.Zero;
fn zero_div_zero() : Nat = Nat.Zero / Nat.Zero;

// --- Modulus, classical cases ----------------------------

// 6 % 2 = 0 (6 = 3*2 + 0)
fn six_mod_two() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))) %
    Nat.Succ(Nat.Succ(Nat.Zero));

// 5 % 3 = 2 (5 = 1*3 + 2)
fn five_mod_three() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))) %
    Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

// 7 % 4 = 3 (7 = 1*4 + 3)
fn seven_mod_four() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))))) %
    Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));

// 0 % n = 0 for any n (a/b = 0, so a - 0*b = 0)
fn zero_mod_three() : Nat =
  Nat.Zero % Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

// --- Modulus-by-zero: a % 0 = a --------------------------

// a - (a/0)*0 = a - 0*0 = a — the trivial Euclidean
// decomposition a = 0*q + a holds.
fn three_mod_zero() : Nat =
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) % Nat.Zero;
fn zero_mod_zero() : Nat = Nat.Zero % Nat.Zero;

// --- Composition with Q70 arithmetic and Q68 equality ---

// (6 / 2) * 2 + (6 % 2) == 6 — Euclidean identity.
fn euclidean_six_two() : Bool =
  (Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))) /
     Nat.Succ(Nat.Succ(Nat.Zero))) *
    Nat.Succ(Nat.Succ(Nat.Zero)) +
  (Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))) %
     Nat.Succ(Nat.Succ(Nat.Zero)))
  ==
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))));

// (5 / 3) * 3 + (5 % 3) == 5 — same identity on asymmetric divisor.
fn euclidean_five_three() : Bool =
  (Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))) /
     Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))) *
    Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) +
  (Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))) %
     Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))
  ==
  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))));

fn main() : Nat = six_div_two();
