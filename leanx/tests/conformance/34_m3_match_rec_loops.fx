// M3 milestone: pattern matching + recursion + loops.
//
// Composes feature axes exercised only in isolation before:
//
//   * 08_rec_double / 09_rec_length — single-decl self-recursion.
//   * 22_nested_match / 25_match_bind — match structure.
//   * 32_for_loop — for-loop desugaring (Unit body, B10 V1 subset).
//
// Here we build cross-referencing recursive functions that each
// reduce by pattern match on Nat, plus a for-loop helper whose
// body is Unit to stay within the V1 restrictions.  The main
// block threads literal construction, named-arg calls, and a
// recursive result into a single return.
//
// Linearity note: FX's default parameter grade is linear
// (usage = 1, §6.3).  Per the If rule's "worst-case join across
// branches" (§6.2), a variable used at most once in every arm
// has joined grade 1 — acceptable.  Helpers that reference a
// parameter TWICE in a single arm (e.g. the recursive-call +
// arm-body double use in a classic Peano `times`) mark that
// parameter `ref b: Nat` to lift its grade to `Usage.omega`
// (§7.1 shared borrow, duplicable) via Q53's modeToGrade
// refinement.  `plus` below needs no such lift — each arm uses
// `b` once.  `times` requires it on `b`.
//
// Graduation criterion: `fxi test` accepts; `fxi run` evaluates
// main via three nested recursive passes over a 3-deep Nat.
fn plus(a: Nat, b: Nat) : Nat = match a;
  Zero    => b;
  Succ(p) => Nat.Succ(plus(a: p, b: b));
end match;

fn times(a: Nat, ref b: Nat) : Nat = match a;
  Zero    => Nat.Zero;
  Succ(p) => plus(a: b, b: times(a: p, b: b));
end match;

fn triple(n: Nat) : Nat = match n;
  Zero    => Nat.Zero;
  Succ(p) => Nat.Succ(Nat.Succ(Nat.Succ(triple(p))));
end match;

fn pred_or_zero(n: Nat) : Nat = match n;
  Zero    => Nat.Zero;
  Succ(p) => p;
end match;

fn fuel_walk(count: Nat) : Unit = for i in 0..count; Unit.tt end for;

fn main() : Nat
begin fn
  let three        = Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));
  let tripled      = triple(three);
  let decremented  = pred_or_zero(tripled);
  let summed       = plus(a: decremented, b: Nat.Succ(Nat.Zero));
  let multiplier   = Nat.Succ(Nat.Succ(Nat.Zero));
  let product      = times(a: multiplier, b: summed);
  return product;
end fn;
