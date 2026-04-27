// Q56: let-binder grade routes through `gradeForParam`.
//
// Pre-Q56 this program fired M001 on `double_via_let` because
// the `let bound : Nat = n` desugared to a lam with hardcoded
// `Grade.default` (usage = 1), so referencing `bound` twice in
// the return expression joined to usage = ω — a linearity
// violation at the exit check.
//
// Post-Q56 the let's synthesized lam picks up the same
// `gradeForParam` routing used for fn parameters: because Nat
// is @[copy] at the prelude (Q55), the binder's grade becomes
// `Grade.shared` and multi-use is admitted.  This matters for
// the agentic-LLM target: a user can bind an intermediate
// value via `let` and reference it multiple times without
// worrying about grade fallout.
//
// Graduation criterion: `fxi run` returns plus(3, 3) = 6.
fn plus(a: Nat, b: Nat) : Nat = match a;
  Zero    => b;
  Succ(p) => Nat.Succ(plus(a: p, b: b));
end match;

fn double_via_let(n: Nat) : Nat
begin fn
  let bound : Nat = n;
  return plus(a: bound, b: bound);
end fn;

fn main() : Nat = double_via_let(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));
