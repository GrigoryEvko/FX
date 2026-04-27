// Destructuring lambda via expected-type threading (B11 landing).
// Exercises: callee declares `f: Pair(Nat, Nat) -> Nat`; the
// positional-arg branch threads that as expected into the lam
// elab; the lam's destructure pattern resolves against the
// expected's `Term.ind "Pair" [...]` shape.
type Pair<a: type, b: type>
  MkPair(a, b);
end type;

fn on_pair(f: Pair(Nat, Nat) -> Nat, p: Pair(Nat, Nat)) : Nat = f(p);

fn main() : Nat = on_pair(
  f: fn((x, _y)) => x,
  p: MkPair(Nat.Succ(Nat.Succ(Nat.Zero)), Nat.Zero),
);
