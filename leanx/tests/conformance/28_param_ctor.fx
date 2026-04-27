// Parameterized ADT with type-arg inference at ctor use site
// (B9 second-phase landing).  Exercises:
//
//   * `type option<a: type>` declaration → IndSpec with
//     params = [Type<0>]
//   * Nullary ctor `None` with expected type `option(Nat)`:
//     elaborator reads typeArgs off the expected and emits
//     `Term.ctor "option" 0 [Nat] []` so the kernel's T111
//     arity check passes.
//   * Arg-bearing ctor `Some(Nat.Zero)` with expected type
//     `option(Nat)`: same mechanism threads [Nat] through
//     `Term.ctor "option" 1 [Nat] [Nat.Zero]`.
//   * Type application at signature site `option(Nat)` →
//     `Term.ind "option" [Nat]` via the .app branch.
//
// Match on parameterized scrutinee is NOT yet supported
// (AdtTests pins E010 for that path) — this test avoids
// the matcher and just exercises ctor construction with
// type-arg inference from an ascribed fn return type.
type option<a: type>
  None;
  Some(a);
end type;

fn empty_slot() : option(Nat) = None;
fn filled_slot() : option(Nat) = Some(Nat.Succ(Nat.Succ(Nat.Zero)));
fn main() : Nat = Nat.Succ(Nat.Zero);
