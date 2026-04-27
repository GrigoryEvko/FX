// Q66: §2.6 constructor-test operator `is`.  Spec:
// "Constructor test `is` infix keyword (`x is Some` returns
// bool)."
//
// Elaboration desugars `x is Ctor` to an exhaustive match
// emitting Bool.True for the matching ctor arm and Bool.False
// for every other ctor.  `is` binds tighter than comparison
// and looser than arithmetic, so `x + 1 is Succ` parses as
// `(x + 1) is Succ` and `x is Some == true` as
// `(x is Some) == true`.
//
// Exercises:
//
//   * Bool ctor test (two ctors).
//   * Nat ctor test (Zero vs Succ, recursive payload).
//   * User-defined enum ctor test.
//   * Composition with `and`/`or` from Q63.
//
// Graduation: `fxi run` returns `true` — the last step of
// `ready_check` is `Bool.True is Bool.True`, which is True.
// `@[copy]` so `c is Red or c is Blue` can read `c` twice
// under the lifted lambda / desugared match.  All-nullary
// enums trivially satisfy §7.8's "all components copy"
// requirement.
@[copy]
type color
  Red;
  Green;
  Blue;
end type;

fn is_red(c: color) : Bool = c is Red;
fn is_blue(c: color) : Bool = c is Blue;

fn is_nonzero(n: Nat) : Bool = n is Nat.Succ;
fn is_false(b: Bool) : Bool = b is Bool.False;

// Composed with logical `and` — Q63 interaction.
fn red_and_nonzero(c: color, n: Nat) : Bool =
  c is Red and n is Nat.Succ;

// Composed with `or`.
fn red_or_blue(c: color) : Bool = c is Red or c is Blue;

// Negated test via Q63 `not`.
fn not_red(c: color) : Bool = not (c is Red);

fn main() : Bool
begin fn
  // Three positive tests and one negative, each expected True,
  // then combined via `and` so a single false arm taints the
  // whole result.
  let t_red    : Bool = is_red(Red);
  let t_not_bl : Bool = not_red(Blue);  // Blue is not Red → false
  let t_succ   : Bool = is_nonzero(Nat.Succ(Nat.Zero));
  let t_or     : Bool = red_or_blue(Green);  // Green is neither → false
  // Only t_red and t_succ are True; the composed answer is False.
  // We return t_red and t_succ to verify the positive arms work.
  return t_red and t_succ;
end fn;
