// Q75: §3.3 `Option(T)` first-class construction.
//
// Moves `optionSpec` from `Inductive.Experimental` into the
// main `preludeSpecs` registry (alongside `listSpec` from Q71).
// Elaborator's existing expected-type threading in the `.var`
// ctor path (nullary ctors) and `.app` ctor path (applied ctors)
// pulls `T` from the surrounding `Option(T)` context and bakes
// it into `Term.ctor "Option" [T] [...]`.  The kernel's
// `substParams` handles `.var 0` substitution at ctor-arg check
// time, so no elaborator-side type-arg unification is needed.
//
// Deferred to a follow-up (requires threading a typing context
// through elab to recover per-binder types):
//
//   * `match m; None => ...; Some(x) => ...; end match;` on
//     parameterized inductives.  Today's elab gates this with
//     E010 pointing at the workaround.
//   * `some_x is Some` / `some_x is None` constructor-test (Q66),
//     which desugars to a match and hits the same gate.
//
// Scope of this file: CONSTRUCTION only.  Pattern discrimination
// on Option lands in a follow-up.

// Nullary `Option.None` with expected-type threading.
fn none_nat() : Option(Nat) = Option.None;
fn none_bool() : Option(Bool) = Option.None;

// Applied `Option.Some(x)` with expected-type threading.
fn some_zero() : Option(Nat) = Option.Some(Nat.Zero);
fn some_one()  : Option(Nat) = Option.Some(Nat.Succ(Nat.Zero));
fn some_true() : Option(Bool) = Option.Some(Bool.True);
fn some_false(): Option(Bool) = Option.Some(Bool.False);

// Nested `Option(Option(Nat))` — the inner Option's typeArgs
// thread through the outer's ctor-arg elaboration.
fn nested_some_some() : Option(Option(Nat)) =
  Option.Some(Option.Some(Nat.Zero));
fn nested_some_none() : Option(Option(Nat)) =
  Option.Some(Option.None);
fn nested_none()      : Option(Option(Nat)) = Option.None;

// Construction inside a block body.
fn block_some() : Option(Nat)
begin fn
  let inner = Nat.Succ(Nat.Succ(Nat.Zero));
  return Option.Some(inner);
end fn;

// Construction inside an if-branch.
fn flag_to_option(flag: Bool) : Option(Nat) =
  if flag;
    Option.Some(Nat.Zero)
  else
    Option.None
  end if;

fn when_true()  : Option(Nat) = flag_to_option(flag: Bool.True);
fn when_false() : Option(Nat) = flag_to_option(flag: Bool.False);

// Return the whole option from main to demonstrate pretty output.
fn main() : Option(Nat) = some_one();
