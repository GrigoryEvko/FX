// Q78: nested match on parameterized inductive — ctor-arg
// bindings register their types in Scope.
//
// Q76/Q77 added scope type hints for fn params and let
// bindings.  Q78 closes the remaining common gap: match arm
// ctor-arg bindings.  When an arm pattern is `Some(inner)` on
// a scrutinee of `Option(T)`, the bound `inner` has type T
// (computed by `substParams scrutineeTypeArgs ctorSpec.args[i]`).
// The Scope now registers this type alongside the name.
//
// Implementation split: `scopeAndDepthForCtorTyped` is a new
// variant that takes BOTH the ORIGINAL arg types (used for
// self-ref detection) and the SUBSTITUTED arg types (used as
// the scope type hint).  The split is load-bearing — naive
// substitution turns an `Option(Option(Nat))` payload into
// something the self-ref check mis-reads as "this arg is an
// Option, therefore self-referential", adding a spurious rec
// binder and breaking the arm's lambda-chain depth math.

// --- Nested match on Option(Option(Nat)) -------------------

fn unwrap_double(outer: Option(Option(Nat))) : Nat = match outer;
  None        => Nat.Zero;
  Some(inner) => match inner;
    None    => Nat.Zero;
    Some(x) => x;
  end match;
end match;

fn check_deep() : Nat =
  unwrap_double(outer: Option.Some(Option.Some(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))));  // 3

fn check_inner_none() : Nat =
  unwrap_double(outer: Option.Some(Option.None));  // 0

fn check_outer_none() : Nat =
  unwrap_double(outer: Option.None);  // 0

// --- Nested match rejoining with outer scrutinee data -----

fn double_if_present(outer: Option(Option(Nat))) : Nat = match outer;
  None        => Nat.Zero;
  Some(inner) => match inner;
    None    => Nat.Zero;
    Some(x) => x + x;
  end match;
end match;

fn check_double_three() : Nat =
  double_if_present(outer: Option.Some(Option.Some(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))))));  // 6

// --- Pattern-bound var used as scrutinee of a second match
//     with Bool element type.

fn unwrap_bool_or_false(m: Option(Option(Bool))) : Bool = match m;
  None        => Bool.False;
  Some(inner) => match inner;
    None    => Bool.False;
    Some(b) => b;
  end match;
end match;

fn check_bool_deep_true() : Bool =
  unwrap_bool_or_false(m: Option.Some(Option.Some(Bool.True)));  // true

fn check_bool_deep_false() : Bool =
  unwrap_bool_or_false(m: Option.Some(Option.Some(Bool.False)));  // false

fn check_bool_deep_none() : Bool =
  unwrap_bool_or_false(m: Option.None);  // false

fn main() : Nat = check_deep();
