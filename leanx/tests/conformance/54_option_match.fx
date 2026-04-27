// Q76: match on parameterized inductives via Scope type hints.
//
// Q75 registered `Option(T)` in the main prelude and got
// construction working.  The `match` form stayed gated because
// Scope didn't track per-binder types, so there was no way to
// recover `[Nat]` from a scrutinee like `m: Option(Nat)`.
//
// Q76 adds a `types : List (Option Term)` field to Scope
// parallel to `binders`.  Fn parameter binders (both
// `elabFnParamsInOrder` for top-level decls and the local-fn
// `elabParams`) now call `pushWithType paramName paramType`,
// registering the type alongside the name.  elabMatch consults
// `scope.typeOf?` for variable scrutinees; when the hint is
// `.ind specName typeArgs`, it threads typeArgs into both the
// scrutinee's expected type and the motive's domain.
//
// Sites that don't yet push with type (pattern-bound match
// args, lambda params without annotation, let bindings) still
// fall back to the synthesis probe path.  A follow-up can
// extend those.
//
// This file exercises the common idioms users reach for.

// --- Fn-parameter-typed scrutinee -----------------------

fn unwrap_or_zero(m: Option(Nat)) : Nat = match m;
  None    => Nat.Zero;
  Some(x) => x;
end match;

fn is_some(m: Option(Nat)) : Bool = match m;
  None    => Bool.False;
  Some(x) => Bool.True;
end match;

fn double_or_zero(m: Option(Nat)) : Nat = match m;
  None    => Nat.Zero;
  Some(x) => x + x;
end match;

// --- Option over Bool — proves typeArg inference works for
//     arbitrary element types, not just Nat.

fn bool_value_or_false(m: Option(Bool)) : Bool = match m;
  None    => Bool.False;
  Some(b) => b;
end match;

// --- Call from another fn to exercise scope-typed return. ---

fn some_three() : Option(Nat) =
  Option.Some(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));

fn extract_three() : Nat = unwrap_or_zero(m: some_three());

// --- Callers that pin expected behavior. ---

fn check_unwrap_some_zero() : Nat = unwrap_or_zero(m: Option.Some(Nat.Zero));    // 0
fn check_unwrap_some_five() : Nat =
  unwrap_or_zero(m: Option.Some(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))));  // 5
fn check_unwrap_none()      : Nat = unwrap_or_zero(m: Option.None);              // 0

fn check_is_some_yes() : Bool = is_some(m: Option.Some(Nat.Zero));               // true
fn check_is_some_no()  : Bool = is_some(m: Option.None);                          // false

fn check_double_two() : Nat = double_or_zero(m: Option.Some(Nat.Succ(Nat.Succ(Nat.Zero))));  // 4
fn check_double_none() : Nat = double_or_zero(m: Option.None);                               // 0

fn check_bool_true()  : Bool = bool_value_or_false(m: Option.Some(Bool.True));   // true
fn check_bool_false() : Bool = bool_value_or_false(m: Option.Some(Bool.False));  // false
fn check_bool_none()  : Bool = bool_value_or_false(m: Option.None);              // false

fn main() : Nat = extract_three();
