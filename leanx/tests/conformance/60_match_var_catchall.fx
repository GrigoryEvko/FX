// Q82: variable-pattern `n => body` as match catch-all.
//
// Per `fx_design.md` §4.3, match patterns include variable
// bindings.  Q81 landed the wildcard form (`_ => body`); Q82
// completes the catch-all story with the binding form where the
// body references the scrutinee as a named value.
//
// Implementation strategy (MatchHelpers.lean +
// Elaborate.lean elabMatch):
//
//   When neither a ctor-specific arm nor a wildcard arm covers
//   some ctor, the elaborator looks for a var-pattern arm
//   `n => body` and synthesizes a method body shaped as a
//   β-redex `(λ n : scrutineeType. body) (Ctor(arg_0, ...,
//   arg_{k-1}))`.  The kernel's whnf reduces the β-redex, so
//   `n` in the body sees the reconstructed ctor value at zero
//   cost beyond the standard β step.  `Ctor(args)` uses the
//   de Bruijn indices computed by the new
//   `argDeBruijnIndicesForCtor` helper, which mirrors
//   `scopeAndDepthForCtor`'s push counts (arg itself + extra
//   `_rec` binder for self-ref args) so the indices agree with
//   the method's lambda chain.

// --- Var catch-all on Nat ---------------------------------

fn is_zero(n: Nat) : Bool = match n;
  Zero => Bool.True;
  k    => Bool.False;
end match;

// Body uses the bound var — proves the β-redex reconstructs
// the ctor value (not just passes `_`).
fn identity_non_zero(n: Nat) : Nat = match n;
  Zero => Nat.Zero;
  k    => k;
end match;

// --- Var catch-all on Option ------------------------------

fn opt_has_value(m: Option(Nat)) : Bool = match m;
  Some(x) => Bool.True;
  other   => Bool.False;
end match;

fn echo_non_none(m: Option(Nat)) : Option(Nat) = match m;
  None  => Option.None;
  other => other;
end match;

// --- Var catch-all on List --------------------------------

fn list_is_empty(xs: List(Nat)) : Bool = match xs;
  Nil  => Bool.True;
  rest => Bool.False;
end match;

// --- Var catch-all on a user-defined enum -----------------

type color
  Red;
  Green;
  Blue;
end type;

fn is_red(c: color) : Bool = match c;
  Red => Bool.True;
  x   => Bool.False;
end match;

// --- Callers to pin outputs -------------------------------

fn check_is_zero_yes() : Bool = is_zero(n: Nat.Zero);              // true
fn check_is_zero_no()  : Bool = is_zero(n: Nat.Succ(Nat.Zero));    // false

fn check_identity_zero() : Nat = identity_non_zero(n: Nat.Zero);            // 0
fn check_identity_one()  : Nat = identity_non_zero(n: Nat.Succ(Nat.Zero));  // 1
fn check_identity_two()  : Nat =
  identity_non_zero(n: Nat.Succ(Nat.Succ(Nat.Zero)));                       // 2

fn check_opt_some() : Bool = opt_has_value(m: Option.Some(Nat.Zero));  // true
fn check_opt_none() : Bool = opt_has_value(m: Option.None);             // false

fn check_echo_some() : Option(Nat) =
  echo_non_none(m: Option.Some(Nat.Succ(Nat.Zero)));                    // Some(1)
fn check_echo_none() : Option(Nat) = echo_non_none(m: Option.None);     // None

fn check_list_empty_yes() : Bool = list_is_empty(xs: []);           // true
fn check_list_empty_no()  : Bool = list_is_empty(xs: [Nat.Zero]);   // false

fn check_color_red()   : Bool = is_red(c: Red);    // true
fn check_color_green() : Bool = is_red(c: Green);  // false
fn check_color_blue()  : Bool = is_red(c: Blue);   // false

fn main() : Bool = check_identity_two() == Nat.Succ(Nat.Succ(Nat.Zero));
