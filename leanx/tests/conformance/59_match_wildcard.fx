// Q81: wildcard arm `_ => body` as catch-all in match
// expressions.
//
// Per `fx_design.md` §4.3, match patterns include wildcards
// (`_`).  Before Q81 the elaborator rejected any match that
// didn't have one explicit arm per ctor with a non-exhaustive
// diagnostic; authors had to write `Succ(p) => body` even when
// they didn't need `p`.
//
// Implementation: in `elabMatch`'s ctor walk, when no ctor-
// specific arm matches, look for a wildcard arm in the list
// and synthesize a ctor-specific arm from it — the pattern
// becomes `SpecName.CtorName(_, _, ..)` with one wildcard per
// declared ctor arg, body stays the same.  Downstream methods-
// build proceeds identically to an explicit arm.
//
// Variable-pattern catch-all (`n => body`) binds the scrutinee
// value as `n` in the body.  Implementing that requires
// reconstructing the ctor value inside the method and is
// deferred to a follow-up.  For now, `_ => body` covers the
// common "I don't care about the arg" case.

// --- Wildcard on Nat ----------------------------------

fn is_zero(n: Nat) : Bool = match n;
  Zero => Bool.True;
  _    => Bool.False;
end match;

fn is_succ(n: Nat) : Bool = match n;
  Succ(p) => Bool.True;
  _       => Bool.False;
end match;

// --- Wildcard on Option ------------------------------

fn opt_has_value(m: Option(Nat)) : Bool = match m;
  Some(x) => Bool.True;
  _       => Bool.False;
end match;

fn opt_is_none(m: Option(Nat)) : Bool = match m;
  None => Bool.True;
  _    => Bool.False;
end match;

// --- Wildcard on List --------------------------------

fn list_is_empty(xs: List(Nat)) : Bool = match xs;
  Nil => Bool.True;
  _   => Bool.False;
end match;

fn list_has_head(xs: List(Nat)) : Bool = match xs;
  Cons(h, t) => Bool.True;
  _          => Bool.False;
end match;

// --- Ternary user-defined enum with wildcard ----------

type color
  Red;
  Green;
  Blue;
end type;

fn is_red(c: color) : Bool = match c;
  Red => Bool.True;
  _   => Bool.False;
end match;

// --- Callers to pin outputs --------------------------

fn check_is_zero_yes() : Bool = is_zero(n: Nat.Zero);              // true
fn check_is_zero_no()  : Bool = is_zero(n: Nat.Succ(Nat.Zero));    // false
fn check_is_succ_yes() : Bool = is_succ(n: Nat.Succ(Nat.Zero));    // true
fn check_is_succ_no()  : Bool = is_succ(n: Nat.Zero);              // false

fn check_opt_some() : Bool = opt_has_value(m: Option.Some(Nat.Zero));  // true
fn check_opt_none() : Bool = opt_has_value(m: Option.None);             // false

fn check_list_empty_yes() : Bool = list_is_empty(xs: []);           // true
fn check_list_empty_no()  : Bool = list_is_empty(xs: [Nat.Zero]);   // false

fn check_color_red()   : Bool = is_red(c: Red);    // true
fn check_color_green() : Bool = is_red(c: Green);  // false
fn check_color_blue()  : Bool = is_red(c: Blue);   // false

fn main() : Bool = check_is_zero_yes();
