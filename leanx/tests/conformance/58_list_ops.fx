// Q80: recursive match on List(T) via the Q75-Q79 parameterized-
// inductive support chain.
//
// Q71 put `List` into the prelude and added list literals.  Q76
// added scope type hints for fn params; Q78 added them for
// match-arm ctor-arg bindings.  Q80 shows the composition:
// structural recursion on the Cons tail works end-to-end
// because:
//
//   * `list_length(xs: List(Nat))` — `xs`'s scope hint is
//     `Term.ind "List" [Nat]`, so the match recovers typeArgs
//     `[Nat]` for the motive (Q76).
//   * `Cons(h, t) => ...` — `t`'s substituted arg type is
//     `Term.ind "List" [Nat]` (List's Cons declared arg type
//     `.ind "List" [.var 0]` with var 0 → Nat), so `t` is
//     scope-typed `List(Nat)` (Q78).
//   * `list_length(xs: t)` — `t`'s scope hint flows through,
//     so the recursive call elabs cleanly.
//
// All operations below are MONOMORPHIC over Nat.  Polymorphic
// `fn length<T>(xs: List(T)) : Nat` still needs A10 (elaborator-
// side type-arg inference on fn type parameters at call sites).
// Monomorphic versions unblock real programs today.

// --- Basic counting -----------------------------------

fn list_length(xs: List(Nat)) : Nat = match xs;
  Nil         => Nat.Zero;
  Cons(h, t)  => Nat.Succ(list_length(xs: t));
end match;

// --- Folding — sum over a Nat list --------------------

fn list_sum(xs: List(Nat)) : Nat = match xs;
  Nil         => Nat.Zero;
  Cons(h, t)  => h + list_sum(xs: t);
end match;

// --- Predicates on shape ------------------------------

fn list_is_empty(xs: List(Nat)) : Bool = match xs;
  Nil         => Bool.True;
  Cons(h, t)  => Bool.False;
end match;

// --- Safe head via default value ----------------------

fn list_head_or(default: Nat, xs: List(Nat)) : Nat = match xs;
  Nil         => default;
  Cons(h, t)  => h;
end match;

// --- Membership check — recursion + `==` --------------

fn list_contains(needle: Nat, xs: List(Nat)) : Bool = match xs;
  Nil         => Bool.False;
  Cons(h, t)  => if h == needle;
                   Bool.True
                 else
                   list_contains(needle: needle, xs: t)
                 end if;
end match;

// --- Composition with Q71 list literals + Q70 arithmetic ---

fn check_len_zero()   : Nat  = list_length(xs: []);
fn check_len_one()    : Nat  = list_length(xs: [Nat.Zero]);
fn check_len_three()  : Nat  = list_length(xs: [Nat.Zero, Nat.Succ(Nat.Zero), Nat.Succ(Nat.Succ(Nat.Zero))]);

fn check_sum_empty()  : Nat  = list_sum(xs: []);
fn check_sum_123()    : Nat  = list_sum(xs: [Nat.Succ(Nat.Zero), Nat.Succ(Nat.Succ(Nat.Zero)), Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))]);

fn check_empty_yes()  : Bool = list_is_empty(xs: []);
fn check_empty_no()   : Bool = list_is_empty(xs: [Nat.Zero]);

fn check_head_default() : Nat = list_head_or(default: Nat.Succ(Nat.Zero), xs: []);
fn check_head_first()   : Nat = list_head_or(default: Nat.Zero, xs: [Nat.Succ(Nat.Succ(Nat.Zero))]);

fn check_contains_yes() : Bool =
  list_contains(needle: Nat.Succ(Nat.Succ(Nat.Zero)),
                xs: [Nat.Zero, Nat.Succ(Nat.Zero), Nat.Succ(Nat.Succ(Nat.Zero))]);
fn check_contains_no() : Bool =
  list_contains(needle: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))),
                xs: [Nat.Zero, Nat.Succ(Nat.Zero), Nat.Succ(Nat.Succ(Nat.Zero))]);
fn check_contains_empty() : Bool =
  list_contains(needle: Nat.Zero, xs: []);

fn main() : Nat = check_sum_123();
