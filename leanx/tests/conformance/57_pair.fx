// Q79: `Pair(T, U)` — two-parameter inductive first-class.
//
// Pair moves from `experimentalSpecs` into the main prelude
// registry, joining Option (Q75) and List (Q71).  Core prelude
// grows from 6 to 7 specs; experimentalSpecs drops to just
// [resultSpec].
//
// The two-parameter case exercises a subtly different
// `Term.substParams` path than Option's one parameter.  For
// ctor args `[var 1, var 0]` (Pair's MkPair arg types):
//
//   * typeArgs `[a, b]` after reverse = `[b, a]`.
//   * openWith b: replaces var 0 (= second param) with b;
//     shifts others down, so var 1 becomes var 0.
//   * openWith a: replaces the NEW var 0 (= originally var 1,
//     first param) with a.
//
// Result: MkPair's args substitute correctly to `[a, b]`.
// Q78's Scope type hints propagate the substituted arg types
// into pattern-bound names, so `MkPair(x, y)` binds `x: a` and
// `y: b` with the right types.

// --- Construction + simple access ---------------------

fn mkpair_nn() : Pair(Nat, Nat) =
  Pair.MkPair(Nat.Zero, Nat.Succ(Nat.Zero));

fn mkpair_nb() : Pair(Nat, Bool) =
  Pair.MkPair(Nat.Succ(Nat.Succ(Nat.Zero)), Bool.True);

fn mkpair_bn() : Pair(Bool, Nat) =
  Pair.MkPair(Bool.False, Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));

// --- Projection functions via match -------------------

fn first_nb(p: Pair(Nat, Bool)) : Nat = match p;
  MkPair(a, b) => a;
end match;

fn second_nb(p: Pair(Nat, Bool)) : Bool = match p;
  MkPair(a, b) => b;
end match;

fn first_bn(p: Pair(Bool, Nat)) : Bool = match p;
  MkPair(a, b) => a;
end match;

fn second_bn(p: Pair(Bool, Nat)) : Nat = match p;
  MkPair(a, b) => b;
end match;

// --- Chained access on let-bound pair -----------------

fn sum_pair(p: Pair(Nat, Nat)) : Nat = match p;
  MkPair(a, b) => a + b;
end match;

fn let_then_project() : Nat
begin fn
  let p : Pair(Nat, Nat) =
    Pair.MkPair(Nat.Succ(Nat.Succ(Nat.Zero)),
                Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));
  let s : Nat = sum_pair(p: p);
  return s;
end fn;

// --- Nested Pair ---------------------------------------

fn nested_pair() : Pair(Pair(Nat, Nat), Bool) =
  Pair.MkPair(Pair.MkPair(Nat.Zero, Nat.Succ(Nat.Zero)), Bool.True);

fn inner_first(p: Pair(Pair(Nat, Nat), Bool)) : Nat = match p;
  MkPair(inner, flag) => match inner;
    MkPair(a, b) => a;
  end match;
end match;

fn outer_flag(p: Pair(Pair(Nat, Nat), Bool)) : Bool = match p;
  MkPair(inner, flag) => flag;
end match;

// --- Callers ------------------------------------------

fn check_first_nb()   : Nat  = first_nb(p: mkpair_nb());              // 2
fn check_second_nb()  : Bool = second_nb(p: mkpair_nb());             // true
fn check_first_bn()   : Bool = first_bn(p: mkpair_bn());              // false
fn check_second_bn()  : Nat  = second_bn(p: mkpair_bn());             // 3
fn check_sum()        : Nat  = let_then_project();                    // 5
fn check_inner_first(): Nat  = inner_first(p: nested_pair());         // 0
fn check_outer_flag() : Bool = outer_flag(p: nested_pair());          // true

fn main() : Nat = check_sum();
