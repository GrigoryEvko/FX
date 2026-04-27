// Q84: `as`-patterns in match arms.
//
// Per `fx_design.md` §4.3: "Patterns include: literals,
// constructors, wildcards, variable bindings, tuple patterns,
// record patterns, spread patterns, and `as` bindings".  Per
// `fx_grammar.md` §8: `as_pattern = app_pattern (AS lower_ident)?`.
//
// Before Q84 the parser didn't consume `as` and the AST had no
// constructor for as-bindings.
//
// Implementation:
//
//   * `Pattern.asPattern inner name span` added to the AST
//     (FX/Syntax/Ast.lean).
//   * `parsePattern` split into `parsePatternBase` + optional
//     `as IDENT` postfix (FX/Syntax/Parser.lean).
//   * `resolveArmCtor?` peeks through `.asPattern` so ctor-
//     specific classification still fires for `Succ(p) as n`.
//   * `stripArmAsPattern` helper extracts the base pattern and
//     the as-name (MatchHelpers.lean, Q84).
//   * `buildMethods` in elabMatch threads the as-name alongside
//     each arm.  For ctor-specific `Succ(p) as n`, the as-name
//     feeds into the same `varCatchAllName` slot Q82 uses for
//     var-pattern catch-alls — so the existing β-redex wrap
//     `(λ n : scrutineeType. body) (Ctor args)` binds `n` to
//     the reconstructed ctor value.  For catch-all `_ as n`,
//     the name is equivalent to the var-pattern `n`.
//
// Scope: top-of-arm-pattern `as` bindings only.  Nested `as` on
// ctor args (`Some(Cons(h, t) as inner)`) is parsed but
// rejected at elaboration — nested destructuring / nested `as`
// is a future task.

// --- Ctor-specific `as` binding --------------------------

// `Succ(p) as whole` binds both `p` (ctor arg) and `whole` (the
// reconstructed Succ value).  Returning `whole` proves the
// β-redex ran and carried the reconstruction.
fn identity_non_zero(n: Nat) : Nat = match n;
  Zero             => Nat.Zero;
  Succ(p) as whole => whole;
end match;

// Body uses BOTH bindings: ctor arg `p` and as-name `whole`.
fn double_succ_arg(n: Nat) : Nat = match n;
  Zero             => Nat.Zero;
  Succ(p) as whole => whole;   // return the full successor
end match;

// --- Wildcard + `as` (equivalent to var-pattern) -------

fn is_some(m: Option(Nat)) : Bool = match m;
  Some(_) => Bool.True;
  _ as other => Bool.False;
end match;

fn opt_echo(m: Option(Nat)) : Option(Nat) = match m;
  None => Option.None;
  _ as everything => everything;
end match;

// --- Ctor-specific `as` on multi-arg ctor --------------

fn list_echo(xs: List(Nat)) : List(Nat) = match xs;
  Nil => [];
  Cons(_h, _t) as whole => whole;
end match;

// --- `as` bindings with guards (composes with Q83) ------

fn small_or_echo(n: Nat) : Nat = match n;
  Zero                              => Nat.Zero;
  Succ(p) as whole if p == Nat.Zero => Nat.Zero;  // "1" → 0
  _ as other                        => other;     // others → self
end match;

// --- User enum with `as` on a ctor -----------------------

type color
  Red;
  Green;
  Blue;
end type;

fn which_color(c: color) : color = match c;
  Red as r => r;
  _ as other => other;
end match;

// --- Callers to pin outputs ------------------------------

fn id_zero() : Nat = identity_non_zero(n: Nat.Zero);                          // 0
fn id_one()  : Nat = identity_non_zero(n: Nat.Succ(Nat.Zero));                // 1
fn id_two()  : Nat = identity_non_zero(n: Nat.Succ(Nat.Succ(Nat.Zero)));      // 2

fn dbl_zero() : Nat = double_succ_arg(n: Nat.Zero);                            // 0
fn dbl_two()  : Nat = double_succ_arg(n: Nat.Succ(Nat.Succ(Nat.Zero)));        // 2

fn some_yes() : Bool = is_some(m: Option.Some(Nat.Zero));                      // True
fn some_no()  : Bool = is_some(m: Option.None);                                 // False

fn echo_some() : Option(Nat) = opt_echo(m: Option.Some(Nat.Succ(Nat.Zero)));   // Some(1)
fn echo_none() : Option(Nat) = opt_echo(m: Option.None);                        // None

fn list_nil() : List(Nat) = list_echo(xs: []);                                   // Nil
fn list_one() : List(Nat) = list_echo(xs: [Nat.Succ(Nat.Zero)]);                 // [1]

fn sm_zero() : Nat = small_or_echo(n: Nat.Zero);                                 // 0
fn sm_one()  : Nat = small_or_echo(n: Nat.Succ(Nat.Zero));                       // 0 (guard fires)
fn sm_three(): Nat = small_or_echo(n: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));   // 3

fn wc_red()   : color = which_color(c: Red);
fn wc_green() : color = which_color(c: Green);

fn main() : Nat = id_two();
