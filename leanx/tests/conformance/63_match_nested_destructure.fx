// Q85: nested ctor-arg destructuring.
//
// Per `fx_design.md` §4.3 + `fx_grammar.md` §8, ctor-arg
// patterns can themselves be ctor patterns:
// `Some(Cons(h, _)) => body`.  Before Q85 the elaborator
// rejected any non-identifier / non-wildcard ctor-arg pattern
// with "nested patterns deferred".
//
// Implementation (AST-level rewrite):
//
//   Before `buildMethods` extracts argPatterns from the primary
//   arm, `rewriteNestedArgs` (MatchHelpers.lean) checks for
//   nested ctor args.  When found, it:
//
//     1. Replaces the nested position with a fresh `__nested_
//        arg_{i}` var binder.
//     2. Synthesizes an inner `match __fresh; nestedPat =>
//        origBody; _ => catchAllBody; end match` as the arm
//        body.
//     3. Moves any outer guard INTO the inner arm (so it can
//        reference the inner bindings).
//
//   The elaborator's recursive `elabExpr` → `elabMatch` call
//   processes the inner match end-to-end — Q81 wildcards, Q82
//   var-patterns, Q83 guards, Q84 `as`-bindings ALL compose
//   underneath, since the inner match goes through the same
//   pipeline.
//
// Scope:
//   * One nested position per arm.  Multiple nested positions
//     would need a chain of inner matches — deferred.
//   * Requires an unguarded WILDCARD catch-all (no var binding).
//     Var-pattern / as-pattern catch-alls bind the scrutinee
//     value, which isn't in scope inside the synthesized inner
//     match.

// --- Head extraction through Option-of-List ---------------

fn head_or_zero(m: Option(List(Nat))) : Nat = match m;
  Some(Cons(h, _)) => h;
  _                => Nat.Zero;
end match;

// --- Nested with multi-arg outer ctor ---------------------

// `MkPair(Some(_), _)` destructures the first arg.  The second
// arg stays a wildcard; the outer catch-all covers the rest.
fn has_some_left(p: Pair(Option(Nat), Bool)) : Bool = match p;
  MkPair(Some(_), _) => Bool.True;
  _                  => Bool.False;
end match;

// --- Nested with guard composing with Q83 -----------------

// Inner pattern guard: `Cons(h, _) if h == Zero => ...`.  After
// Q85 rewrite the guard moves into the inner match arm — Q83
// then handles the if/else chain.
fn starts_with_zero(xs: List(Nat)) : Bool = match xs;
  Cons(h, _) => h == Nat.Zero;
  _          => Bool.False;
end match;

// --- Nested as-pattern on inner ctor (Q84 compose) -------

fn describe_list(xs: Option(List(Nat))) : List(Nat) = match xs;
  Some(Cons(h, _) as inner) => inner;
  _                         => [];
end match;

// --- Deeper chain: outer ctor with nested inside nested --

// Only ONE outer arm with nested, other cases fall through.
// The inner `Some(Nat)` itself can't nest further without
// more work, but the first-level nesting suffices for many
// common idioms.
fn nested_some_cons(m: Option(List(Nat))) : Nat = match m;
  Some(Cons(Nat.Zero, _)) => Nat.Succ(Nat.Zero);  // head is zero → 1
  _                       => Nat.Zero;             // anything else → 0
end match;

// --- Callers to pin outputs -------------------------------

fn check_head_none() : Nat = head_or_zero(m: Option.None);                           // 0
fn check_head_some_nil() : Nat = head_or_zero(m: Option.Some([]));                   // 0
fn check_head_some_one() : Nat = head_or_zero(m: Option.Some([Nat.Succ(Nat.Zero)])); // 1
fn check_head_some_chain() : Nat =
  head_or_zero(m: Option.Some([Nat.Zero, Nat.Succ(Nat.Zero)]));                      // 0

fn check_pair_some() : Bool =
  has_some_left(p: Pair.MkPair(Option.Some(Nat.Zero), Bool.True));                   // True
fn check_pair_none() : Bool =
  has_some_left(p: Pair.MkPair(Option.None, Bool.False));                             // False

fn check_starts_zero() : Bool = starts_with_zero(xs: [Nat.Zero]);                    // True
fn check_starts_one()  : Bool = starts_with_zero(xs: [Nat.Succ(Nat.Zero)]);          // False
fn check_starts_empty(): Bool = starts_with_zero(xs: []);                             // False

fn check_describe_nil() : List(Nat) = describe_list(xs: Option.None);                // []
fn check_describe_one() : List(Nat) =
  describe_list(xs: Option.Some([Nat.Succ(Nat.Zero)]));                              // [1]

fn check_nested_zero() : Nat =
  nested_some_cons(m: Option.Some([Nat.Zero, Nat.Succ(Nat.Zero)]));                  // 1 (head is Zero)
fn check_nested_one()  : Nat =
  nested_some_cons(m: Option.Some([Nat.Succ(Nat.Zero)]));                            // 0 (head is 1, not Zero)

fn main() : Nat = check_head_some_one();
