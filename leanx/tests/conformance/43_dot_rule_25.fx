// Q65: §4.2 rule 25 — multi-dot expressions in argument
// position desugar to a SINGLE `fn(it) => ...` sharing the
// same implicit element across every `.field` occurrence.
//
// Pre-Q65 only the bare form `map(.name)` worked; composing
// dots through logical/prefix/binop nodes (`.active and
// .enabled`) fired E010 at elab because the top-level AST
// node at the arg site wasn't `.dotShorthand`.  Post-Q65 the
// call-arg dispatch detects any dot reachable through
// composable non-binding nodes and lifts the whole expression
// into `fn(it) => subst(expr)` before recursing.
//
// Lift scope: binop / prefix / logical not|and|or / pipe /
// try-prefix / if-then-else / field / index.  Stops at lambda,
// match, for, while, begin (those introduce their own
// scope), matching the spec's §4.2 prose "use explicit lambda"
// escape hatch.
//
// §7.8: `user` is `@[copy]` so the lifted lambda's implicit
// `it` can be used in multiple field projections without
// tripping M001.  Without `@[copy]`, multi-use of a linear
// record under a single lambda binder is a LEGITIMATE
// rejection — the lift mechanism itself is sound either way.
@[copy]
type user {
  active:  Bool;
  enabled: Bool;
  paid:    Bool;
};

fn apply_pred(p: user -> Bool, u: user) : Bool = p(u);

// Test 1 — bare dot (Q61 path unchanged).
fn test_bare(u: user) : Bool = apply_pred(p: .active, u: u);

// Test 2 — logical `and` of two dots (§4.2 rule 25 canonical).
fn test_and(u: user) : Bool =
  apply_pred(p: .active and .enabled, u: u);

// Test 3 — logical `or` of two dots.
fn test_or(u: user) : Bool =
  apply_pred(p: .active or .paid, u: u);

// Test 4 — `not` over a single dot (prefix walk).
fn test_not(u: user) : Bool =
  apply_pred(p: not .active, u: u);

// Test 5 — compound `(a and b) or c` mixing three fields.
fn test_triple(u: user) : Bool =
  apply_pred(p: .active and .enabled or .paid, u: u);

fn main() : Bool
begin fn
  let alice : user = user {
    active:  Bool.True,
    enabled: Bool.True,
    paid:    Bool.False
  };
  // True and True = True, so apply_pred returns True.
  return test_and(alice);
end fn;
