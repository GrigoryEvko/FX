// Q71: §3.7 list literals `[a, b, c]`.  Parser recognizes `[`
// at atom position as a list literal (postfix `[` → index is
// unchanged).  Elab extracts the element type from the
// expected `List(T)` Pi and builds a `Cons`/`Nil` chain over
// the prelude `List` spec.  Empty `[]` is bare `Nil`.
//
// `List` was moved from `Inductive.Experimental` into the main
// `preludeSpecs` registry specifically for this landing — the
// elaborator bakes concrete element types into `Term.ctor
// "List" [elementType] [...]` directly, sidestepping the A10
// gap (elaborator-side type-arg inference on `var 0` ctor
// args).  Polymorphic FX fns over `List` still require A10.
fn empty_nat() : List(Nat) = [];

fn one_nat() : List(Nat) = [Nat.Zero];

fn three_nats() : List(Nat) =
  [Nat.Zero, Nat.Succ(Nat.Zero), Nat.Succ(Nat.Succ(Nat.Zero))];

fn bool_list() : List(Bool) = [Bool.True, Bool.False, Bool.True];

// Trailing comma tolerated.
fn trailing_comma() : List(Nat) = [Nat.Zero, Nat.Succ(Nat.Zero),];

// Nested — a list of lists via the same sugar.  (Element type
// threads through: outer expected is `List(List(Nat))`; each
// item is a `List(Nat)`, each item of those is a Nat.)
fn nested() : List(List(Nat)) =
  [[Nat.Zero], [Nat.Succ(Nat.Zero), Nat.Succ(Nat.Succ(Nat.Zero))]];

// Items computed via Q70 arithmetic — proves the elab threads
// the element type into composite expressions, not just literals.
fn computed() : List(Nat) =
  [Nat.Succ(Nat.Zero) + Nat.Succ(Nat.Succ(Nat.Zero)),
   Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) * Nat.Succ(Nat.Succ(Nat.Zero))];

fn main() : List(Nat) = computed();
