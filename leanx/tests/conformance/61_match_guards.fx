// Q83: guarded match arms with catch-all fallthrough.
//
// Per `fx_design.md` §4.3, match patterns admit guards:
// "Guards refine pattern arms".  Before Q83 the elaborator
// rejected every guarded arm with "guards not supported in M2".
//
// Implementation (Elaborate.lean elabMatch):
//
//   When a ctor-specific arm carries a guard, the elaborator
//   builds the method body as `if guard; primaryBody else
//   catchAllBody`.  At the kernel level this is one
//   `Term.indRec "Bool" (boolMotive shiftedReturnType)
//   [catchAllBody, primaryBody] guardTerm` — the same shape B6
//   uses for if/else.  The guard and primary body are
//   elaborated under `bodyScope` (ctor arg bindings in scope);
//   the catch-all body is elaborated under the same scope
//   (plus var-extension + β-redex for var-pattern catch-alls,
//   reusing the Q82 machinery).
//
// Scope boundary: guards are allowed on ctor-specific arms
// only.  Guards on catch-alls (wildcard or var-pattern) are
// deferred — they'd need their own fallthrough (another
// catch-all or a totality proof).  The 90% idiom puts the
// guard on the ctor-specific arm, so the restriction rarely
// bites; programs that need chained guards on a catch-all can
// write a nested `match` inside the catch-all body.

// --- Guard on ctor arm + wildcard catch-all --------------

fn classify(n: Nat) : Bool = match n;
  Zero                      => Bool.True;
  Succ(p) if p == Nat.Zero  => Bool.False;
  _                         => Bool.True;
end match;

// --- Guard on ctor arm + var-pattern catch-all -----------

fn one_if_some_zero(m: Option(Nat)) : Nat = match m;
  Some(x) if x == Nat.Zero => Nat.Succ(Nat.Zero);
  other                    => Nat.Zero;
end match;

// --- Guard on a user-enum ctor arm -----------------------

type color
  Red;
  Green;
  Blue;
end type;

fn color_score(c: color) : Nat = match c;
  Red                          => Nat.Succ(Nat.Zero);
  _                            => Nat.Zero;
end match;

// --- Guard using a recursive prelude fn in the condition -

fn describe(n: Nat) : Bool = match n;
  Zero                                => Bool.False;
  Succ(p) if p == Nat.Succ(Nat.Zero)  => Bool.True;
  _                                   => Bool.False;
end match;

// --- Callers to pin outputs ------------------------------

fn check_classify_zero() : Bool = classify(n: Nat.Zero);                        // True
fn check_classify_one()  : Bool = classify(n: Nat.Succ(Nat.Zero));              // False (guard fires)
fn check_classify_two()  : Bool = classify(n: Nat.Succ(Nat.Succ(Nat.Zero)));    // True (guard fails)

fn check_osz_zero() : Nat = one_if_some_zero(m: Option.Some(Nat.Zero));                // 1 (guard fires)
fn check_osz_one()  : Nat = one_if_some_zero(m: Option.Some(Nat.Succ(Nat.Zero)));      // 0 (guard fails -> other)
fn check_osz_none() : Nat = one_if_some_zero(m: Option.None);                           // 0 (no ctor arm)

fn check_color_red()   : Nat = color_score(c: Red);    // 1
fn check_color_green() : Nat = color_score(c: Green);  // 0
fn check_color_blue()  : Nat = color_score(c: Blue);   // 0

fn check_describe_zero()  : Bool = describe(n: Nat.Zero);                               // False
fn check_describe_two()   : Bool = describe(n: Nat.Succ(Nat.Succ(Nat.Zero)));           // True (p == Succ(Zero))
fn check_describe_three() : Bool =
  describe(n: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))));                                   // False (guard fails)

fn main() : Bool = check_classify_one();
