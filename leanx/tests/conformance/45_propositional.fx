// Q67: §2.6 propositional operators `==>` (implies) and
// `<==>` (iff).  Both elaborate to short-circuit `indRec
// "Bool"` shapes — see `logicalImplies` / `logicalIff` cases
// in `FX/Elab/Elaborate.lean`.
//
// Precedence (tightest to loosest):
//
//   not > comparison > is > and > or > arrow > pipe > implies > iff
//
// So `a and b ==> c or d` parses as `(a and b) ==> (c or d)`,
// and `a ==> b ==> c` parses as `a ==> (b ==> c)` (implies is
// right-associative).  `<==>` is non-chained (P042).
//
// Graduation: `main` exercises the classical-logic tautology
// `(a ==> b) <==> (not a or b)` — should evaluate to True for
// every Bool assignment.  Here we fix `a = True, b = False`:
//
//   (True ==> False) <==> (not True or False)
//      = False       <==>  False
//      = True
fn impl_tt() : Bool = Bool.True  ==> Bool.True;
fn impl_tf() : Bool = Bool.True  ==> Bool.False;
fn impl_ft() : Bool = Bool.False ==> Bool.True;
fn impl_ff() : Bool = Bool.False ==> Bool.False;

fn iff_tt() : Bool = Bool.True  <==> Bool.True;
fn iff_tf() : Bool = Bool.True  <==> Bool.False;
fn iff_ft() : Bool = Bool.False <==> Bool.True;
fn iff_ff() : Bool = Bool.False <==> Bool.False;

// Classical tautology `(a ==> b) <==> (not a or b)` — verify
// one assignment.  Full truth-table coverage is via the
// eight atomic fns above.
fn classical_tautology() : Bool =
  (Bool.True ==> Bool.False) <==> (not Bool.True or Bool.False);

// Chain: `a ==> b ==> c` = `a ==> (b ==> c)` (right-assoc).
// With a=True, b=True, c=False: True ==> (True ==> False)
// = True ==> False = False.
fn implies_chain() : Bool =
  Bool.True ==> Bool.True ==> Bool.False;

fn main() : Bool = classical_tautology();
