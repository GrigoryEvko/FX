// Q63: logical `not`/`and`/`or` keywords per §2.6.
//
// Per spec: "Logical use keywords: `not` prefix, `and`/`or`
// infix (keywords, NOT symbols — there are no `!`, `&&`, `||`
// tokens)."  Pre-Q63 the parser's top-of-file docstring
// explicitly deferred these.
//
// Implementation: parser-level desugar to Expr.ifExpr.  No
// elab changes — B6's ifExpr pathway handles the result:
//
//   not x     -> if x then Bool.False else Bool.True
//   a and b   -> if a then b else Bool.False
//   a or b    -> if a then Bool.True else b
//
// Precedence (tightest to loosest): `not` > comparison > `and`
// > `or` > `->`.  So `a < b and c < d` parses as `(a < b) and
// (c < d)`; `a and b or c` parses as `(a and b) or c`.
//
// Graduation: fxi run reports every truth-table case correctly.
fn not_true()   : Bool = not Bool.True;
fn not_false()  : Bool = not Bool.False;

fn and_tt() : Bool = Bool.True  and Bool.True;
fn and_tf() : Bool = Bool.True  and Bool.False;
fn and_ft() : Bool = Bool.False and Bool.True;
fn and_ff() : Bool = Bool.False and Bool.False;

fn or_tt()  : Bool = Bool.True  or Bool.True;
fn or_tf()  : Bool = Bool.True  or Bool.False;
fn or_ft()  : Bool = Bool.False or Bool.True;
fn or_ff()  : Bool = Bool.False or Bool.False;

// `and` binds tighter than `or`: False or True and True
// parses as `False or (True and True)` = True.
fn precedence_check() : Bool =
  Bool.False or Bool.True and Bool.True;

// `not` binds tighter than `and`: not False and True
// parses as `(not False) and True` = True.
fn not_then_and() : Bool = not Bool.False and Bool.True;

fn main() : Bool =
  not (Bool.False and (Bool.True or Bool.False));
