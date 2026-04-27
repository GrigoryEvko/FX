// If/else expression.  Exercises: `if cond; then else ... end if`
// tail-expression position (no trailing ;), Bool condition,
// both branches same type.
fn choose(flag: Bool, a: Nat, b: Nat) : Nat =
  if flag; a else b end if;
