// Pattern match on Bool scrutinee.  Exercises: match over a
// two-constructor inductive, unused scrutinee binder (`_`).
fn negate(b: Bool) : Bool = match b;
  True  => Bool.False;
  False => Bool.True;
end match;
