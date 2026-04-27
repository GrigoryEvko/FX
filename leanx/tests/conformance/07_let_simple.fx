// Plain let-binding.  Exercises: `let name = expr;` inside a
// block, scope threading from let to tail expression, begin/end
// body form.
fn compute(n: Nat) : Nat
begin fn
  let m = Nat.Succ(n);
  return m;
end fn;
