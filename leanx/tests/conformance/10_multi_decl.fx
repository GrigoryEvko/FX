// Two decls with cross-reference.  Exercises: two-pass elab
// (signatures registered pass 1, bodies checked pass 2 with
// full GlobalEnv), forward-ref via Term.const, rec fn calling
// non-rec fn.
fn plus_one(n: Nat) : Nat = Nat.Succ(n);

fn double_via_plus(n: Nat) : Nat = match n;
  Zero    => Nat.Zero;
  Succ(p) => plus_one(plus_one(double_via_plus(p)));
end match;
