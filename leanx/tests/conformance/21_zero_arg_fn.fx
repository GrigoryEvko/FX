// Zero-parameter fn.  Exercises: R1's Unit-Pi desugaring (§31.7
// kernel translation — every 0-arg fn becomes
// `λ (_ :_ghost Unit). body : Π (_ :_ghost Unit) → T @ eff`),
// ensures the ghost Unit binder doesn't leak into the body's
// type-check.
fn pure_zero() : Nat = Nat.Zero;
