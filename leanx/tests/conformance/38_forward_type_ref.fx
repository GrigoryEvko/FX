// Q59: a fn signature can reference a type declared LATER in
// the same file.  Pre-Q59 this fired E001 "unknown identifier
// 'pair_t'" because the pass-1 loop in `checkFile` iterated
// decls in textual order — types only became visible in the
// globalEnv when their own loop iteration processed the
// typeDecl arm.  Post-Q59 `checkFile` runs a type-decl
// pre-pass that registers every typeDecl / sessionDecl before
// any fn signature elaborates, so the `fn pair_val() :
// pair_t` below sees `pair_t` already in the globalEnv despite
// appearing first.
//
// Matches the spec's implicit expectation — fns can forward-
// reference each other (§Q12 two-pass invariant), and types
// should behave the same way.  Without the pre-pass, users
// had to manually re-order decls with types first, which
// clashes with "code reads top-to-bottom like prose".
//
// Graduation: `fxi run` returns 2 (the `left` field of the
// constructed pair).
fn pair_val() : pair_t =
  pair_t { left: Nat.Succ(Nat.Succ(Nat.Zero)),
           right: Nat.Succ(Nat.Zero) };

type pair_t {
  left: Nat;
  right: Nat;
};

fn main() : Nat = pair_val().left;
