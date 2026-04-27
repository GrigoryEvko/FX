// Q61: §4.2 dot-shorthand.  `.field` without a receiver is
// surface sugar for `fn(it) => it.field`, the canonical
// pipeline idiom per the spec:
//
//   users |> map(.name)           -- extract names
//         |> filter(.active)      -- keep active ones
//
// The elaborator requires an expected Pi-type from the
// callee's parameter so it knows what record to project
// from.  Here `apply_to_user` declares `f: user -> Nat`,
// and the call `apply_to_user(f: .age, ...)` threads the
// arrow `user -> Nat` into dot-shorthand elab; the elaborator
// looks up `user`'s spec, finds the `age` field, and builds
// `fn(it) => it.age` pointing at the right projection.
//
// Pre-Q61 the parser would fire P010 on the leading dot;
// post-Q61 both parser and elab accept.
type user {
  name: Nat;
  age:  Nat;
};

fn apply_to_user(f: user -> Nat, u: user) : Nat = f(u);

fn main() : Nat
begin fn
  let alice : user = user {
    name: Nat.Succ(Nat.Zero),
    age:  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))
  };
  let age_alice = apply_to_user(f: .age, u: alice);
  return age_alice;
end fn;
