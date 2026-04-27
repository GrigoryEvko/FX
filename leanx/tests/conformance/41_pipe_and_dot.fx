// Q62: `|>` pipe operator composed with §4.2 dot-shorthand.
//
// This is THE canonical FX pipeline idiom from §4.2:
//
//   let result = items
//     |> filter(.active and .age >= 18)
//     |> map(.name)
//     |> sort_by(.name)
//     |> take(100);
//
// The spec shows how pipe threads values through a chain of
// transforms and dot-shorthand extracts record fields without
// lambdas.  A minimal but faithful version here: thread a
// single `user` value through a pipe into a higher-order
// `apply_to_user` that takes `.age` as its function arg.
//
// Exercises three recent landings together:
//   * Q61 dot-shorthand in the named-arg position (`f: .age`)
//   * Q62 pipe desugar (prepends positional)
//   * Q62 NamedArgs: rewriting single positional to named when
//     there's exactly one unfilled parameter slot (§4.2 rule 5)
//
// Graduation: fxi run returns alice's age = 3.
type user {
  name: Nat;
  age:  Nat;
};

fn apply_to_user(u: user, f: user -> Nat) : Nat = f(u);

fn main() : Nat
begin fn
  let alice : user = user {
    name: Nat.Succ(Nat.Zero),
    age:  Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))
  };
  let result = alice |> apply_to_user(f: .age);
  return result;
end fn;
