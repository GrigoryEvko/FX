// Record literal construction + field access (B8 landing).
// Exercises:
//   * `type point { x: Nat; y: Nat };` — record decl compiles
//     to an IndSpec with a single constructor whose `argNames`
//     match the surface field names.
//   * `point { x: ..., y: ... }` — record literal parses as an
//     Expr.app with named args; MatchHelpers.resolveCtorRef?
//     routes the `point` head to the spec's sole ctor; named
//     args reorder to positional via the ctor's argNames.
//   * `p.x` — field projection compiles to indRec on the
//     single-ctor motive, extracting the named field by
//     positional index.
type point {
  x: Nat;
  y: Nat;
};

fn origin() : point =
  point { x: Nat.Succ(Nat.Succ(Nat.Zero)), y: Nat.Succ(Nat.Zero) };

fn get_x(p: point) : Nat = p.x;

fn main() : Nat = get_x(origin());
