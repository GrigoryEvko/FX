// User-defined enum with three nullary ctors (B9 ADT translation).
// Exercises: `type ... end type` decl → IndSpec registration,
// ctor construction at runtime, match compilation against a
// user spec, unqualified ctor reference (Red, Green, Blue).
type color
  Red;
  Green;
  Blue;
end type;

fn describe(c: color) : Nat = match c;
  Red   => Nat.Zero;
  Green => Nat.Succ(Nat.Zero);
  Blue  => Nat.Succ(Nat.Succ(Nat.Zero));
end match;

fn main() : Nat = describe(Blue);
