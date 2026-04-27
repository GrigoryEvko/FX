// Polymorphic identity.  Exercises: type param `<a: type>` at
// definition site, single-arg body via `= expr;` one-liner form.
fn identity<a: type>(x: a) : a = x;
