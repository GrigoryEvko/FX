// Type parameter at a fn definition.  Exercises: `<a: type>` at
// binder site, ghost-grade binder injection, body using the
// type parameter as a type annotation on a let-binding (T045
// demands either explicit type or synthesis-mode RHS — we
// ascribe the binding).
fn wrap<a: type>(x: a) : a
begin fn
  let y : a = x;
  return y;
end fn;
