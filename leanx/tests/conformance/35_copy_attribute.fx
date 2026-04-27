// Q54: `@[copy]` attribute on a type decl.
//
// §7.8: a type marked `@[copy]` has all bindings at grade ω —
// the kernel's usage dimension (§6.3 dim 3, {0, 1, ω}) accepts
// multi-use without an explicit `ref` mode.  The elaborator
// detects the bare-var `copy` attribute in `parseTypeDecl`'s
// `attrs` array, propagates to `IndSpec.isCopy`, and the Q54
// `gradeForParam` helper upgrades `Grade.default` to
// `Grade.shared` at every parameter-binding site whose type
// resolves to a copy-marked `IndSpec`.
//
// Acceptance shape: a function takes a copy-marked type and
// references the parameter twice inside a block.  Without
// `@[copy]` (or a surface `ref`), this would fire M001.  The
// companion negative test lives in
// `tests/Tests/Elab/CopyGradeEndToEndTests.lean` — running the
// same source minus the attribute and asserting M001 fires.
@[copy]
type point
  Point(Nat);
end type;

fn deref(p: point) : Nat = match p;
  Point(inner) => inner;
end match;

fn deref_again(p: point) : Nat = match p;
  Point(inner) => inner;
end match;

fn use_twice(p: point) : Nat
begin fn
  let first  = deref(p);
  let second = deref_again(p);
  return Nat.Succ(Nat.Zero);
end fn;
