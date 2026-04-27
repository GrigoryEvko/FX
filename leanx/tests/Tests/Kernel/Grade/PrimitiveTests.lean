import FX.Kernel.Inductive

/-!
# Primitive-type prelude registration tests (D2)

Compile-time assertions that every §3.1 primitive type is
registered in `FX.Kernel.Inductive.preludeSpecs` and resolves
via `specByName?`.  A failed test here means the prelude
dropped a primitive that the surface grammar expects — e.g.,
adding `u8` is a compile-time ratchet that these examples pin.

Structure: one `example` per primitive name, asserting
`knownName` returns `true`, plus one `example` per category
asserting the ctor list is empty (the §3.1 phase-2 rendering
as opaque refinement aliases without exposed constructors).

Reference: `fx_design.md` §3.1 Primitive Types, plus
`FX/Kernel/Inductive.lean`'s `primitiveNumericNames` docstring
for the Phase-2 scope caveat (no literal construction until
refinement types land in Stream E).
-/

namespace Tests.Kernel.Grade.Primitive

open FX.Kernel

/-! ## Signed fixed-width integers (§3.1 row 1) -/

example : Inductive.knownName "i8"    = true := by decide
example : Inductive.knownName "i16"   = true := by decide
example : Inductive.knownName "i32"   = true := by decide
example : Inductive.knownName "i64"   = true := by decide
example : Inductive.knownName "i128"  = true := by decide
example : Inductive.knownName "i256"  = true := by decide
example : Inductive.knownName "i512"  = true := by decide
example : Inductive.knownName "i1024" = true := by decide

/-! ## Unsigned fixed-width integers (§3.1 row 2) -/

example : Inductive.knownName "u8"    = true := by decide
example : Inductive.knownName "u16"   = true := by decide
example : Inductive.knownName "u32"   = true := by decide
example : Inductive.knownName "u64"   = true := by decide
example : Inductive.knownName "u128"  = true := by decide
example : Inductive.knownName "u256"  = true := by decide
example : Inductive.knownName "u512"  = true := by decide
example : Inductive.knownName "u1024" = true := by decide

/-! ## Platform pointer widths (§3.1 row 3) -/

example : Inductive.knownName "isize" = true := by decide
example : Inductive.knownName "usize" = true := by decide

/-! ## Arbitrary-precision + lowercase-nat-alias (§3.1 rows 4, 5) -/

example : Inductive.knownName "int" = true := by decide
example : Inductive.knownName "nat" = true := by decide
-- Capital-N Nat stays the inductive used for literal elaboration.
example : Inductive.knownName "Nat" = true := by decide

/-! ## Character and string (§3.1 rows 6, 7) -/

example : Inductive.knownName "char"   = true := by decide
example : Inductive.knownName "string" = true := by decide

/-! ## Exact decimals (§3.1 row 8) -/

example : Inductive.knownName "decimal" = true := by decide
example : Inductive.knownName "dec32"   = true := by decide
example : Inductive.knownName "dec64"   = true := by decide
example : Inductive.knownName "dec96"   = true := by decide
example : Inductive.knownName "dec128"  = true := by decide
example : Inductive.knownName "dec256"  = true := by decide
example : Inductive.knownName "dec512"  = true := by decide
example : Inductive.knownName "dec1024" = true := by decide

/-! ## Exact fractions (§3.1 row 9) -/

example : Inductive.knownName "frac"    = true := by decide
example : Inductive.knownName "frac64"  = true := by decide
example : Inductive.knownName "frac128" = true := by decide
example : Inductive.knownName "frac256" = true := by decide

/-! ## IEEE 754 floats (§3.1 row 10) -/

example : Inductive.knownName "f32" = true := by decide
example : Inductive.knownName "f64" = true := by decide

/-! ## Shape contract — every primitive is a zero-ctor IndSpec

Primitive types in Phase-2 carry zero constructors: they are
opaque type-level tokens that refinement types will give
structure in Stream E.  Pinning the empty ctor list guards
against accidental "add a Zero ctor to i64" drift. -/

example :
    (Inductive.specByName? "i64").map (·.ctors.length) = some 0 := by decide

example :
    (Inductive.specByName? "u8").map (·.ctors.length) = some 0 := by decide

example :
    (Inductive.specByName? "char").map (·.ctors.length) = some 0 := by decide

example :
    (Inductive.specByName? "string").map (·.ctors.length) = some 0 := by decide

example :
    (Inductive.specByName? "f64").map (·.ctors.length) = some 0 := by decide

/-! ## Pre-existing prelude specs keep their constructor content

Regression check: adding primitives must NOT bleed into Bool /
Nat / Unit / Empty.  These keep their known ctor counts. -/

example :
    (Inductive.specByName? "Bool").map (·.ctors.length) = some 2 := by decide

example :
    (Inductive.specByName? "Nat").map (·.ctors.length) = some 2 := by decide

example :
    (Inductive.specByName? "Unit").map (·.ctors.length) = some 1 := by decide

example :
    (Inductive.specByName? "Empty").map (·.ctors.length) = some 0 := by decide

/-! ## Non-primitive names stay unresolved

Names that should NOT be in the prelude: guard against
accidental typo-promoted entries. -/

example : Inductive.knownName "i7" = false := by decide
example : Inductive.knownName "u33" = false := by decide
example : Inductive.knownName "double" = false := by decide
example : Inductive.knownName "uint" = false := by decide
example : Inductive.knownName "word" = false := by decide

/-! ## Primitive count stability

`primitiveNumericNames` has a specific length — if it changes
unexpectedly (a primitive gets added or removed), this test
flags the drift loudly. -/

example : Inductive.primitiveNumericNames.length = 36 := by decide

/-! ## Strict positivity passes trivially

Zero-ctor specs have no constructor args to inspect, so strict
positivity is vacuously satisfied.  Compile-time `native_decide`
catch: if anyone refactors `StrictPositivity.isSatisfied` to
return `false` on empty ctor lists, this test flags the
regression. -/

example :
    (Inductive.specByName? "i64").all StrictPositivity.isSatisfied = true := by
  native_decide

example :
    (Inductive.specByName? "u8").all StrictPositivity.isSatisfied = true := by
  native_decide

example :
    (Inductive.specByName? "decimal").all StrictPositivity.isSatisfied = true := by
  native_decide

end Tests.Kernel.Grade.Primitive
