import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Representation — layout-exposure chain semiring

`RepresentationGrade` tracks how much representation/layout detail a
value is allowed to expose.  The chain runs from native layout, the
most restrictive representation, to fully transparent representation.
This is encoded as an exposure debt so smaller means more restrictive:

```text
native < cLayout < packed < bigEndian < transparent
```

This orientation matches the `GradeSemiring` convention that `0` is
the restrictive bottom and `1` is the permissive top:

* `0` = `native` — no representation exposure
* `1` = `transparent` — maximum representation exposure
* `+` = max/more exposed representation
* `*` = min/layout scaling, with native annihilating
* `≤` = exposure order, so less exposed representation fits where more
  exposed representation is allowed

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Representation grade: five-step layout-exposure chain. -/
inductive RepresentationGrade : Type
  /-- Native layout; lattice bottom; no representation exposure. -/
  | native
  /-- C-compatible layout exposure. -/
  | cLayout
  /-- Packed layout exposure. -/
  | packed
  /-- Big-endian layout exposure. -/
  | bigEndian
  /-- Transparent representation; lattice top; maximum exposure. -/
  | transparent
  deriving DecidableEq, Repr

namespace RepresentationGrade

/-- Combining representation grades keeps the more exposed layout. -/
def add : RepresentationGrade → RepresentationGrade → RepresentationGrade
  | .native, rightOperand => rightOperand
  | .cLayout, .native => .cLayout
  | .cLayout, .cLayout => .cLayout
  | .cLayout, .packed => .packed
  | .cLayout, .bigEndian => .bigEndian
  | .cLayout, .transparent => .transparent
  | .packed, .native => .packed
  | .packed, .cLayout => .packed
  | .packed, .packed => .packed
  | .packed, .bigEndian => .bigEndian
  | .packed, .transparent => .transparent
  | .bigEndian, .native => .bigEndian
  | .bigEndian, .cLayout => .bigEndian
  | .bigEndian, .packed => .bigEndian
  | .bigEndian, .bigEndian => .bigEndian
  | .bigEndian, .transparent => .transparent
  | .transparent, .native => .transparent
  | .transparent, .cLayout => .transparent
  | .transparent, .packed => .transparent
  | .transparent, .bigEndian => .transparent
  | .transparent, .transparent => .transparent

/-- Sequential representation scaling keeps the less exposed layout;
`native` annihilates and `transparent` is the identity. -/
def mul : RepresentationGrade → RepresentationGrade → RepresentationGrade
  | .native, .native => .native
  | .native, .cLayout => .native
  | .native, .packed => .native
  | .native, .bigEndian => .native
  | .native, .transparent => .native
  | .cLayout, .native => .native
  | .cLayout, .cLayout => .cLayout
  | .cLayout, .packed => .cLayout
  | .cLayout, .bigEndian => .cLayout
  | .cLayout, .transparent => .cLayout
  | .packed, .native => .native
  | .packed, .cLayout => .cLayout
  | .packed, .packed => .packed
  | .packed, .bigEndian => .packed
  | .packed, .transparent => .packed
  | .bigEndian, .native => .native
  | .bigEndian, .cLayout => .cLayout
  | .bigEndian, .packed => .packed
  | .bigEndian, .bigEndian => .bigEndian
  | .bigEndian, .transparent => .bigEndian
  | .transparent, .native => .native
  | .transparent, .cLayout => .cLayout
  | .transparent, .packed => .packed
  | .transparent, .bigEndian => .bigEndian
  | .transparent, .transparent => .transparent

/-- Representation subsumption: less exposed layout fits where more
exposed layout is allowed. -/
def le : RepresentationGrade → RepresentationGrade → Prop
  | .native, .native => True
  | .native, .cLayout => True
  | .native, .packed => True
  | .native, .bigEndian => True
  | .native, .transparent => True
  | .cLayout, .native => False
  | .cLayout, .cLayout => True
  | .cLayout, .packed => True
  | .cLayout, .bigEndian => True
  | .cLayout, .transparent => True
  | .packed, .native => False
  | .packed, .cLayout => False
  | .packed, .packed => True
  | .packed, .bigEndian => True
  | .packed, .transparent => True
  | .bigEndian, .native => False
  | .bigEndian, .cLayout => False
  | .bigEndian, .packed => False
  | .bigEndian, .bigEndian => True
  | .bigEndian, .transparent => True
  | .transparent, .native => False
  | .transparent, .cLayout => False
  | .transparent, .packed => False
  | .transparent, .bigEndian => False
  | .transparent, .transparent => True

end RepresentationGrade

/-- Representation grades form the five-element chain lattice semiring.
The proof fields are closed finite case analyses over the enum. -/
instance : GradeSemiring RepresentationGrade where
  zero := .native
  one  := .transparent
  add  := RepresentationGrade.add
  mul  := RepresentationGrade.mul
  le   := RepresentationGrade.le

  add_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl

  add_comm := by
    intro first second
    cases first <;> cases second <;> rfl

  add_zero_left := by
    intro value
    cases value <;> rfl

  add_zero_right := by
    intro value
    cases value <;> rfl

  mul_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl

  mul_one_left := by
    intro value
    cases value <;> rfl

  mul_one_right := by
    intro value
    cases value <;> rfl

  mul_distrib_left := by
    intro scalar leftAddend rightAddend
    cases scalar <;> cases leftAddend <;> cases rightAddend <;> rfl

  mul_distrib_right := by
    intro leftAddend rightAddend scalar
    cases leftAddend <;> cases rightAddend <;> cases scalar <;> rfl

  mul_zero_left := by
    intro value
    cases value <;> rfl

  mul_zero_right := by
    intro value
    cases value <;> rfl

  le_refl := by
    intro value
    cases value <;> exact True.intro

  le_trans := by
    intro first second third firstLeSecond secondLeThird
    cases first <;> cases second <;> cases third <;>
      first | exact True.intro | contradiction

  add_mono := by
    intro leftLow leftHigh rightLow rightHigh leftLeq rightLeq
    cases leftLow <;> cases leftHigh <;> cases rightLow <;> cases rightHigh <;>
      first | exact True.intro | contradiction

  mul_mono := by
    intro leftLow leftHigh rightLow rightHigh leftLeq rightLeq
    cases leftLow <;> cases leftHigh <;> cases rightLow <;> cases rightHigh <;>
      first | exact True.intro | contradiction

/-! ## Smoke samples -/

/-- Combining native layout with transparent layout keeps transparent
representation exposure. -/
example :
    RepresentationGrade.add .native .transparent = .transparent := rfl

/-- Sequential scaling by native annihilates representation exposure. -/
example :
    RepresentationGrade.mul .native .transparent = .native := rfl

/-- Native layout fits where transparent layout is allowed. -/
example :
    RepresentationGrade.le .native .transparent := True.intro

/-- Transparent layout does not fit where native layout is required. -/
example :
    ¬ RepresentationGrade.le .transparent .native :=
  fun impossibleRepresentation => impossibleRepresentation.elim

end LeanFX2.Graded.Instances
