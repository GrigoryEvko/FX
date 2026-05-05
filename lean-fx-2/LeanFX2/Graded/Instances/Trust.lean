import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Trust — trust-debt lattice semiring

`TrustGrade` tracks the trust status of a value or proof artifact.
The order is a five-element chain from fully checked to least trusted:

```text
verified < reviewed < tested < assumed < external
```

This orientation matches the `GradeSemiring` convention that `0` is
the restrictive bottom and `1` is the permissive top:

* `0` = `verified` — no trust debt
* `1` = `external` — maximum trust debt
* `+` = max/worst trust debt
* `*` = min/trust-debt scaling, with verified annihilating
* `≤` = chain order, so better trust fits where worse trust is allowed

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Trust grade: five-step trust-debt chain. -/
inductive TrustGrade : Type
  /-- Fully checked by the kernel; lattice bottom; no trust debt. -/
  | verified
  /-- Human or agent review accepted the artifact. -/
  | reviewed
  /-- Checked by tests but not fully reviewed. -/
  | tested
  /-- Assumed locally; must not be treated as a proof. -/
  | assumed
  /-- External or unchecked artifact; lattice top; maximum trust debt. -/
  | external
  deriving DecidableEq, Repr

namespace TrustGrade

/-- Combining trust grades keeps the worse trust debt. -/
def add : TrustGrade → TrustGrade → TrustGrade
  | .verified, rightOperand => rightOperand
  | .reviewed, .verified => .reviewed
  | .reviewed, .reviewed => .reviewed
  | .reviewed, .tested => .tested
  | .reviewed, .assumed => .assumed
  | .reviewed, .external => .external
  | .tested, .verified => .tested
  | .tested, .reviewed => .tested
  | .tested, .tested => .tested
  | .tested, .assumed => .assumed
  | .tested, .external => .external
  | .assumed, .verified => .assumed
  | .assumed, .reviewed => .assumed
  | .assumed, .tested => .assumed
  | .assumed, .assumed => .assumed
  | .assumed, .external => .external
  | .external, .verified => .external
  | .external, .reviewed => .external
  | .external, .tested => .external
  | .external, .assumed => .external
  | .external, .external => .external

/-- Sequential trust scaling keeps the better of the two trust debts;
`verified` annihilates and `external` is the identity. -/
def mul : TrustGrade → TrustGrade → TrustGrade
  | .verified, .verified => .verified
  | .verified, .reviewed => .verified
  | .verified, .tested => .verified
  | .verified, .assumed => .verified
  | .verified, .external => .verified
  | .reviewed, .verified => .verified
  | .reviewed, .reviewed => .reviewed
  | .reviewed, .tested => .reviewed
  | .reviewed, .assumed => .reviewed
  | .reviewed, .external => .reviewed
  | .tested, .verified => .verified
  | .tested, .reviewed => .reviewed
  | .tested, .tested => .tested
  | .tested, .assumed => .tested
  | .tested, .external => .tested
  | .assumed, .verified => .verified
  | .assumed, .reviewed => .reviewed
  | .assumed, .tested => .tested
  | .assumed, .assumed => .assumed
  | .assumed, .external => .assumed
  | .external, .verified => .verified
  | .external, .reviewed => .reviewed
  | .external, .tested => .tested
  | .external, .assumed => .assumed
  | .external, .external => .external

/-- Trust subsumption: better trust fits where worse trust is allowed. -/
def le : TrustGrade → TrustGrade → Prop
  | .verified, .verified => True
  | .verified, .reviewed => True
  | .verified, .tested => True
  | .verified, .assumed => True
  | .verified, .external => True
  | .reviewed, .verified => False
  | .reviewed, .reviewed => True
  | .reviewed, .tested => True
  | .reviewed, .assumed => True
  | .reviewed, .external => True
  | .tested, .verified => False
  | .tested, .reviewed => False
  | .tested, .tested => True
  | .tested, .assumed => True
  | .tested, .external => True
  | .assumed, .verified => False
  | .assumed, .reviewed => False
  | .assumed, .tested => False
  | .assumed, .assumed => True
  | .assumed, .external => True
  | .external, .verified => False
  | .external, .reviewed => False
  | .external, .tested => False
  | .external, .assumed => False
  | .external, .external => True

end TrustGrade

/-- Trust grades form the five-element chain lattice semiring.
The proof fields are closed finite case analyses over the enum. -/
instance : GradeSemiring TrustGrade where
  zero := .verified
  one  := .external
  add  := TrustGrade.add
  mul  := TrustGrade.mul
  le   := TrustGrade.le

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

/-- Combining a verified artifact with an external artifact keeps the
external trust debt. -/
example :
    TrustGrade.add .verified .external = .external := rfl

/-- Sequential scaling by verified annihilates trust debt. -/
example :
    TrustGrade.mul .verified .external = .verified := rfl

/-- Fully verified artifacts fit where external artifacts are allowed. -/
example :
    TrustGrade.le .verified .external := True.intro

/-- External artifacts do not fit where verified artifacts are required. -/
example :
    ¬ TrustGrade.le .external .verified :=
  fun impossibleTrust => impossibleTrust.elim

end LeanFX2.Graded.Instances
