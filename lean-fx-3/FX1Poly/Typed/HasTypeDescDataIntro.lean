import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.CellConstructors
import FX1Poly.Core.BoolCanonicalFormsCandidate

/-! # FX1Poly/Typed/HasTypeDescDataIntro — the standalone data-CONSTRUCTOR introduction judgment
    (DI-1: the nullary arm — `boolTrue` / `boolFalse : boolCode`).

The grown engine `HasTypeDescPi` is formation-only: it PROVES the data constructors UNTYPED
(`HasTypeDescPiDataHeadUntyped`, e.g. `boolTrue`/`boolFalse`/`pair`/`natZero` all have NO grown
typing).  To make typed canonicity ("closed `t : boolCode` reduces to `boolTrue` or `boolFalse`")
non-vacuous, the kernel must TYPE those constructors — and the cascade-free way to do that, per the
established `HasTypeDescFlat` precedent, is a SEPARATE standalone judgment that REFERENCES (never
extends) the existing engines.  This is that judgment's first brick.

`HasTypeDescDataIntro` is a brand-new relation — NOT mutual with, and NOT an arm of, `HasTypeDescPi`
— so it does not disturb `HasTypeDescPi`'s recursor or its data-head-untyped refutations: those stay
true (`boolTrue` is still untyped IN THE GROWN ENGINE).  Exactly as `HasTypeDescFlat` types
`product`-the-TYPE-former without invalidating `HasTypeDescPi.pairCellHasNoTyping`, this types
`boolTrue`-the-VALUE without invalidating `HasTypeDescPi.boolTrueCellHasNoTyping`.  The two are
different judgments about different things.

## The nullary arm

A NULLARY data constructor (`boolTrue`, `boolFalse`, and later `unit` / `natZero` / `listNil`) has no
children and a fixed output type-code (`boolCode`).  Its intro rule is therefore the simplest
possible — no premise telescope at all (lighter than `HasTypeDescFlat.flatFormation`, which still
carries a `FlatDescTelescope`).  Table-driven over `dataIntroNullaryRuleDescOf` (P13 cascade-freedom:
a new nullary constructor is ONE more table row, never a new arm).  The n-ary constructors (`pair`,
`eitherInl/Inr` — DI-2) and the recursive ones (`natSucc`, `listCons` — DI-3) get their own arms
carrying premise telescopes that type the children at their argument type-codes; `dataIntroNullary
RuleDescOf` is the NULLARY-only table (its rows are exactly the childless constructors).

## Zero-axiom

`dataIntroNullaryRuleDescOf` is a pure-syntax `Option` table (metadata lemmas `rfl` on the diagonal,
mirroring `flatTypingRuleDescOf_*`); the inductive is a single positive arm; the smokes are direct
`nullaryIntro` applications with `rfl` table lookups.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- An introduction-rule description for a NULLARY data constructor: the fixed output type-code (a
function of the scope), e.g. `boolTrue`/`boolFalse` both output `boolCode`.  Pure syntax (no
`HasTypeDescPi`), strictly positive, mirroring `TypingRuleDesc`. -/
structure DataIntroNullaryRuleDesc where
  outputTypeCode : (scope : Nat) → RawTerm scope

/-- The per-generator NULLARY data-constructor intro table.  Its rows are exactly the childless data
constructors (no premise telescope); `boolTrue` and `boolFalse` both introduce a member of `boolCode`.
A future nullary constructor (`unit` / `natZero` / `listNil`) is ONE more row, never a new arm. -/
def dataIntroNullaryRuleDescOf (generator : Generator) : Option DataIntroNullaryRuleDesc :=
  if generator = .gen_boolTrue then some { outputTypeCode := fun _ => boolTypeCell }
  else if generator = .gen_boolFalse then some { outputTypeCode := fun _ => boolTypeCell }
  else if generator = .gen_unit then some { outputTypeCode := fun _ => unitTypeCell }
  else none

/-- `gen_unit` introduces a member of `unitCode` (metadata check, `rfl` on the diagonal) — the unit
VALUE's intro row, ending `gen_unit`'s reserved status (the type whose unit-eta judgment collapses
all members to this one constructor). -/
theorem dataIntroNullaryRuleDescOf_unit :
    dataIntroNullaryRuleDescOf .gen_unit
      = some { outputTypeCode := fun _ => unitTypeCell } :=
  rfl

/-- `gen_boolTrue` introduces a member of `boolCode` (metadata check, `rfl` on the diagonal). -/
theorem dataIntroNullaryRuleDescOf_boolTrue :
    dataIntroNullaryRuleDescOf .gen_boolTrue
      = some { outputTypeCode := fun _ => boolTypeCell } := rfl

/-- `gen_boolFalse` introduces a member of `boolCode` (metadata check). -/
theorem dataIntroNullaryRuleDescOf_boolFalse :
    dataIntroNullaryRuleDescOf .gen_boolFalse
      = some { outputTypeCode := fun _ => boolTypeCell } := rfl

/-- **The data-constructor introduction judgment.**  A standalone layer (NOT mutual with / NOT an arm
of `HasTypeDescPi`, mirroring `HasTypeDescFlat`) typing the data VALUE constructors at their data
type-codes.  The nullary arm: a childless constructor in `dataIntroNullaryRuleDescOf` introduces a
member of its tabled output type-code — no premise (the n-ary/recursive arms, DI-2/DI-3, add premise
telescopes). -/
inductive HasTypeDescDataIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | nullaryIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (rule : DataIntroNullaryRuleDesc)
      (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
      HasTypeDescDataIntro profile context (.mkGen generator payload children)
        (rule.outputTypeCode scope)

/-- **★ `boolTrue : boolCode` in the data-intro engine.**  The Boolean `true` value-constructor is
TYPED at the `boolCode` data type — the value the grown engine proves untyped
(`HasTypeDescPi.boolTrueCellHasNoTyping`) now has a typing in the dedicated data-constructor judgment.
The first concrete brick toward non-vacuous bool canonicity. -/
theorem HasTypeDescDataIntro.boolTrueTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescDataIntro profile context boolTrueCell boolTypeCell :=
  HasTypeDescDataIntro.nullaryIntro context .gen_boolTrue () .childNil
    { outputTypeCode := fun _ => boolTypeCell } rfl

/-- **★ `unit : unitCode` in the data-intro engine.**  The ONE canonical inhabitant of the unit
type, typed at its code — the value half of the unit data story (the formation half is
`HasTypeDescBaseType.unitCodeTyped`); the substrate the typed unit-eta judgment collapses to. -/
theorem HasTypeDescDataIntro.unitValueTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescDataIntro profile context unitCell unitTypeCell :=
  HasTypeDescDataIntro.nullaryIntro context .gen_unit () .childNil
    { outputTypeCode := fun _ => unitTypeCell } rfl

/-- **★ `boolFalse : boolCode` in the data-intro engine.**  The `false` companion of `boolTrueTyped`;
together they are the two closed canonical members the bool-canonicity statement ranges over. -/
theorem HasTypeDescDataIntro.boolFalseTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescDataIntro profile context boolFalseCell boolTypeCell :=
  HasTypeDescDataIntro.nullaryIntro context .gen_boolFalse () .childNil
    { outputTypeCode := fun _ => boolTypeCell } rfl

/-- **Partition witness: `boolTrue` is NOT a grown FORMATION former.**  `typingRuleDescOf gen_boolTrue
= none` (it is a VALUE constructor, not a type-former), so the data-intro judgment's domain is disjoint
from the grown formation table — exactly as `typingRuleDescOf_productCode_none` partitions the flat
engine.  The data-intro judgment is the ONLY engine that types `boolTrue`. -/
theorem typingRuleDescOf_boolTrue_none :
    typingRuleDescOf .gen_boolTrue = none := rfl

end FX1Poly.Typed
