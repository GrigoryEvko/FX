import FX1Poly.Tier0.FxBaseSubstDisplayMap
import FX1Poly.Typed.HasTypeDescDecidable
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DisplayMapDecidableFibration
    — the Tm↠Ty display map's typed refinement is a DECIDABLE fibration (SN-086 payoff, #486)

`FX1Poly/Tier0/FxBaseSubstDisplayMap.lean` ships the raw cellular display map `displayClassifier :
Tm ↠ Ty` over the term-carrying base, with its comprehension pullback (representability in the
Natural-Model generalized-element sense).  This file adds the FX-specific content the #486 reading
names: **"representability = the decidable typing fibration — a term's type is computable."**

  * `ClassifiedCell.IsAdmittedByFormation` — the typed refinement of the display map's total space:
    a classified cell is admitted when the formation engine types its subject at its classifier
    (`HasTypeDesc Γ subject classifier`).
  * `ClassifiedCell.decideAdmittedByFormation` — ★ the decidable-fibration witness, the
    `memberDecidable`-shaped field of the display map (mirroring `MorphismClass.memberDecidable` in
    `fxBaseRMC`): membership in the typed refinement of every display fiber is DECIDABLE, via the
    shipped total formation-engine decider `HasTypeDesc.decidableOfWellFormed` (whose own docstring
    already carries the §5.2 "Natural-Model display map" reading).
  * `displayFiberTypedMembershipDecidable` — the same witness phrased fiberwise: for a fixed type
    cell, whether a subject lies in the TYPED fiber over it is decidable.
  * `classifiedCellOfTyping` + `displayClassifier_classifiedCellOfTyping` — every grown-engine
    typing derivation is literally a point of `Tm`, and the display map sends it to its classifier
    ("a term goes to its type" made literal, `rfl`).
  * `genericClassifiedCell_admittedByFormation` / `_admittedByGrown` — NON-VACUITY: the comprehension
    pullback's generic element (fresh variable over the weakened type) is genuinely typed by both
    engines over the extended context — `HasTypeDesc.var` + `lookup_cons_zero` (definitional) +
    the SUBSTVEC-3 deep coherence `weakening_subst_eq_rename` aligning the categorical weakening
    SUBSTITUTION with the typing context's weakening RENAMING.

## Honest scope boundary

This is the CATEGORICAL VIEW of the shipped decidable checker, not a new decidability result: the
fibration's decidable lift IS `HasTypeDesc.decidableOfWellFormed` (#461/#303), repackaged at
the display-map interface.  The decider is the FORMATION engine's (total); the GROWN engine's
checking stays bidirectional (per-head combinators `HasTypeDescPi.decidableCheck*` — a bare Curry λ
has no unique type, so no total grown decider exists; see `HasTypeDescPiCheckOfInferred`).

## Zero-axiom verification

Definitions + direct applications of the shipped decider, the `var` rule (with `lookup_cons_zero`
definitional), `weakening_subst_eq_rename`, and `HasTypeDescPi.ofFormation`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0

/-- **The typed refinement of the display map's total space.**  A classified cell is admitted when
the formation engine types its subject at its classifier — the judgmental gate over the raw `Tm`. -/
def _root_.FX1Poly.Tier0.ClassifiedCell.IsAdmittedByFormation (profile : PolyProfile)
    {scope : Nat} (context : TypingContext profile scope) (cell : ClassifiedCell scope) : Prop :=
  HasTypeDesc profile context cell.subjectCell cell.classifierCell

/-- ★ **The decidable-fibration witness** — the `memberDecidable`-shaped field of the display map:
membership in the typed refinement of every display fiber is decidable, via the shipped total
formation-engine decider.  The categorical reading of decidable typing (#486); honestly a
repackaging of `HasTypeDesc.decidableOfWellFormed`, not a new decidability result. -/
def _root_.FX1Poly.Tier0.ClassifiedCell.decideAdmittedByFormation {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContextDesc context) (cell : ClassifiedCell scope) :
    Decidable (cell.IsAdmittedByFormation profile context) :=
  HasTypeDesc.decidableOfWellFormed wellFormed cell.subjectCell cell.classifierCell

/-- The decidable-fibration witness phrased FIBERWISE: for a fixed type cell, whether a subject lies
in the typed fiber of the display map over it is decidable. -/
def displayFiberTypedMembershipDecidable {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContextDesc context) (typeCell subject : RawTerm scope) :
    Decidable ((ClassifiedCell.mk subject typeCell).IsAdmittedByFormation profile context) :=
  ClassifiedCell.decideAdmittedByFormation wellFormed (ClassifiedCell.mk subject typeCell)

/-- Every grown-engine typing derivation is a point of the `Tm` family: the classified cell pairing
the derivation's subject with its classifier. -/
def classifiedCellOfTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (_typed : HasTypeDescPi profile context subject classifier) : ClassifiedCell scope :=
  { subjectCell := subject, classifierCell := classifier }

/-- The display map sends a typed term's cell to its classifier — "a term goes to its type" made
literal (`rfl`). -/
theorem displayClassifier_classifiedCellOfTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    displayClassifier.component scope (classifiedCellOfTyping typed) = classifier := rfl

/-- **Non-vacuity of the comprehension's generic element**: over the context extended by `typeCell`,
the generic classified cell (fresh variable over the weakened type) is genuinely typed by the
formation engine.  The `var` rule's classifier `lookup ⟨0,_⟩ = rename weaken typeCell` (definitional)
meets the categorical weakening through the SUBSTVEC-3 deep coherence `weakening_subst_eq_rename`. -/
theorem genericClassifiedCell_admittedByFormation (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (typeCell : RawTerm scope) :
    (genericClassifiedCell typeCell).IsAdmittedByFormation profile (context.cons typeCell) := by
  show HasTypeDesc profile (context.cons typeCell)
    (RawTerm.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
    (RawTerm.subst (SubstVec.weakening scope).toRawTermSubst typeCell)
  rw [SubstVec.weakening_subst_eq_rename]
  exact HasTypeDesc.var (context.cons typeCell) ⟨0, Nat.succ_pos scope⟩

/-- The generic classified cell is typed by the GROWN engine as well (`ofFormation`). -/
theorem genericClassifiedCell_admittedByGrown (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (typeCell : RawTerm scope) :
    HasTypeDescPi profile (context.cons typeCell)
      (genericClassifiedCell typeCell).subjectCell
      (genericClassifiedCell typeCell).classifierCell :=
  HasTypeDescPi.ofFormation
    (genericClassifiedCell_admittedByFormation profile context typeCell)

end FX1Poly.Typed
