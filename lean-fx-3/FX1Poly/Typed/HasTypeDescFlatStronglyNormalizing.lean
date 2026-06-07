import FX1Poly.Typed.HasTypeDescFlatSubjectReduction
import FX1Poly.Typed.HasTypeDescSubjectStronglyNormalizingNative

/-! # FX1Poly/Typed/HasTypeDescFlatStronglyNormalizing
    — strong normalization for the flat-former typing judgment (next #935 increment)

`HasTypeDescFlat` (the standalone flat-former engine, #934) types the non-dependent `[0,0]` type-code formers
`product` / `sum` / `either` / `arrow` / `equiv`.  After subject reduction (firing-45,
`HasTypeDescFlatSubjectReduction`), the next metatheory it needs is strong normalization: every
flat-formation-typed subject is strongly normalizing.  This file supplies it — the flat twin of
`HasTypeDesc.subjectStronglyNormalizingNative`.

## The proof reuses the shipped SN substrate verbatim

The cumulative engine's SN (`HasTypeDescSubjectStronglyNormalizingNative`) factors through a GENERIC accessibility
substrate (in `namespace FX1Poly.Core`): `formerCell_isStronglyNormalizing_of_accChildren` says a cell over a
CONGRUENCE-ONLY generator is SN once its child spine is accessible, and
`accStepChildrenSuccessor_of_allStronglyNormalizing` turns an all-children-SN spine into that accessibility.  The
ONLY generator-specific input is the congruence-only inversion — and the flat engine already has exactly that:
`flatFormerCellStepIsChildCongruence` (firing-45).  So flat-former SN is the same assembly with the flat
inversion swapped in — no new accessibility machinery, mirroring how the cumulative
`formerCellStronglyNormalizingOfChildren` routes through the cumulative `former_step_inv`.

The telescope half is even LIGHTER than the cumulative one: `FlatDescTelescope` is STANDALONE (not mutual with
`HasTypeDesc`), so `FlatDescTelescope.childrenStronglyNormalizing` is a plain structural recursion that calls the
already-proven `HasTypeDesc.subjectStronglyNormalizingNative` on each head — no mutual block (the cumulative
`DescTelescope.childrenStronglyNormalizingNative` needs the mutual `⋈` because its telescope IS mutual with the
subject judgment).

## The corpus

`HasTypeDescFlat.subjectStronglyNormalizing` is the headline; the five closed witnesses
(`productFlatTypeStronglyNormalizing` … `equivFlatTypeStronglyNormalizing`) instantiate it at each former's
formation smoke, so every flat former is demonstrated to type AND strongly normalize.

## Zero-axiom verification

`flatFormerCellStronglyNormalizingOfChildren` is a direct application of the shipped generic
`formerCell_isStronglyNormalizing_of_accChildren`.  `FlatDescTelescope.childrenStronglyNormalizing` is structural
`match`-recursion (`.nil` → `True.intro`, `.cons` → the anonymous-constructor pair).
`HasTypeDescFlat.subjectStronglyNormalizing` is a single-arm `cases derivation` (the `context` is the inductive's
auto-determined index — 8 bound fields, not 9).  The closed witnesses are direct applications.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **A flat-former cell with all children strongly normalizing is strongly normalizing.**  The flat twin of
`formerCellStronglyNormalizingOfChildren`: a flat former (`flatTypingRuleDescOf generator = some rule`) heads no
root redex (`flatFormerCellStepIsChildCongruence`), so every Step out of the cell is a child congruence; the cell
is therefore SN once its child spine is accessible, which all-children-SN supplies via the shipped
`accStepChildrenSuccessor_of_allStronglyNormalizing`.  Generic over the flat former — a future flat row extends it
with no change here, exactly as the cumulative former-SN routes through `former_step_inv`. -/
theorem flatFormerCellStronglyNormalizingOfChildren {scope : Nat} {generator : Generator}
    {rule : TypingRuleDesc} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule)
    (childrenSN : children.allStronglyNormalizing) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) :=
  formerCell_isStronglyNormalizing_of_accChildren
    (fun cellStep => flatFormerCellStepIsChildCongruence isFlatFormation cellStep)
    (accStepChildrenSuccessor_of_allStronglyNormalizing childrenSN)

/-- **Every child of a flat telescope is strongly normalizing.**  NOT mutual (`FlatDescTelescope` is standalone):
plain structural recursion calling the already-proven `HasTypeDesc.subjectStronglyNormalizingNative` on each head
typing, accumulating the tail recursively.  Lighter than the cumulative
`DescTelescope.childrenStronglyNormalizingNative`, which is mutual with the subject judgment. -/
theorem FlatDescTelescope.childrenStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    children.allStronglyNormalizing :=
  match telescope with
  | .nil => True.intro
  | .cons _head _headLevel _restLevels _rest headTyped restTyped =>
      ⟨HasTypeDesc.subjectStronglyNormalizingNative headTyped,
        FlatDescTelescope.childrenStronglyNormalizing restTyped⟩

/-- **★ Flat-former subject strong normalization.**  Every flat-formation-typed subject is strongly
normalizing — the flat-engine twin of `HasTypeDesc.subjectStronglyNormalizingNative`.  Cases the (single-
constructor) derivation; the subject is a flat-former cell, SN once its telescope children are SN
(`FlatDescTelescope.childrenStronglyNormalizing`), discharged by `flatFormerCellStronglyNormalizingOfChildren`.

The `cases derivation with | flatFormation generator payload children levels flag rule isFlat premise` binds the
constructor's 8 explicit fields; the `context` is the inductive's auto-determined INDEX and must NOT be bound. -/
theorem HasTypeDescFlat.subjectStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescFlat profile context subject classifier) :
    IsStronglyNormalizing subject := by
  cases derivation with
  | flatFormation generator payload children levels flag rule isFlat premise =>
      exact flatFormerCellStronglyNormalizingOfChildren isFlat
        (FlatDescTelescope.childrenStronglyNormalizing premise)

/-- Closed witness: `product (Type@0) (Type@0)` is strongly normalizing (the headline at the `productCode` smoke). -/
theorem productFlatTypeStronglyNormalizing (profile : PolyProfile) (flag : UniverseFlag) :
    IsStronglyNormalizing (RawTerm.mkGen .gen_productCode () (flatProductTypeZeroChildren flag)) :=
  HasTypeDescFlat.subjectStronglyNormalizing (productFlatFormationSmoke profile flag)

/-- Closed witness: `sum (Type@0) (Type@0)` is strongly normalizing. -/
theorem sumFlatTypeStronglyNormalizing (profile : PolyProfile) (flag : UniverseFlag) :
    IsStronglyNormalizing (RawTerm.mkGen .gen_sumCode () (flatProductTypeZeroChildren flag)) :=
  HasTypeDescFlat.subjectStronglyNormalizing (sumFlatFormationSmoke profile flag)

/-- Closed witness: `either (Type@0) (Type@0)` is strongly normalizing. -/
theorem eitherFlatTypeStronglyNormalizing (profile : PolyProfile) (flag : UniverseFlag) :
    IsStronglyNormalizing (RawTerm.mkGen .gen_eitherCode () (flatProductTypeZeroChildren flag)) :=
  HasTypeDescFlat.subjectStronglyNormalizing (eitherFlatFormationSmoke profile flag)

/-- Closed witness: `arrow (Type@0) (Type@0)` is strongly normalizing. -/
theorem arrowFlatTypeStronglyNormalizing (profile : PolyProfile) (flag : UniverseFlag) :
    IsStronglyNormalizing (RawTerm.mkGen .gen_arrowCode () (flatProductTypeZeroChildren flag)) :=
  HasTypeDescFlat.subjectStronglyNormalizing (arrowFlatFormationSmoke profile flag)

/-- Closed witness: `equiv (Type@0) (Type@0)` is strongly normalizing — completing the five-former flat SN corpus. -/
theorem equivFlatTypeStronglyNormalizing (profile : PolyProfile) (flag : UniverseFlag) :
    IsStronglyNormalizing (RawTerm.mkGen .gen_equivCode () (flatProductTypeZeroChildren flag)) :=
  HasTypeDescFlat.subjectStronglyNormalizing (equivFlatFormationSmoke profile flag)

end FX1Poly.Typed
