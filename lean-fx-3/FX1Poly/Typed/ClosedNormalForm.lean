import FX1Poly.Typed.ClosedConvDecision
import FX1Poly.Core.NormalizeMeta

/-! # FX1Poly/Typed/ClosedNormalForm
    — the canonical-NF EXTRACTION companion to the closed decidable-Conv DECISION lane

`ClosedConvDecision.lean` crossed the FT-derived SN lane into the conversion-DECISION lane
(`Conv.decidableOfStronglyNormalizing` — decide whether two closed FT-certified terms convert).  This file
ships the symmetric EXTRACTION half: from the same FT-derived SN, the normalizer (`RawTerm.normalize`, the
WN-grind spine) EXTRACTS the canonical normal form of a closed FT-certified term, with its full metatheory —
the term converts to it, it is structurally normal, and equality of canonical NFs is a COMPLETE invariant for
conversion.  This is the dependent-fragment twin of the simply-typed `SimplyTypedNormalForm.lean` extractor.

## The general extractor and the canonicity cherries

`closedNormalFormFromLevelIndexed` is the reusable extractor: any closed term with a level-indexed fundamental
conclusion (at a positive level) has a computable canonical normal form (`= RawTerm.normalize subject
<closed-SN>`).  `closedNormalForm_conv` / `closedNormalForm_isStepNormalForm` give its correctness (the term
converts to it; it is normal), and `closedConv_iff_normalForm_eq` is the complete-invariant characterization
(two closed FT-terms convert IFF their canonical NFs coincide — the equality behind the decision).  These are
CONDITIONAL on the FT conclusion, exactly like the `ClosedLevelIndexed.lean` / `ClosedConvDecision.lean`
handoffs, and become unconditional for every closed well-typed term once the `HasTypeDescPi.rec` assembly
supplies the conclusion.

`closedBetaRedexNormalForm_eq` is the UNCONDITIONAL canonicity cherry — and it is PROVEN, not merely decidable:
the closed β-redex `(λ (x : Type@e). x) (Type@e)` has canonical normal form EXACTLY its reduct `Type@e`.  The
proof is internals-independent — it routes through the complete invariant (`normalize_eq_iff_conv`) with the
genuine conversion `betaRedexConvertsToReduct` and the fixed-point law on the normal reduct
(`normalize_eq_self_of_isStepNormalForm`), never inspecting how the normalizer reduces.  `closedIdentityNormalForm_eq`
is the fixed-point companion: the closed identity `λ (x : Type@e). x` is already normal, so it is its own
canonical NF.

## Zero-axiom verification

Each declaration composes `RawTerm.normalize` / its metatheory with the already-gated FT-SN results and
`betaRedexConvertsToReduct`.  Leaf normality (`isStepNormalForm (universeCodeCell …)`, `isStepNormalForm
(lamCell (variableCell 0))`) is `rfl` (`isStepNormalFormBool` computes on a leaf).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Canonical-NF extractor for a closed FT-certified term.**  The closed term is strongly normalizing by the
closed-SN handoff, so the normalizer produces its canonical normal form.  Conditional on the level-indexed
fundamental conclusion (auto-upgrades to every closed well-typed term once the recursor lands).  The
extraction twin of `closedConvDecidableFromLevelIndexed` (which decides; this extracts). -/
def closedNormalFormFromLevelIndexed {profile : PolyProfile} (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (levelIndexedFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (predLevel + 1)
        (TypingContext.empty : TypingContext profile 0) subject classifier) :
    RawTerm 0 :=
  RawTerm.normalize subject
    (closedSubjectStronglyNormalizingFromLevelIndexed predLevel levelIndexedFundamental)

/-- **A closed FT-certified term converts to its canonical normal form.**  The normalizer's reduction chain
lifts to `Conv` (`RawTerm.conv_normalize`). -/
theorem closedNormalForm_conv {profile : PolyProfile} (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (levelIndexedFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (predLevel + 1)
        (TypingContext.empty : TypingContext profile 0) subject classifier) :
    Conv subject (closedNormalFormFromLevelIndexed predLevel levelIndexedFundamental) :=
  RawTerm.conv_normalize subject _

/-- **The canonical normal form is structurally normal.**  Directly `RawTerm.normalize_isStepNormalForm`. -/
theorem closedNormalForm_isStepNormalForm {profile : PolyProfile} (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (levelIndexedFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (predLevel + 1)
        (TypingContext.empty : TypingContext profile 0) subject classifier) :
    RawTerm.isStepNormalForm (closedNormalFormFromLevelIndexed predLevel levelIndexedFundamental) :=
  RawTerm.normalize_isStepNormalForm subject _

/-- **The canonical normal form is a COMPLETE conversion invariant.**  Two closed FT-certified terms convert
IFF their canonical normal forms coincide — the equality the decidable-Conv decision compares.  The extraction
twin of the decision: `closedConvDecidableFromLevelIndexed` decides this `↔`'s left side; here it is the
explicit biconditional over the extracted normal forms. -/
theorem closedConv_iff_normalForm_eq {profile : PolyProfile}
    (leftPredLevel rightPredLevel : Nat)
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    (leftFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (leftPredLevel + 1)
        (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier)
    (rightFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (rightPredLevel + 1)
        (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier) :
    Conv leftSubject rightSubject ↔
      closedNormalFormFromLevelIndexed leftPredLevel leftFundamental =
        closedNormalFormFromLevelIndexed rightPredLevel rightFundamental :=
  RawTerm.normalize_eq_iff_conv leftSubject rightSubject _ _

/-- **Canonicity cherry (PROVEN, not just decidable): the closed β-redex normalizes to its reduct.**  The
canonical normal form of `(λ (x : Type@e). x) (Type@e)` is EXACTLY `Type@e`.  Internals-independent: the
genuine conversion `betaRedexConvertsToReduct` feeds the complete invariant `normalize_eq_iff_conv`, equating
the redex's normal form with the reduct's, and the reduct `Type@e` is its own normal form
(`normalize_eq_self_of_isStepNormalForm`, leaf-normal by `rfl`).  The closed dependent fragment's first PROVEN
canonical-form computation — the redex's value is `Type@e`. -/
theorem closedBetaRedexNormalForm_eq {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.normalize
      (appCell (lamCell (universeCodeCell levelExpr.lsucc flag)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag) : RawTerm 0)
      (closedIdentityApplication_stronglyNormalizing (profile := profile) levelExpr flag) =
      universeCodeCell levelExpr flag := by
  have convFact :
      Conv
        (appCell (lamCell (universeCodeCell levelExpr.lsucc flag)
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell levelExpr flag) : RawTerm 0)
        (universeCodeCell levelExpr flag) :=
    betaRedexConvertsToReduct levelExpr flag
  rw [(RawTerm.normalize_eq_iff_conv
        (appCell (lamCell (universeCodeCell levelExpr.lsucc flag)
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell levelExpr flag))
        (universeCodeCell levelExpr flag)
        (closedIdentityApplication_stronglyNormalizing (profile := profile) levelExpr flag)
        (universeCode_stronglyNormalizing (profile := profile) levelExpr flag)).mp convFact]
  exact RawTerm.normalize_eq_self_of_isStepNormalForm (universeCodeCell levelExpr flag) _ rfl

/-- **Fixed-point companion: the closed identity is its own canonical NF.**  `λ (x : Type@e). x` is already
structurally normal, so the normalizer returns it unchanged (`normalize_eq_self_of_isStepNormalForm`,
leaf-normal by `rfl`). -/
theorem closedIdentityNormalForm_eq {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.normalize (lamCell (universeCodeCell levelExpr flag)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0)
      (closedIdentityOnUniverse_stronglyNormalizing (profile := profile) levelExpr flag) =
      lamCell (universeCodeCell levelExpr flag) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) :=
  RawTerm.normalize_eq_self_of_isStepNormalForm
    (lamCell (universeCodeCell levelExpr flag) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) _ rfl

end FX1Poly.Typed
