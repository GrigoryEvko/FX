import FX1Poly.Typed.ClosedSNSmoke
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/ClosedConvDecision
    — the first lane crossing: FT-derived strong normalization feeds the SN-fragment conversion decider

The level-indexed fundamental theorem (Route 2, the Tait reducibility lane) delivers strong
normalization — and `ClosedSNSmoke.lean` ships UNCONDITIONAL `IsStronglyNormalizing` results for
concrete closed terms (a universe code, a Π type code, the identity function, a β-redex) by composing the FT
arms at the empty context.  The payoff of strong normalization is DECIDABLE CONVERSION: the normalizer spine
(`FX1Poly/Core/Normalize.lean`) ships `Conv.decidableOfStronglyNormalizing` — given `IsStronglyNormalizing`
witnesses for two terms, it normalizes each and compares the normal forms, yielding `Decidable (Conv _ _)`
with no `Normalizer` structure and no global-confluence hypothesis.

This file CROSSES those two lanes for the first time.  The FT-derived SN results discharge the decider's SN
hypotheses, producing UNCONDITIONAL decidable conversion for concrete closed terms — including ones with a
LAMBDA, a BOUND VARIABLE, and a β-REDEX (`decidableConvBetaRedexAndReduct`, `decidableConvBetaRedexAndIdentity`).
It is the concrete, FT-certified realization of the raw-layer decidable-`Conv` milestone (#267 / #503): the SN
work is not academic — it directly makes conversion decidable, and here it is, hypothesis-free, on real terms.

## The general bridge and non-vacuity

`closedConvDecidableFromLevelIndexed` is the reusable structural lemma: ANY two closed terms each carrying a
level-indexed fundamental conclusion (at a positive level) have decidable conversion.  It is stated CONDITIONAL
on those fundamental conclusions (exactly as the `ClosedLevelIndexed.lean` handoffs are), and becomes "every
closed well-typed term pair has decidable `Conv`" the moment the `HasTypeDescPi.rec` assembly supplies them.
The concrete corollaries instantiate it (transitively) at the FT arms shipped in `ClosedSNSmoke.lean`.

`betaRedexConvertsToReduct` proves the decider is NOT classifying a vacuity: the closed β-redex
`(λ (x : Type@e). x) (Type@e)` genuinely CONVERTS to its reduct `Type@e` (one `Step.beta`, with
`subst0 (variableCell 0) (Type@e)` reducing definitionally to `Type@e`), so `decidableConvBetaRedexAndReduct`
decides a pair that really is convertible — the conversion decision does real work.

## Zero-axiom verification

Each declaration composes `Conv.decidableOfStronglyNormalizing` / `Conv.fromStep` with the already-gated
FT-SN results and `Step.beta`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The lane-crossing bridge: FT-certified closed terms have decidable conversion.**  Two closed terms, each
carrying a level-indexed fundamental conclusion at a positive level (`leftPredLevel + 1` / `rightPredLevel + 1`),
are strongly normalizing by the closed-SN handoff (`closedSubjectStronglyNormalizingFromLevelIndexed`), and the
SN-fragment decider (`Conv.decidableOfStronglyNormalizing` — normalize each, compare normal forms) then decides
their conversion.  Stated CONDITIONAL on the two fundamental conclusions, exactly like the
`ClosedLevelIndexed.lean` handoffs; becomes unconditional for every closed well-typed term pair once the
`HasTypeDescPi.rec` assembly supplies the fundamental conclusion.  This is the structural statement that the
reducibility/SN lane (Route 2) feeds the conversion-decision lane (the WN-grind spine, #267 / #503). -/
def closedConvDecidableFromLevelIndexed {profile : PolyProfile}
    (leftPredLevel rightPredLevel : Nat)
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    (leftFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (leftPredLevel + 1)
        (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier)
    (rightFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (rightPredLevel + 1)
        (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier) :
    Decidable (Conv leftSubject rightSubject) :=
  Conv.decidableOfStronglyNormalizing
    (closedSubjectStronglyNormalizingFromLevelIndexed leftPredLevel leftFundamental)
    (closedSubjectStronglyNormalizingFromLevelIndexed rightPredLevel rightFundamental)

/-- **Unconditional decidable conversion: the closed β-redex against its reduct.**  Both terms are strongly
normalizing — the β-redex `(λ (x : Type@e). x) (Type@e)` by `closedIdentityApplication_stronglyNormalizing` (the
FT `piElim` composition) and its reduct `Type@e` by `universeCode_stronglyNormalizing` — so the SN-fragment
decider decides their conversion.  This pair IS convertible (`betaRedexConvertsToReduct`), so the decision is
non-vacuous: the decider normalizes the redex to its value and finds them equal. -/
def decidableConvBetaRedexAndReduct {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Decidable
      (Conv
        (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell levelExpr flag) : RawTerm 0)
        (universeCodeCell levelExpr flag)) :=
  Conv.decidableOfStronglyNormalizing
    (closedIdentityApplication_stronglyNormalizing (profile := profile) levelExpr flag)
    (universeCode_stronglyNormalizing (profile := profile) levelExpr flag)

/-- **Unconditional decidable conversion: the closed β-redex against the identity function.**  Both terms are
strongly normalizing via the FT lane — the β-redex by `closedIdentityApplication_stronglyNormalizing`, the
identity `λ (x : Type@e). x` by `closedIdentityOnUniverse_stronglyNormalizing` — so their conversion is
decidable.  Here BOTH SN witnesses come through the fundamental theorem (lambda + bound variable + application),
the strongest demonstration that the FT-SN lane discharges the decider's hypotheses. -/
def decidableConvBetaRedexAndIdentity {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Decidable
      (Conv
        (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell levelExpr flag) : RawTerm 0)
        (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) :=
  Conv.decidableOfStronglyNormalizing
    (closedIdentityApplication_stronglyNormalizing (profile := profile) levelExpr flag)
    (closedIdentityOnUniverse_stronglyNormalizing (profile := profile) levelExpr flag)

/-- **The closed β-redex genuinely converts to its reduct.**  `(λ (x : Type@e). x) (Type@e)` reduces by one
`Step.beta` to `subst0 (variableCell 0) (Type@e)`, which is definitionally `Type@e`; `Conv.fromStep` lifts that
single step to conversion.  The non-vacuity witness for `decidableConvBetaRedexAndReduct`: the decided pair is
really convertible, so the decision procedure has a true instance to find — not an always-false relation. -/
theorem betaRedexConvertsToReduct (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Conv
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag) : RawTerm 0)
      (universeCodeCell levelExpr flag) :=
  Conv.fromStep Step.beta

end FX1Poly.Typed
