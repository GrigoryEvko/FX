import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.SigmaCodeShape
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/HasTypeSubjectReduction
    — typed Subject Reduction (P4) for the current typing fragment

`HasType.subjectHasNoStep` is the structural invariant of the current `HasType`
fragment (`var` / `conv` / `universeFormation` / `piFormation` /
`sigmaFormation`): every well-typed SUBJECT is NORMAL — the leaves
(`variableCell`, `universeCodeCell`) have no outgoing `Step`, and the type
formers (`piTyCodeCell`, `sigmaTyCodeCell`) are pure (no head redex), so a step
could only descend into a child, ruled out by the children's IHs.  It is the
subject-side companion of `IsType.hasNoStep` (the classifier side).

Typed Subject Reduction (P4, the fibration property — polycell.md §11.8.5,
"P4 Subject Reduction = the fibration property") — `HasType Γ t T → Step t t' →
HasType Γ t' T` — then holds for this fragment *vacuously*: the `Step` premise
is unsatisfiable because the subject is normal, so there is no redex to
preserve.  The THEOREM is permanent; its content grows as redex-bearing arms
(`app` β-reduction, eliminator ι) join `HasType`, at which point the proof
routes through the typed substitution lemma and the structural iota arms.  P4
feeds canonicity ⇒ consistency (P10), NOT decidability (that is the
decidable-`Conv` line).

## Zero-axiom verification

A propext-free `induction` on the `HasType` derivation (the recursor with a
subject-only motive) + the leaf no-step lemmas (`noStep_var`,
`noStep_universeCode`); the `conv` arm is its premise's IH.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- Every well-typed subject in the current fragment is NORMAL: the leaves
(`variableCell`, `universeCodeCell`) step nowhere (`noStep_var` /
`noStep_universeCode`), and the type formers (`piTyCodeCell`, `sigmaTyCodeCell`)
are pure, so a step could only descend into a child.

Proved by **induction on the derivation**: the motive "the subject does not step"
depends only on the subject, so `var`/`universeFormation` discharge by the leaf
no-step lemmas; `conv` is exactly its premise's IH (the subject is unchanged
across a conversion); and `piFormation` / `sigmaFormation` feed the children IHs
to `piTyCodeCell_noStep_of_childrenNoStep` /
`sigmaTyCodeCell_noStep_of_childrenNoStep`, reaching the children's normality.
`IsType.hasNoStep` delegates here. -/
theorem HasType.subjectHasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    ∀ reduct : RawTerm scope, Step subject reduct → False := by
  induction typed with
  | var context index => exact fun _reduct step => StepStar.noStep_var index step
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise _ihReclassifierTyped =>
      exact ihTypedPremise
  | universeFormation context levelExpr flag =>
      exact fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step
  | piFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      exact piTyCodeCell_noStep_of_childrenNoStep ihDomain ihCodomain
  | sigmaFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      exact sigmaTyCodeCell_noStep_of_childrenNoStep ihDomain ihCodomain

/-- **Typed Subject Reduction (P4)** for the current fragment.  Holds vacuously:
a well-typed subject does not `Step` (`subjectHasNoStep`), so the reduction
premise is absurd and typing is preserved with no redex to check.  The statement
is permanent; β/ι content arrives with the redex-bearing `HasType` arms. -/
theorem HasType.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (typed : HasType profile context subject classifier)
    (steps : Step subject reduct) :
    HasType profile context reduct classifier :=
  absurd steps (typed.subjectHasNoStep reduct)

end FX1Poly.Typed
