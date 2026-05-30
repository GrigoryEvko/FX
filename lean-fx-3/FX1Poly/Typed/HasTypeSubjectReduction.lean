import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/HasTypeSubjectReduction
    — typed Subject Reduction (P4) for the current typing fragment

`HasType.subjectHasNoStep` is the structural invariant of the current `HasType`
fragment (`var` / `conv` / `universeFormation`): every well-typed SUBJECT is a
non-stepping leaf — a `variableCell` or a `universeCodeCell`, neither of which
has an outgoing `Step`.  It is the subject-side companion of `IsType.hasNoStep`
(which is the classifier side).

Typed Subject Reduction (P4, the fibration property — polycell.md §11.8.5,
"P4 Subject Reduction = the fibration property") — `HasType Γ t T → Step t t' →
HasType Γ t' T` — then holds for this fragment *vacuously*: the `Step` premise
is unsatisfiable because the subject is a leaf, so there is no redex to
preserve.  The THEOREM is permanent; its content grows as redex-bearing arms
(`app` β-reduction, eliminator ι) join `HasType` (#444), at which point the
proof routes through the typed substitution lemma (#457) and the structural
iota arms instead of leaf no-step.  Per the milestone ledger (#484), P4 feeds
canonicity ⇒ consistency (P10), NOT decidability (that is the decidable-`Conv`
line, already shipped for the normal fragment).

## Zero-axiom verification

A propext-free `induction` on the `HasType` derivation (the recursor with a
subject-only motive) + the leaf no-step lemmas (`noStep_var`,
`noStep_universeCode`); the `conv` arm is its premise's IH.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- Every well-typed subject in the current fragment is a non-stepping leaf: a
`variableCell` or a `universeCodeCell`, both normal leaves (`noStep_var` /
`noStep_universeCode`).

Proved by **induction on the derivation** (NOT `rcases` on
`typedSubjectIsVariableOrUniverseCode`): the motive "the subject does not step"
depends only on the subject, so `var`/`universeFormation` discharge by the leaf
no-step lemmas and `conv` is exactly its premise's IH (the subject is unchanged
across a conversion).  This is the #443-ready shape: a nesting type former
(`piFormation`) joins as one more arm whose children IHs feed
`piTyCodeCell_noStep_of_childrenNoStep` — whereas the old classification-`rcases`
proof could not have reached the children's normality.  It also decouples this
lemma (and `IsType.hasNoStep`, which now delegates here) from the classification
lemma, shrinking the eventual Π cascade. -/
theorem HasType.subjectHasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    ∀ reduct : RawTerm scope, Step subject reduct → False := by
  induction typed with
  | var index => exact fun _reduct step => StepStar.noStep_var index step
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise _ihReclassifierTyped =>
      exact ihTypedPremise
  | universeFormation levelExpr flag =>
      exact fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step

/-- **Typed Subject Reduction (P4)** for the current fragment.  Holds vacuously:
a well-typed subject does not `Step` (`subjectHasNoStep`), so the reduction
premise is absurd and typing is preserved with no redex to check.  The statement
is permanent; β/ι content arrives with the redex-bearing `HasType` arms (#444). -/
theorem HasType.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (typed : HasType profile context subject classifier)
    (steps : Step subject reduct) :
    HasType profile context reduct classifier :=
  absurd steps (typed.subjectHasNoStep reduct)

end FX1Poly.Typed
