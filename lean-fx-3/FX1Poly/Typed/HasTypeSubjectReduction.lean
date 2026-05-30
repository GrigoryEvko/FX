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

`typedSubjectIsVariableOrUniverseCode` (a propext-free induction) + the leaf
no-step lemmas (`noStep_var`, `noStep_universeCode`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- Every well-typed subject in the current fragment is a non-stepping leaf: it
is a `variableCell` or a `universeCodeCell`
(`typedSubjectIsVariableOrUniverseCode`), and both are normal leaves
(`noStep_var` / `noStep_universeCode`). -/
theorem HasType.subjectHasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    ∀ reduct : RawTerm scope, Step subject reduct → False := by
  rcases typed.typedSubjectIsVariableOrUniverseCode with
    ⟨index, subjectIsVariable⟩ | ⟨levelExpr, flag, subjectIsUniverse⟩
  · subst subjectIsVariable
    exact fun _reduct step => StepStar.noStep_var index step
  · subst subjectIsUniverse
    exact fun _reduct step =>
      StepStar.noStep_universeCode (levelExpr, flag) step

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
