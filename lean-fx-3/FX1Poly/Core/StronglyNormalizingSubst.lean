import FX1Poly.Core.StepSubst
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Core/StronglyNormalizingSubst
    — strong normalization is REFLECTED by substitution.

`StepSubst.lean` proved that `Step` is preserved *forward* by substitution: a reduction `Step a b` lifts to
`Step (subst σ a) (subst σ b)` (the substituted terms step in lockstep with the original).  This file draws
the immediate well-foundedness corollary in the BACKWARD direction:

* `StepStar.stronglyNormalizing_of_subst` — if the substituted term `subst σ term` is strongly normalizing,
  then so is `term` itself.

The intuition: every reduction out of `term` lifts (via `Step.subst`) to a reduction out of `subst σ term`,
so an infinite reduction sequence of `term` would lift to an infinite reduction sequence of `subst σ term`,
contradicting the latter's strong normalization.  Mechanically this is `Acc`-reflection along the map
`subst σ`: `StepSuccessor` (the flipped `Step`) is a sub-relation of its `InvImage` under `subst σ` exactly
because `Step.subst` maps successors forward, and `Acc` transports backward along `InvImage` then along a
sub-relation.

Only the backward direction holds cheaply.  The *forward* direction (SN of `term` ⇒ SN of `subst σ term`)
is false without further hypotheses: substitution can create redexes a normal form did not have
(`app (var 0) a` is a normal form, but substituting `var 0 := lam b` yields the redex `app (lam b) a`), so
forward preservation is the genuinely hard "substitution preserves SN" theorem, not a corollary of
`Step.subst`.

This backward lemma is exactly what removes the closing-substitution wart from the simply-typed decider: the
fundamental theorem supplies SN of `subst σ term` (its reducibility candidate lives under a substitution into
a non-empty scope), and this lemma pulls it back to SN of the bare `term`.

## Zero-axiom verification

`Subrelation.accessible` composed with `InvImage.accessible` (both `Init`-level well-foundedness primitives),
fed `Step.subst` as the sub-relation witness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Strong normalization is reflected by substitution.**  If `subst σ term` is strongly normalizing, so is
`term`: every successor of `term` lifts (via `Step.subst`) to a successor of `subst σ term`, so `term`'s
accessibility follows from `subst σ term`'s by reflecting `Acc` along `subst σ`. -/
theorem StepStar.stronglyNormalizing_of_subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (term : RawTerm sourceScope)
    (substTerminates : StepStar.IsStronglyNormalizing (RawTerm.subst substitution term)) :
    StepStar.IsStronglyNormalizing term :=
  Subrelation.accessible
    (fun stepSuccessor => Step.subst substitution stepSuccessor)
    (InvImage.accessible (RawTerm.subst substitution) substTerminates)

end FX1Poly.Core
