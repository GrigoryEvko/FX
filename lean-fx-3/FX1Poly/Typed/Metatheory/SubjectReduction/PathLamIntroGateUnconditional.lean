import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamInnerAffineBridge
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateDispatch

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/PathLamIntroGateUnconditional
    — discharging the `pathLam` intro-gate's last conditional (A1-RETIRE-COUNT)

`IntroGateDispatch.pathLamIntroGateBranchCloses` proved the seventeenth introducer-congruence row MODULO one
honest believed-true Prop, `PathLamBodyStepPreservesAppScaledAffine`: when a TYPED `pathLam` body steps, its
beta-stable App-scaled freshest-binder affine grade is preserved.  That Prop is FALSE as a raw-term lemma (a raw
body admits a non-affine inner `pathLam` whose endpoint-β duplicates the dimension), which is exactly why it
carried a `HasTypeUnion` hypothesis — it is the A1-SUBST-OPEN subterm-typing metatheory.

This file discharges it.  The two ingredients are now both in hand:

  * `allInnerPathLamAffine_ofTyped` (the typed ⟹ inner-affine bridge): a union-typed body satisfies the
    structural invariant `AllInnerPathLamAffine` — every inner `pathLam` is itself an introducer whose
    `sideCondition` IS the App-scaled affine grade, so typing forces all inner `pathLam` sites affine.
  * `appScaledDimensionGrade_step_le_ofSitesAffine` (the headline beta-stability lemma): UNDER that invariant,
    ANY `Step` of the body does not increase the App-scaled grade.

Composing them with `UsageGrade.le_trans` against the redex's own affine `sideCondition` re-establishes the grade
on the stepped body — UNCONDITIONALLY.  So `PathLamBodyStepPreservesAppScaledAffine` is now a THEOREM, and the
seventeenth intro-gate row (`PathLamIntroGateBranchCloses`) closes with no hypothesis.

## Zero-axiom

`allInnerPathLamAffine_ofTyped` (zero-axiom, audit-gated) + `appScaledDimensionGrade_step_le_ofSitesAffine`
(zero-axiom) + `UsageGrade.le_trans`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-- **★ The affine-subject-reduction Prop, DISCHARGED (A1-RETIRE-COUNT).**  When a TYPED `pathLam` body steps,
its beta-stable App-scaled freshest-binder affine grade is preserved — UNCONDITIONALLY.  Typing forces every
inner `pathLam` affine (`allInnerPathLamAffine_ofTyped`), so the App-scaled grade is beta-stable
(`appScaledDimensionGrade_step_le_ofSitesAffine`): the stepped body's grade is `≤` the original's, which the
redex's own `sideCondition` bounds by `one`.  This is the single residual the `pathLam` SR arc rested on; with
it the syntactic affine occurrence count carries no soundness role. -/
theorem pathLamBodyStepPreservesAppScaledAffine_holds {profile : PolyProfile} :
    PathLamBodyStepPreservesAppScaledAffine profile := by
  intro scope _context body _bodyPrime _classifier bodyTyped bodyStep sideHolds
  exact UsageGrade.le_trans
    (appScaledDimensionGrade_step_le_ofSitesAffine
      (allInnerPathLamAffine_ofTyped bodyTyped) bodyStep ⟨0, Nat.succ_pos scope⟩)
    sideHolds

/-- **★ The seventeenth introducer-congruence row, UNCONDITIONAL.**  `pathLamIntroGateBranchCloses` instantiated
at the now-proven `PathLamBodyStepPreservesAppScaledAffine`: the `pathLam` intro-gate branch closes with no
remaining hypothesis — the body obligation drift, the `bridge`-code output drift at both endpoints, and the
re-established App-scaled affine side condition are all in hand. -/
theorem pathLamIntroGateBranchClosesUnconditional {profile : PolyProfile} :
    PathLamIntroGateBranchCloses profile :=
  pathLamIntroGateBranchCloses pathLamBodyStepPreservesAppScaledAffine_holds

end FX1Poly.Typed
