import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamIntroGateUnconditional
import FX1Poly.Typed.Metatheory.SubjectReduction.CongruenceCloserAssembly
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSingleStepSubjectReduction

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/SubjectReductionPathLamDischarged
    — the SR arc with the `pathLam` node DISCHARGED (A1-SR-RECLOSE)

`PathLamIntroGateUnconditional.lean` proved the seventeenth introducer-congruence row
`pathLamIntroGateBranchClosesUnconditional : PathLamIntroGateBranchCloses profile` with NO hypothesis — the
interval-lock + App-scaled affine bridge discharged the lone open intro branch.  This file threads that
unconditional witness through the single-step subject-reduction arc, so the `pathLam` node is no longer an
ASSUMED premise anywhere downstream:

  * `unionIntroCongruenceClosesUnconditional` — the WHOLE introducer-congruence gate
    (`UnionIntroCongruenceCloses`), all seventeen rows, unconditional;
  * `unionCongruenceCloserModuloChildSR` — the single-step congruence closer modulo EXACTLY the well-founded
    single-step-SR self-reference `UnionChildSubjectReduction` (the formation / elim / intro mountain all
    discharged — the `pathLam` branch and the empty-type bookkeeping no longer appear);
  * `singleStepSubjectReductionModuloChildSR` / `…PreservingModuloChildSR` — the single-step union SR master
    (up-to-`Conv` and classifier-preserving) modulo ONLY that one self-reference.

## What this closes, and the honest residual

Before this file the single-step congruence closer rested on TWO premises (`CongruenceCloserAssembly`):
`UnionChildSubjectReduction` AND `PathLamIntroGateBranchCloses`.  The second is now a THEOREM, so the package
collapses to ONE premise.  That remaining premise — `UnionChildSubjectReduction`, the single-step-SR
self-reference — is NOT a `pathLam`/A1 obligation: it ties off by structural-fuel recursion
(`unionChildSubjectReductionOfAllBelow`, #1784 SR-WF-TIEOFF) whose bounded congruence master's open gate is the
ELIMINATOR motive-multi-step third, an arc orthogonal to A1.  So the `pathLam` interval-lock investment is now
provably LOAD-BEARING and OFF the open critical path: every place that used to assume the `pathLam` branch gets
it for free.

Native empty-type consistency is a SEPARATE, more-discharged route (`EmptyTypeConsistencyNativeUnion`):
`coreFragmentConsistencyFromElimCongruenceCloserSnDischarged` already has the SN gate discharged (#1734) and
collapses the intro arm VACUOUSLY at `emptyTypeCell` (`congruenceClosesToEmptyTypeModuloElim`), so it never
depended on the `pathLam` intro node — it rests on the eliminator congruence closer (#1740).  The review's
re-entrancy worry ("the affine bridge re-opens consistency behind the `pathLam` node") is therefore answered
negatively: the augmented judgment leaves the empty-type route untouched (the full kernel + zero-axiom audit
build green), and the `pathLam` node it was worried about is here discharged, not assumed.

## Zero-axiom

Pure composition of `pathLamIntroGateBranchClosesUnconditional` (zero-axiom, audit-gated) with the shipped
congruence-closer assembly and single-step SR masters.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The introducer-congruence gate, UNCONDITIONAL.**  `unionIntroCongruenceClosesOfPathLam` instantiated at
the now-proven `pathLamIntroGateBranchClosesUnconditional`: all seventeen introducer rows — the sixteen shipped
data/`lam` branches plus the discharged `pathLam` branch — close with no remaining premise.  The introducer leg
of the native congruence mountain is fully closed. -/
theorem HasTypeUnion.unionIntroCongruenceClosesUnconditional {profile : PolyProfile} :
    UnionIntroCongruenceCloses profile :=
  HasTypeUnion.unionIntroCongruenceClosesOfPathLam pathLamIntroGateBranchClosesUnconditional

/-- **★ The single-step congruence closer modulo ONLY the well-founded self-reference.**  The two-premise
package of `unionCongruenceCloserOfPathLam` (`UnionChildSubjectReduction` AND `PathLamIntroGateBranchCloses`)
collapses to one: the `pathLam` branch is supplied by `pathLamIntroGateBranchClosesUnconditional`, so the only
remaining hypothesis is the single-step-SR self-reference `UnionChildSubjectReduction` (#1784 SR-WF-TIEOFF).
The formation, eliminator, and (now) introducer gates are all unconditional. -/
theorem HasTypeUnion.unionCongruenceCloserModuloChildSR {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionCongruenceCloser profile context classifier :=
  HasTypeUnion.unionCongruenceCloserOfPathLam wellFormed childSubjectReduction
    pathLamIntroGateBranchClosesUnconditional

/-- **★ The single-step union SR master (up to `Conv`) modulo ONLY the self-reference.**  A single `Step` of a
union-typed term yields a reduct union-typed at a `Conv`-equal classifier, given just well-formedness and the
single-step-SR self-reference `UnionChildSubjectReduction` — the `pathLam` branch is discharged inside.  The
`pathLam` interval-lock node carries no residual soundness role in single-step subject reduction. -/
theorem HasTypeUnion.singleStepSubjectReductionModuloChildSR {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (step : Step subject reduct) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context reduct pinned ∧ Conv pinned classifier :=
  HasTypeUnion.singleStepSubjectReductionUpToCongruence typed wellFormed
    (HasTypeUnion.unionCongruenceCloserModuloChildSR wellFormed childSubjectReduction) step

/-- **★ The classifier-PRESERVING single-step union SR master modulo ONLY the self-reference.**  Same as
`singleStepSubjectReductionModuloChildSR` but landing the reduct at the EXACT original classifier (the
up-to-`Conv` reduct reclassified back via the conv arm + unconditional validity).  This is the drop-in shape
the consistency route's `singleStepSubjectReduction` gate consumes — with the `pathLam` branch discharged, its
only standing hypothesis is the well-founded self-reference. -/
theorem HasTypeUnion.singleStepSubjectReductionPreservingModuloChildSR {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (step : Step subject reduct) :
    HasTypeUnion profile context reduct classifier :=
  HasTypeUnion.singleStepSubjectReductionPreservingUpToCongruence typed wellFormed
    (HasTypeUnion.unionCongruenceCloserModuloChildSR wellFormed childSubjectReduction) step

end FX1Poly.Typed
