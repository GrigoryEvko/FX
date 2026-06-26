import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateDispatch
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimCongruenceGate
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFormationCongruenceGate

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/CongruenceCloserAssembly
    — SR-DSL-5: the single-step congruence closer, assembled from the three gates

`HasTypeUnion.unionCongruenceCloserOfGates` (HasTypeUnionCongruenceClosesGeneric.lean) reduces the generic
`UnionCongruenceCloser` (the residual of single-step subject reduction on a `.mkGen` whose children step) to
THREE named congruence gates plus the single-step-SR self-reference `UnionChildSubjectReduction`.  All three
gates are now inhabited:

  * **formation** — `HasTypeUnion.unionFormationCongruenceClosesGate` (unconditional, generic over the four
    formation families);
  * **elim** — `elimCongruenceClosesFromBranches` (unconditional, dispatching `elimRuleOf_cases` over its eleven
    branch lemmas — `pathApp` included, since only the affine `pathLam` INTRODUCER is interval-blocked);
  * **intro** — `HasTypeUnion.unionIntroCongruenceClosesOfPathLam` (dispatching `introRuleOf_cases` over the
    sixteen shipped intro branches, with the seventeenth — `pathLam` — taken as the premise
    `PathLamIntroGateBranchCloses`).

So this file assembles the lot: the entire single-step congruence closer reduces to EXACTLY TWO honest
premises — the `pathLam` intro branch (`PathLamIntroGateBranchCloses`, discharged by the A1 / interval-non-
fibrant lineage) and the single-step-SR self-reference (`UnionChildSubjectReduction`, discharged by the
well-founded recursion that ties single-step SR to its own congruence case).  Nothing else in the native
congruence mountain remains open.

## Zero-axiom

`unionCongruenceCloserOfGates` applied to the three shipped gate inhabitants.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The single-step congruence closer, modulo the two honest premises.**  For any context and classifier,
the generic `UnionCongruenceCloser` is inhabited given (1) the single-step-SR self-reference
`UnionChildSubjectReduction` and (2) the one `pathLam` intro branch `PathLamIntroGateBranchCloses` — the
formation and eliminator gates are discharged unconditionally.  This is the off-`emptyTypeCell` generalization
of `congruenceClosesToEmptyTypeModuloElim` with its full native congruence content assembled: the whole intro /
elim / formation mountain now rests on exactly the `pathLam` branch (#A1-4) and the well-founded self-reference
(#SR-WF-TIEOFF). -/
theorem HasTypeUnion.unionCongruenceCloserOfPathLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (pathLamBranch : PathLamIntroGateBranchCloses profile) :
    UnionCongruenceCloser profile context classifier :=
  HasTypeUnion.unionCongruenceCloserOfGates wellFormed childSubjectReduction
    HasTypeUnion.unionFormationCongruenceClosesGate
    (HasTypeUnion.unionIntroCongruenceClosesOfPathLam pathLamBranch)
    elimCongruenceClosesFromBranches

end FX1Poly.Typed
