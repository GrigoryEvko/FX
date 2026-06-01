import FX1Poly.Core.CandidateInterpretationDeterminism

/-! # FX1Poly/Core/PointwiseIffAlgebra
    — the equivalence-relation algebra of `PointwiseIff` (reflexivity, symmetry, transitivity)

`PointwiseIff candidateA candidateB := ∀ term, candidateA term ↔ candidateB term` is the candidate
equivalence the reducibility model is functional up to (`ReducibleType.deterministic` returns it).  Every
candidate transport — porting a membership/reducibility fact from one candidate to a pointwise-equivalent
one — needs to reflect, flip, and chain these equivalences.  This brick ships that equivalence-relation
algebra so the transports read as `pointwise.symm`, `pointwise₁.trans pointwise₂` rather than inlining
`fun term => (h term).symm` each time.  In particular the pending pointwise-congruence closure of
`ReducibleType` (the `ofPointwiseIff` arm that lets the canonical member-predicate candidate be a genuine
`ReducibleType` candidate — the choice-free `piIntro` keystone, ported from the stratified
`StratifiedReducibleType.ofPointwiseIff` template) threads these at every cross-arm of `deterministic`.

## Zero-axiom verification

Each is a pointwise lift of the corresponding `Iff` combinator (`Iff.rfl` / `.symm` / `.trans`) under the
`∀ term` binder — no `propext` (the `Iff`s are transported, never converted to equalities).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- Reflexivity of candidate pointwise-equivalence: every candidate is pointwise-equivalent to itself. -/
theorem PointwiseIff.refl {scope : Nat} (candidate : RawTerm scope → Prop) :
    PointwiseIff candidate candidate :=
  fun _term => Iff.rfl

/-- Symmetry of candidate pointwise-equivalence. -/
theorem PointwiseIff.symm {scope : Nat} {candidateA candidateB : RawTerm scope → Prop}
    (equivalence : PointwiseIff candidateA candidateB) : PointwiseIff candidateB candidateA :=
  fun term => (equivalence term).symm

/-- Transitivity of candidate pointwise-equivalence: chaining two equivalences through a shared middle
candidate.  This is the composition the reducibility transports use to move a fact along a chain of
pointwise-equivalent candidates (e.g. `base ~ canonical ~ reshaped`). -/
theorem PointwiseIff.trans {scope : Nat} {candidateA candidateB candidateC : RawTerm scope → Prop}
    (equivalenceLeft : PointwiseIff candidateA candidateB)
    (equivalenceRight : PointwiseIff candidateB candidateC) : PointwiseIff candidateA candidateC :=
  fun term => (equivalenceLeft term).trans (equivalenceRight term)

end FX1Poly.Core
