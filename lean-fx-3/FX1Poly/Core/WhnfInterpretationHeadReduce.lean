import FX1Poly.Core.WhnfInterpretationDeterminism

/-! # Foundation/PolyCell/Core/WhnfInterpretationHeadReduce
    — the weak-head interpretation respects weak-head reduction (both directions)

The `headExpand` constructor of `InterpretsWhnf` gives the BACKWARD direction by construction: if a
weak-head reduct interprets to a candidate, so does the redex.  This file proves the FORWARD
direction, `InterpretsWhnf.headReduce`: if a redex interprets to a candidate, so does its weak-head
reduct.  Together they package as `InterpretsWhnf.headStep_iff` — a type-code and its weak-head reduct
interpret to the SAME candidate.  This is the conversion-invariance CORE: the interpretation is stable
under weak-head reduction in both directions, which is exactly what `InterpretsType` (syntactic-head
dispatch) lacked.

The forward direction is a one-step inversion: a code with a weak-head step is application-headed and
reducible, so its derivation can only be `headExpand`; `HeadStep.deterministic` then identifies the
constructor's reduct with the given one.  The other four arms are impossible — `typeVariable` /
`piType` have no weak-head step (closed by `cases` on the impossible `HeadStep`), `baseNormal` /
`neutralApp` contradict the step (via `subjectRootIsApp` / the stored no-step hypothesis).

## Zero-axiom verification

`cases` on the interpretation (free subject — the propext-safe direction), discharging the impossible
arms by `cases` on the impossible `HeadStep` or `HeadStep.subjectRootIsApp`, and the `headExpand` arm
by `HeadStep.deterministic` + `rw`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Forward weak-head reduction respect**: if a type-code interprets to a candidate and weak-head
reduces, its reduct interprets to the SAME candidate.  One-step inversion: the code has a weak-head
step, so its derivation is `headExpand`, whose reduct is identified with the given one by
`HeadStep.deterministic`. -/
theorem InterpretsWhnf.headReduce {scope targetScope : Nat}
    {env : CandidateEnv scope targetScope} {typeCode reduct : RawTerm scope}
    {candidate : RawTerm targetScope → Prop}
    (interprets : InterpretsWhnf env typeCode candidate)
    (headStep : HeadStep typeCode reduct) :
    InterpretsWhnf env reduct candidate := by
  cases interprets with
  | typeVariable environment index => cases headStep
  | piType _domainInterprets _codomainInterprets => cases headStep
  | baseNormal environment _notVariable _notPiType notApp =>
      exact absurd (HeadStep.subjectRootIsApp headStep) notApp
  | neutralApp environment noHeadStep => exact absurd headStep (noHeadStep reduct)
  | headExpand headStepConstructor reductInterprets =>
      rw [HeadStep.deterministic headStep headStepConstructor]
      exact reductInterprets

/-- **Weak-head reduction invariance**: a type-code and its weak-head reduct interpret to the same
candidate (forward by `headReduce`, backward by the `headExpand` constructor).  The conversion-
invariance core of the weak-head interpretation. -/
theorem InterpretsWhnf.headStep_iff {scope targetScope : Nat}
    {env : CandidateEnv scope targetScope} {typeCode reduct : RawTerm scope}
    {candidate : RawTerm targetScope → Prop}
    (headStep : HeadStep typeCode reduct) :
    InterpretsWhnf env typeCode candidate ↔ InterpretsWhnf env reduct candidate :=
  ⟨fun interprets => interprets.headReduce headStep,
   fun interprets => InterpretsWhnf.headExpand headStep interprets⟩

end FX1Poly.Core
