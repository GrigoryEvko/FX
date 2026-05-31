import FX1Poly.Core.WhnfInterpretation
import FX1Poly.Core.HeadStepRenameReflect
import FX1Poly.Core.HeadStepCommute
import FX1Poly.Core.CandidateInterpretationRename

/-! # Foundation/PolyCell/Core/WhnfInterpretationRename
    — the weak-head interpretation commutes with renaming

Mirrors `InterpretsType.rename` (`CandidateInterpretationRename`) for the conversion-invariant
`InterpretsWhnf`.  If a type-code interprets to a candidate under an environment pre-composed with a
renaming, then the renamed code interprets to the SAME candidate under the original environment.  This
is the renaming leg of the fundamental theorem (the binder cases interpret a codomain under one more
variable, which on the term side is a weakening = renaming).

The two arms beyond `InterpretsType`'s are discharged by the weak-head substrate:

  * `neutralApp` — a stuck application stays stuck after renaming, by
    `HeadStep.rename_preserves_headNormal` (`HeadStepRenameReflect`);
  * `headExpand` — the renamed code weak-head reduces to the renamed reduct, by `HeadStep.rename`
    (`HeadStepCommute`), and the reduct interprets by the induction hypothesis.

The other three arms (`typeVariable`, `piType`, `baseNormal`) are exactly as in `InterpretsType.rename`
(`rename_var_reduces`, `rename_piTyCode` + `candidateEnv_cons_lift_eq`, `rename_rootGenerator`).

## Zero-axiom verification

Induction on the interpretation discharging to the shipped rename substrate; no new recursion.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **The weak-head interpretation commutes with renaming.**  If `typeCode` interprets to `candidate`
under `sourceEnv` and each source variable's candidate agrees with the renamed environment, then
`rename rawRenaming typeCode` interprets to `candidate` under the renamed environment. -/
theorem InterpretsWhnf.rename {sourceScope targetScope : Nat}
    {sourceEnv : CandidateEnv sourceScope targetScope} {typeCode : RawTerm sourceScope}
    {candidate : RawTerm targetScope → Prop}
    (interpretation : InterpretsWhnf sourceEnv typeCode candidate) :
    ∀ {renamedScope : Nat} {env : CandidateEnv renamedScope targetScope}
      (rawRenaming : RawRenaming sourceScope renamedScope),
      (∀ index, sourceEnv index = env (rawRenaming index)) →
      InterpretsWhnf env (RawTerm.rename rawRenaming typeCode) candidate := by
  induction interpretation with
  | typeVariable environment index =>
      intro renamedScope env rawRenaming envEquality
      rw [RawTerm.rename_var_reduces, envEquality index]
      exact InterpretsWhnf.typeVariable env (rawRenaming index)
  | piType _domainInterp _codomainInterp domainInductiveHypothesis
      codomainInductiveHypothesis =>
      intro renamedScope env rawRenaming envEquality
      rw [RawTerm.rename_piTyCode]
      exact InterpretsWhnf.piType
        (domainInductiveHypothesis rawRenaming envEquality)
        (codomainInductiveHypothesis (RawRenaming.lift rawRenaming)
          (candidateEnv_cons_lift_eq envEquality))
  | baseNormal environment notVariable notPiType notApp =>
      intro renamedScope env rawRenaming _envEquality
      refine InterpretsWhnf.baseNormal env ?_ ?_ ?_
      · rw [RawTerm.rename_rootGenerator]; exact notVariable
      · rw [RawTerm.rename_rootGenerator]; exact notPiType
      · rw [RawTerm.rename_rootGenerator]; exact notApp
  | neutralApp environment noHeadStep =>
      intro renamedScope env rawRenaming _envEquality
      rw [RawTerm.rename_app_reduces]
      exact InterpretsWhnf.neutralApp env
        (HeadStep.rename_preserves_headNormal rawRenaming noHeadStep)
  | headExpand headStep _reductInterprets reductInductiveHypothesis =>
      intro renamedScope env rawRenaming envEquality
      exact InterpretsWhnf.headExpand (HeadStep.rename rawRenaming headStep)
        (reductInductiveHypothesis rawRenaming envEquality)

end FX1Poly.Core
