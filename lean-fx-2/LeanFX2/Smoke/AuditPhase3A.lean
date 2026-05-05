import LeanFX2.Reduction.Step

/-! Phase 3.A zero-axiom audit — Step inductive + cast helpers. -/

#print axioms LeanFX2.Step
#print axioms LeanFX2.Step.castSourceType
#print axioms LeanFX2.Step.castTargetType
#print axioms LeanFX2.Step.castSourceRaw
#print axioms LeanFX2.Step.castTargetRaw
#print axioms LeanFX2.Step.castSourceTerm
#print axioms LeanFX2.Step.castTargetTerm

/-! Smoke: a concrete βι reduction at scope 0. -/

namespace LeanFX2.Smoke.Phase3A

/-- `(λx:unit. x) () ⟶β ()` at the empty context. -/
example :
    LeanFX2.Step
      (LeanFX2.Term.app
        (LeanFX2.Term.lam
          (codomainType := LeanFX2.Ty.unit)
          (LeanFX2.Term.var ⟨0, Nat.zero_lt_succ _⟩))
        (LeanFX2.Term.unit
          (context := LeanFX2.Ctx.empty (mode := LeanFX2.Mode.software) (level := 0))))
      (LeanFX2.Term.subst0
        (LeanFX2.Term.var ⟨0, Nat.zero_lt_succ _⟩)
        (LeanFX2.Term.unit
          (context := LeanFX2.Ctx.empty (mode := LeanFX2.Mode.software) (level := 0)))) :=
  LeanFX2.Step.betaApp _ _

/-- `boolElim true t e ⟶ι t`. -/
example
    {motiveType : LeanFX2.Ty 0 0}
    (thenBranch elseBranch :
      LeanFX2.Term (LeanFX2.Ctx.empty (mode := LeanFX2.Mode.software) (level := 0))
        motiveType LeanFX2.RawTerm.boolTrue) :
    LeanFX2.Step
      (LeanFX2.Term.boolElim LeanFX2.Term.boolTrue thenBranch elseBranch)
      thenBranch :=
  LeanFX2.Step.iotaBoolElimTrue _ _

end LeanFX2.Smoke.Phase3A
