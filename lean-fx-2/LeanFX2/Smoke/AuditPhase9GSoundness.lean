import LeanFX2.Algo.Soundness

/-! Phase 9.G — Closure soundness audit (zero-axiom).

This file demonstrates the end-to-end soundness contract for
`Algo/Eval`: every reduction the typed evaluator performs is
witnessed by a `Step` (single-step) or `StepStar` (multi-step)
in the kernel reduction relation.

## What's audited

* `Term.headStep?_sound` — single-step closure: `headStep? = some _
  → Step ...`.  Combines the 6 per-case theorems via
  exhaustive pattern match on the source term + scrutinee head.

* `Term.eval_sound` — multi-step closure: `StepStar ... (eval fuel
  ...)`.  Lifts via fuel induction on top of `headStep?_sound`.

## Concrete instantiations

Each example invokes the closure on a witnessed reduction and
verifies the produced Step witness has the expected reduct.
-/

namespace LeanFX2.SmokePhase9GSoundness

open LeanFX2

#print axioms Term.headStep?_sound
#print axioms Term.eval_sound

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Concrete: `headStep?_sound` on a boolElim-true reduction.
The closure recovers a `Step` witness with reduct = thenBranch.

The explicit `(result := ⟨_, thenBranch⟩)` is needed because the
return type `Step _ result.snd` involves a Sigma projection that
Lean's elaborator doesn't pattern-match against `thenBranch` from
the goal alone — it has to be told. -/
theorem boolElimTrue_step_sound
    {motiveType : Ty level scope}
    (thenBranch : Term context motiveType RawTerm.unit)
    (elseBranch : Term context motiveType RawTerm.unit) :
    Step (Term.boolElim (motiveType := motiveType)
            Term.boolTrue thenBranch elseBranch) thenBranch :=
  Term.headStep?_sound (result := ⟨_, thenBranch⟩) _ rfl

/-- Concrete: `eval_sound` on a boolElim-true reduction with
fuel = 1.  The closure produces a `StepStar` chain of length 1. -/
theorem boolElimTrue_eval_sound
    {motiveType : Ty level scope}
    (thenBranch : Term context motiveType RawTerm.unit)
    (elseBranch : Term context motiveType RawTerm.unit) :
    StepStar (Term.boolElim (motiveType := motiveType)
                Term.boolTrue thenBranch elseBranch)
             (Term.eval 1 (Term.boolElim (motiveType := motiveType)
                              Term.boolTrue thenBranch elseBranch)).snd :=
  Term.eval_sound 1 _

/-- Concrete: `eval_sound` with fuel = 0 produces a refl chain.
Eval doesn't fire when fuel is zero, so source = result. -/
theorem eval_sound_zeroFuel
    (someTerm : Term context (Ty.unit (level := level) (scope := scope))
                              RawTerm.unit) :
    StepStar someTerm (Term.eval 0 someTerm).snd :=
  Term.eval_sound 0 someTerm

/-- Concrete: `eval_sound` on a non-firing canonical term.
`Term.unit` is in WHNF — eval returns it unchanged. -/
theorem eval_sound_unitInWhnf :
    StepStar (context := context) (Term.unit (level := level) (scope := scope))
             (Term.eval 5 Term.unit).snd :=
  Term.eval_sound 5 Term.unit

/-- Concrete: `headStep?_sound` on a natElim-zero reduction. -/
theorem natElimZero_step_sound
    {motiveType : Ty level scope}
    (zeroBranch : Term context motiveType RawTerm.unit)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType)
                              (RawTerm.lam RawTerm.unit)) :
    Step (Term.natElim (motiveType := motiveType)
            Term.natZero zeroBranch succBranch) zeroBranch :=
  Term.headStep?_sound (result := ⟨_, zeroBranch⟩) _ rfl

/-- Concrete: `headStep?_sound` on a listElim-nil reduction. -/
theorem listElimNil_step_sound
    {elementType motiveType : Ty level scope}
    (nilBranch : Term context motiveType RawTerm.unit)
    (consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType)
                                            motiveType))
                              (RawTerm.lam (RawTerm.lam RawTerm.unit))) :
    Step (Term.listElim (elementType := elementType)
            (motiveType := motiveType)
            Term.listNil nilBranch consBranch) nilBranch :=
  Term.headStep?_sound (result := ⟨_, nilBranch⟩) _ rfl

/-- Concrete: `headStep?_sound` on an optionMatch-none reduction. -/
theorem optionMatchNone_step_sound
    {elementType motiveType : Ty level scope}
    (noneBranch : Term context motiveType RawTerm.unit)
    (someBranch : Term context (Ty.arrow elementType motiveType)
                              (RawTerm.lam RawTerm.unit)) :
    Step (Term.optionMatch (elementType := elementType)
            (motiveType := motiveType)
            Term.optionNone noneBranch someBranch) noneBranch :=
  Term.headStep?_sound (result := ⟨_, noneBranch⟩) _ rfl

end LeanFX2.SmokePhase9GSoundness
