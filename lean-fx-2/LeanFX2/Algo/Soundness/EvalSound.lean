import LeanFX2.Algo.Soundness.HeadStepClosure

namespace LeanFX2

/-! ## Multi-step closure: `Term.eval_sound`

Lift `Term.headStep?_sound` through the fuel-bounded loop in
`Term.eval`.  Whenever `Term.eval fuel` produces a result, that
result is reachable from the source term via a `StepStar` chain
of length ≤ fuel.

This is the END-TO-END soundness contract for the typed
evaluator: `Term.eval` is a sound implementation of the kernel's
multi-step reduction (within the restricted ι-rule subset that
`headStep?` currently fires).

Proof: induction on fuel.
* `fuel = 0`: `eval 0 t = ⟨_, t⟩`, so `StepStar.refl t`.
* `fuel = n + 1`: case on `t.headStep?`:
  - `none`: `eval (n+1) t = ⟨_, t⟩`, `StepStar.refl t`.
  - `some ⟨_, reducedTerm⟩`: per `headStep?_sound`,
    `Step t reducedTerm`; per IH on `n`, `StepStar reducedTerm
    (eval n reducedTerm).snd`; compose via `StepStar.step`.

Zero-axiom under strict policy. -/


variable {mode : Mode} {level : Nat}

theorem Term.eval_sound
    {scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope} :
    ∀ (fuel : Nat) (someTerm : Term context someType raw),
      StepStar someTerm (Term.eval fuel someTerm).snd
  | 0, someTerm => by
    -- `Term.eval 0 someTerm = ⟨_, someTerm⟩` by definition
    show StepStar someTerm someTerm
    exact StepStar.refl someTerm
  | fuel + 1, someTerm => by
    -- `Term.eval (fuel+1) someTerm = match someTerm.headStep? with ...`
    -- Case on the firing.
    match firedEq : someTerm.headStep? with
    | none =>
      -- eval returns ⟨_, someTerm⟩
      show StepStar someTerm (Term.eval (fuel + 1) someTerm).snd
      rw [show (Term.eval (fuel + 1) someTerm)
            = (match someTerm.headStep? with
               | some ⟨_, reducedTerm⟩ => Term.eval fuel reducedTerm
               | none => ⟨_, someTerm⟩) from rfl, firedEq]
      exact StepStar.refl someTerm
    | some ⟨reducedRaw, reducedTerm⟩ =>
      -- eval continues with reducedTerm
      have firstStep : Step someTerm reducedTerm :=
        Term.headStep?_sound someTerm firedEq
      have tailChain : StepStar reducedTerm (Term.eval fuel reducedTerm).snd :=
        Term.eval_sound fuel reducedTerm
      show StepStar someTerm (Term.eval (fuel + 1) someTerm).snd
      rw [show (Term.eval (fuel + 1) someTerm)
            = (match someTerm.headStep? with
               | some ⟨_, reducedTerm⟩ => Term.eval fuel reducedTerm
               | none => ⟨_, someTerm⟩) from rfl, firedEq]
      exact StepStar.step firstStep tailChain

end LeanFX2
