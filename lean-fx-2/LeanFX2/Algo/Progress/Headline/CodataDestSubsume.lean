import LeanFX2.Algo.Progress.Headline.Prelude

/-! # LeanFX2.Algo.Progress.Headline.CodataDestSubsume

Trivial unconditional-WHNF progress theorems for the
`Term.codataDest` and `Term.subsume` conditional eliminators.

Both are placeholders for future kernel extensions: the typed
β rules `Step.betaCodataDestObservation` and
`Step.betaSubsumeIntro` do not yet ship, so both terms are
classified as WHNF unconditionally (matches `Algo/WHNF/Evaluator.lean`).

Carved out of the monolithic `LeanFX2/Algo/Progress/Headline.lean`
for compile-time parallelism (per-Term-head sub-modules).
Zero-axiom under strict policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Focused progress theorem for the `Term.codataDest` head.
M05.D.2 conditional eliminator #8 of 17.  Currently a trivial
unconditional WHNF case: the raw layer ships no codata
observation β rule yet (`Term.isWHNF (Term.codataDest _) = true`
unconditionally per `Algo/WHNF/Evaluator.lean:382`).  When the
β rule lands this theorem will expand to the standard
firing/non-firing pattern. -/
theorem Term.codataDest_progress_or_step
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue :
      Term context (Ty.codata stateType outputType) codataRaw) :
    Term.isWHNF (Term.codataDest codataValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.codataDest codataValue) target := Or.inl rfl

/-- Focused progress theorem for the `Term.subsume` head.
M05.D.2 conditional eliminator #9 of 17.  Trivial unconditional
WHNF case: `Term.isWHNF (Term.subsume _) = true` holds by
definition (no typed β rule `Step.betaSubsumeIntro` exists yet;
spec-blocker for M05.B.5.2 `Term.subsume_modIntro_steps` per the
docstring in `BetaIotaStepProvability.lean:326`).  Placeholder
for future kernel extension. -/
theorem Term.subsume_progress_or_step
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Term.isWHNF (Term.subsume innerTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.subsume innerTerm) target := Or.inl rfl

end LeanFX2
