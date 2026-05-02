import LeanFX.Syntax.Reduction.Step

/-! # Multi-step reduction (`StepStar`).

Reflexive-transitive closure of single-step `Step` plus the
structural congruences threading multi-step reduction through
each constructor of `Term`.

Layout:

  * `StepStar` — inductive with `refl` and `step`.  Same
    `{ctx} {T}` indices as `Step`, so subject reduction is
    structural (no separate theorem to state).
  * `Step.toStar` — single steps lift to multi-step.
  * `StepStar.trans` — transitivity, load-bearing for the
    eventual conversion algorithm.
  * Per-position congruences (`app_cong_left`,
    `app_cong_right`, `pair_cong_first`, `pair_cong_second`,
    `appPi_cong_left`, `appPi_cong_right`) and their combined
    forms (`app_cong`, `pair_cong`, `appPi_cong`) plus
    `lam_cong`, `lamPi_cong`, `fst_cong`, `snd_cong`.

The parallel-reduction multi-step counterpart `Step.parStar`
lives in `Reduction.ParSubst` (built on `Step.par` from
`Reduction.Par`), where the analogous chain congruences are
proved against `Step.par` instead. -/

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-- Reflexive-transitive closure of `Step` — multi-step reduction.
Captures the eventual reach of the reduction relation. -/
inductive StepStar :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Zero-step: a term reduces to itself. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      StepStar t t
  /-- Prepend a single step to an existing multi-step path. -/
  | step :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ t₃ : Term ctx T},
      Step t₁ t₂ → StepStar t₂ t₃ → StepStar t₁ t₃

/-! Subject reduction is **structural** in this kernel: `Step`,
`StepStar`, and `Conv` (introduced below) all share their
`{ctx} {T}` indices between input and output terms, so every
well-typed input produces a well-typed output by the relations'
signatures alone.  No inductive subject-reduction theorem to state
— the typing is in the relation's type. -/

/-- Single steps lift to multi-step. -/
theorem Step.toStar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : StepStar t₁ t₂ :=
  StepStar.step h (StepStar.refl t₂)

/-- Transitivity of multi-step reduction.  Together with `refl` this
makes `StepStar` an equivalence-relation-like object and is
load-bearing for the eventual conversion algorithm — in particular
for showing common-reducts when comparing terms. -/
theorem StepStar.trans
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → StepStar t₂ t₃ → StepStar t₁ t₃
  | .refl _, h         => h
  | .step s rest, h    => .step s (StepStar.trans rest h)

/-- Append a single step to an existing multi-step path — companion
to `StepStar.step` (which prepends).  Both directions are useful for
trace manipulation in conversion algorithms. -/
theorem StepStar.append
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → Step t₂ t₃ → StepStar t₁ t₃ :=
  fun stars step =>
    StepStar.trans stars (Step.toStar step)

/-- **Generic StepStar lifter**: lift a multi-step reduction through
any term-context-changing function `mapTerm` whose single-step
reduction has a matching lifter.  Source and target may live in
different contexts and at different scopes — needed by binder cong
rules whose source body is in `ctx.cons _`.  Generic proof pattern
behind the constructor-specific `StepStar.*_cong` lemmas. -/
theorem StepStar.mapStep
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    (mapTerm : Term sourceCtx sourceType → Term targetCtx targetType)
    (mapSingleStep :
      ∀ {beforeTerm afterTerm : Term sourceCtx sourceType},
        Step beforeTerm afterTerm →
        Step (mapTerm beforeTerm) (mapTerm afterTerm)) :
    ∀ {beforeTerm afterTerm : Term sourceCtx sourceType},
      StepStar beforeTerm afterTerm →
      StepStar (mapTerm beforeTerm) (mapTerm afterTerm)
  | _, _, .refl _ => StepStar.refl _
  | _, _, .step singleStep remainingSteps =>
      StepStar.step (mapSingleStep singleStep)
        (StepStar.mapStep mapTerm mapSingleStep remainingSteps)

/-! ## StepStar structural congruences.

Multi-step threading through each constructor.  Per-position and
combined forms; induction on `StepStar` with `refl`/`step` arms. -/

/-- Multi-step reduction threads through the function position of `Term.app`. -/
theorem StepStar.app_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) (h : StepStar f₁ f₂) :
    StepStar (Term.app f₁ a) (Term.app f₂ a) :=
  StepStar.mapStep (fun functionTerm => Term.app functionTerm a) Step.appLeft h

/-- Multi-step reduction threads through the argument position of `Term.app`. -/
theorem StepStar.app_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : StepStar a₁ a₂) :
    StepStar (Term.app f a₁) (Term.app f a₂) :=
  StepStar.mapStep (fun argumentTerm => Term.app f argumentTerm) Step.appRight h

/-- Multi-step reduction threads through both positions of `Term.app`. -/
theorem StepStar.app_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  StepStar.trans (StepStar.app_cong_left a₁ h_f)
                 (StepStar.app_cong_right f₂ h_a)

/-- Multi-step reduction threads through the body of `Term.lam`. -/
theorem StepStar.lam_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken}
    (h : StepStar body₁ body₂) :
    StepStar (Term.lam (codomainType := codomainType) body₁)
             (Term.lam (codomainType := codomainType) body₂) :=
  StepStar.mapStep (Term.lam (codomainType := codomainType)) Step.lamBody h

/-- Multi-step reduction threads through the body of `Term.lamPi`. -/
theorem StepStar.lamPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType}
    (h : StepStar body₁ body₂) :
    StepStar (Term.lamPi (domainType := domainType) body₁)
             (Term.lamPi (domainType := domainType) body₂) :=
  StepStar.mapStep (Term.lamPi (domainType := domainType)) Step.lamPiBody h

/-- Multi-step reduction threads through the function position of `Term.appPi`.
W9.B1.1 — uses `rfl` for the equation-bearing appPi's resultEq. -/
theorem StepStar.appPi_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) (h : StepStar f₁ f₂) :
    StepStar (Term.appPi rfl f₁ a) (Term.appPi rfl f₂ a) :=
  StepStar.mapStep (fun functionTerm => Term.appPi rfl functionTerm a)
    Step.appPiLeft h

/-- Multi-step reduction threads through the argument position of `Term.appPi`. -/
theorem StepStar.appPi_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : StepStar a₁ a₂) :
    StepStar (Term.appPi rfl f a₁) (Term.appPi rfl f a₂) :=
  StepStar.mapStep (fun argumentTerm => Term.appPi rfl f argumentTerm)
    Step.appPiRight h

/-- Multi-step reduction threads through both positions of `Term.appPi`. -/
theorem StepStar.appPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.appPi rfl f₁ a₁) (Term.appPi rfl f₂ a₂) :=
  StepStar.trans (StepStar.appPi_cong_left a₁ h_f)
                 (StepStar.appPi_cong_right f₂ h_a)

/-- Multi-step reduction threads through the first component of `Term.pair`. -/
theorem StepStar.pair_cong_first {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType))
    (h : StepStar firstVal₁ firstVal₂) :
    StepStar
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₁ secondVal)
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₂ secondVal) :=
  StepStar.mapStep
    (fun firstTerm => Term.pair (firstType := firstType)
                                (secondType := secondType) firstTerm secondVal)
    Step.pairLeft h

/-- Multi-step reduction threads through the second component of `Term.pair`. -/
theorem StepStar.pair_cong_second {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h : StepStar secondVal₁ secondVal₂) :
    StepStar (Term.pair firstVal secondVal₁)
             (Term.pair firstVal secondVal₂) :=
  StepStar.mapStep
    (fun secondTerm => Term.pair (firstType := firstType)
                                 (secondType := secondType) firstVal secondTerm)
    Step.pairRight h

/-- Multi-step reduction threads through both components of `Term.pair`. -/
theorem StepStar.pair_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : StepStar firstVal₁ firstVal₂)
    (h_second : StepStar secondVal₁ secondVal₂) :
    StepStar (Term.pair firstVal₁ secondVal₁)
             (Term.pair firstVal₂ secondVal₂) :=
  StepStar.trans (StepStar.pair_cong_first secondVal₁ h_first)
                 (StepStar.pair_cong_second firstVal₂ h_second)

/-- Multi-step reduction threads through `Term.fst`. -/
theorem StepStar.fst_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : StepStar p₁ p₂) :
    StepStar (Term.fst p₁) (Term.fst p₂) :=
  StepStar.mapStep (Term.fst (firstType := firstType) (secondType := secondType))
    Step.fstCong h

/-- Multi-step reduction threads through `Term.snd`.  W9.B1.2:
`Term.snd` requires `rfl` for resultEq. -/
theorem StepStar.snd_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : StepStar p₁ p₂) :
    StepStar (Term.snd p₁ rfl) (Term.snd p₂ rfl) :=
  StepStar.mapStep
    (fun pairTerm => Term.snd (firstType := firstType)
      (secondType := secondType) pairTerm rfl)
    Step.sndCong h


end LeanFX.Syntax
