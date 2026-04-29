import LeanFX.Syntax.Reduction.Step

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

/-! ## StepStar structural congruences.

Multi-step threading through each constructor.  Per-position and
combined forms; induction on `StepStar` with `refl`/`step` arms. -/

/-- Multi-step reduction threads through the function position of `Term.app`. -/
theorem StepStar.app_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.app f₁ a) (Term.app f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appLeft s) (StepStar.app_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.app`. -/
theorem StepStar.app_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.app f a₁) (Term.app f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appRight s) (StepStar.app_cong_right f rest)

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
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken} :
    StepStar body₁ body₂ →
    StepStar (Term.lam (codomainType := codomainType) body₁)
             (Term.lam (codomainType := codomainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamBody s) (StepStar.lam_cong rest)

/-- Multi-step reduction threads through the body of `Term.lamPi`. -/
theorem StepStar.lamPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType} :
    StepStar body₁ body₂ →
    StepStar (Term.lamPi (domainType := domainType) body₁)
             (Term.lamPi (domainType := domainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamPiBody s) (StepStar.lamPi_cong rest)

/-- Multi-step reduction threads through the function position of `Term.appPi`. -/
theorem StepStar.appPi_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.appPi f₁ a) (Term.appPi f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiLeft s)
        (StepStar.appPi_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.appPi`. -/
theorem StepStar.appPi_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.appPi f a₁) (Term.appPi f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiRight s)
        (StepStar.appPi_cong_right f rest)

/-- Multi-step reduction threads through both positions of `Term.appPi`. -/
theorem StepStar.appPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  StepStar.trans (StepStar.appPi_cong_left a₁ h_f)
                 (StepStar.appPi_cong_right f₂ h_a)

/-- Multi-step reduction threads through the first component of `Term.pair`. -/
theorem StepStar.pair_cong_first {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType)) :
    StepStar firstVal₁ firstVal₂ →
    StepStar
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₁ secondVal)
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₂ secondVal)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.pairLeft s)
        (StepStar.pair_cong_first secondVal rest)

/-- Multi-step reduction threads through the second component of `Term.pair`. -/
theorem StepStar.pair_cong_second {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)} :
    StepStar secondVal₁ secondVal₂ →
    StepStar (Term.pair firstVal secondVal₁)
             (Term.pair firstVal secondVal₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.pairRight s)
        (StepStar.pair_cong_second firstVal rest)

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
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.fst p₁) (Term.fst p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.fstCong s) (StepStar.fst_cong rest)

/-- Multi-step reduction threads through `Term.snd`. -/
theorem StepStar.snd_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.snd p₁) (Term.snd p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.sndCong s) (StepStar.snd_cong rest)


end LeanFX.Syntax
