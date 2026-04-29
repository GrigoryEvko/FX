import LeanFX.Syntax.Reduction.StepStar

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Definitional conversion (`Conv`).

Symmetric / reflexive / transitive closure of `Step`.  Minimal
constructors (`refl`, `sym`, `trans`, `fromStep`); structural-
congruence rules below are derived theorems. -/

/-- The conversion relation: equivalence closure of `Step` over
terms of the same type.  Subject preservation is definitional (the
relation's indices fix the type). -/
inductive Conv :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Reflexivity: every term is convertible with itself. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      Conv t t
  /-- Symmetry: convertibility is bidirectional. -/
  | sym :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₁
  /-- Transitivity: convertibility chains. -/
  | trans :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ t₃ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₃ → Conv t₁ t₃
  /-- Embedding: every single-step reduction is a conversion. -/
  | fromStep :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ : Term ctx T},
      Step t₁ t₂ → Conv t₁ t₂

/-- Multi-step reductions lift to conversions: a sequence of forward
steps is a conversion in the forward direction.  Proven by induction
on `StepStar`: the empty case is reflexivity, the step case composes
`fromStep` with the inductive hypothesis via `trans`. -/
theorem StepStar.toConv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} :
    StepStar t₁ t₂ → Conv t₁ t₂
  | .refl t       => Conv.refl t
  | .step s rest  => Conv.trans (Conv.fromStep s) (StepStar.toConv rest)

/-- Single-step reductions lift to conversions through the multi-step
intermediary.  Direct from `Conv.fromStep`; provided as a named
theorem for symmetry with `Step.toStar`. -/
theorem Step.toConv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : Conv t₁ t₂ :=
  Conv.fromStep h

/-! ## Conv structural congruences.

Make `Conv` a full congruence relation over the term constructors. -/

/-- Convertibility threads through the function position of `Term.app`. -/
theorem Conv.app_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.app f₁ a) (Term.app f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appLeft s)

/-- Convertibility threads through the argument position of `Term.app`. -/
theorem Conv.app_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.app f a₁) (Term.app f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appRight s)

/-- Convertibility threads through both positions of `Term.app`. -/
theorem Conv.app_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  Conv.trans (Conv.app_cong_left a₁ h_f) (Conv.app_cong_right f₂ h_a)

/-- Convertibility threads through the body of `Term.lam`. -/
theorem Conv.lam_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken}
    (h : Conv body₁ body₂) :
    Conv (Term.lam (codomainType := codomainType) body₁)
         (Term.lam (codomainType := codomainType) body₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.lamBody s)

/-- Convertibility threads through the body of `Term.lamPi`. -/
theorem Conv.lamPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType}
    (h : Conv body₁ body₂) :
    Conv (Term.lamPi (domainType := domainType) body₁)
         (Term.lamPi (domainType := domainType) body₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.lamPiBody s)

/-- Convertibility threads through the function position of `Term.appPi`. -/
theorem Conv.appPi_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.appPi f₁ a) (Term.appPi f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiLeft s)

/-- Convertibility threads through the argument position of `Term.appPi`. -/
theorem Conv.appPi_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.appPi f a₁) (Term.appPi f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiRight s)

/-- Convertibility threads through both positions of `Term.appPi`. -/
theorem Conv.appPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  Conv.trans (Conv.appPi_cong_left a₁ h_f) (Conv.appPi_cong_right f₂ h_a)

/-- Convertibility threads through the first component of `Term.pair`. -/
theorem Conv.pair_cong_first {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType))
    (h : Conv firstVal₁ firstVal₂) :
    Conv (Term.pair (firstType := firstType) (secondType := secondType)
                    firstVal₁ secondVal)
         (Term.pair (firstType := firstType) (secondType := secondType)
                    firstVal₂ secondVal) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.pairLeft s)

/-- Convertibility threads through the second component of `Term.pair`. -/
theorem Conv.pair_cong_second {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h : Conv secondVal₁ secondVal₂) :
    Conv (Term.pair firstVal secondVal₁)
         (Term.pair firstVal secondVal₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.pairRight s)

/-- Convertibility threads through both components of `Term.pair`. -/
theorem Conv.pair_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : Conv firstVal₁ firstVal₂)
    (h_second : Conv secondVal₁ secondVal₂) :
    Conv (Term.pair firstVal₁ secondVal₁)
         (Term.pair firstVal₂ secondVal₂) :=
  Conv.trans (Conv.pair_cong_first secondVal₁ h_first)
             (Conv.pair_cong_second firstVal₂ h_second)

/-- Convertibility threads through `Term.fst`. -/
theorem Conv.fst_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : Conv p₁ p₂) :
    Conv (Term.fst p₁) (Term.fst p₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.fstCong s)

/-- Convertibility threads through `Term.snd`. -/
theorem Conv.snd_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : Conv p₁ p₂) :
    Conv (Term.snd p₁) (Term.snd p₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.sndCong s)

/-! ## η-equivalence in natural direction.

`Step.eta*` are contractions (η-redex → underlying value); these
wrappers state η as `f ≡ λx. f x`, the form conversion algorithms
typically check. -/

/-- **η-equivalence for arrow**: `f ≡ λx. f x`. -/
theorem Term.eta_arrow_eq {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType)) :
    Conv f
         (Term.lam (codomainType := codomainType)
            (Term.app (Term.weaken domainType f)
                      (Term.var ⟨0, Nat.zero_lt_succ _⟩))) :=
  Conv.sym (Step.etaArrow f).toConv

/-- **η-equivalence for Σ**: `p ≡ pair (fst p) (snd p)`. -/
theorem Term.eta_sigma_eq {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (p : Term ctx (Ty.sigmaTy firstType secondType)) :
    Conv p
         (Term.pair (firstType := firstType)
                     (secondType := secondType)
            (Term.fst p) (Term.snd p)) :=
  Conv.sym (Step.etaSigma p).toConv

end LeanFX.Syntax
