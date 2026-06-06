import FX1Poly.Modal.SimpleTyping

/-! # FX1Poly/Modal/SimpleStrongNormalization — STLC strong normalization

The orthogonal-composition thesis: the usage dimension does NOT need its own strong-
normalization argument; graded-SN rides on the TYPE dimension's SN through grade erasure
(`HasUsage.erase`), because the term and the β-reduction are grade-AGNOSTIC.  So the only
SN obligation is the TYPE dimension's: `HasSimpleType Γ t T → IsStronglyNormalizing t` (the classic
STLC Tait result), proved ONCE.  Graded-SN is then the trivial corollary `HasUsage → erase → SN`.

This file builds that STLC-SN.  **The reduction + SN substrate** the Tait
reducibility argument consumes:

  * `GradedLambda.Reduces` — full one-step β (root β + congruence everywhere).
  * `GradedLambda.IsStronglyNormalizing` — accessibility under reduction (no infinite reduction
    sequence), mirroring the kernel's RawTerm `IsStronglyNormalizing`.
  * `GradedLambda.IsNeutral` — non-introduction forms (var / app); the CR3 head-expansion condition
    is stated for neutral terms.
  * SN structural lemmas: a variable is SN (`var`); SN passes to subterms (`ofAppLeft` / `ofAppRight`
    / `ofLam`); SN is forward-closed under reduction (`ofReduces`).

The type-indexed reducibility predicate + the candidate conditions CR1/CR2/CR3, the fundamental theorem
under a closing substitution, the SN corollary, and the trivial transfer to graded-SN live in
`GradedFundamentalTheorem.lean`.

## Zero-axiom verification

`Reduces` is a plain inductive; `IsStronglyNormalizing` is `Acc`; the structural lemmas are
`Acc`-eliminator inductions with the `subst`-an-equation generalization (NOT `brecOn`); `var` uses
`cases` on the indexed reduction, which is propext-free because `GradedLambda` is a plain inductive
(cross-constructor discrimination via `GradedLambda.noConfusion`).  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.
-/

namespace FX1Poly.Modal

/-- Full one-step β-reduction on `GradedLambda` (root β + congruence everywhere). -/
inductive GradedLambda.Reduces : GradedLambda → GradedLambda → Prop where
  | beta (body argument : GradedLambda) :
      GradedLambda.Reduces (.app (.lam body) argument) (GradedLambda.substAt 0 argument body)
  | congLam (body body' : GradedLambda) (step : GradedLambda.Reduces body body') :
      GradedLambda.Reduces (.lam body) (.lam body')
  | congAppLeft (function function' argument : GradedLambda)
      (step : GradedLambda.Reduces function function') :
      GradedLambda.Reduces (.app function argument) (.app function' argument)
  | congAppRight (function argument argument' : GradedLambda)
      (step : GradedLambda.Reduces argument argument') :
      GradedLambda.Reduces (.app function argument) (.app function argument')

/-- Strong normalization: accessibility under reduction (no infinite reduction sequence). -/
def GradedLambda.IsStronglyNormalizing (term : GradedLambda) : Prop :=
  Acc (fun reduct source => GradedLambda.Reduces source reduct) term

/-- Neutral terms (not an introduction form): variable or application.  The CR3 head-expansion
condition is stated for neutral terms. -/
def GradedLambda.IsNeutral : GradedLambda → Prop
  | .var _ => True
  | .lam _ => False
  | .app _ _ => True

/-- A variable is strongly normalizing (it has no reducts). -/
theorem GradedLambda.IsStronglyNormalizing.var (index : Nat) :
    GradedLambda.IsStronglyNormalizing (GradedLambda.var index) := by
  apply Acc.intro
  intro reduct step
  cases step

/-- SN of an application's function part. -/
theorem GradedLambda.IsStronglyNormalizing.ofAppLeft {function argument : GradedLambda}
    (snApp : GradedLambda.IsStronglyNormalizing (.app function argument)) :
    GradedLambda.IsStronglyNormalizing function := by
  have generalized : ∀ (term : GradedLambda), GradedLambda.IsStronglyNormalizing term →
      ∀ (fn arg : GradedLambda), term = GradedLambda.app fn arg →
        GradedLambda.IsStronglyNormalizing fn := by
    intro term snTerm
    induction snTerm with
    | intro term _ reductIH =>
        intro fn arg termEq
        subst termEq
        exact Acc.intro fn (fun fn' stepFn =>
          reductIH (GradedLambda.app fn' arg)
            (GradedLambda.Reduces.congAppLeft fn fn' arg stepFn) fn' arg rfl)
  exact generalized (GradedLambda.app function argument) snApp function argument rfl

/-- SN of an application's argument part. -/
theorem GradedLambda.IsStronglyNormalizing.ofAppRight {function argument : GradedLambda}
    (snApp : GradedLambda.IsStronglyNormalizing (.app function argument)) :
    GradedLambda.IsStronglyNormalizing argument := by
  have generalized : ∀ (term : GradedLambda), GradedLambda.IsStronglyNormalizing term →
      ∀ (fn arg : GradedLambda), term = GradedLambda.app fn arg →
        GradedLambda.IsStronglyNormalizing arg := by
    intro term snTerm
    induction snTerm with
    | intro term _ reductIH =>
        intro fn arg termEq
        subst termEq
        exact Acc.intro arg (fun arg' stepArg =>
          reductIH (GradedLambda.app fn arg')
            (GradedLambda.Reduces.congAppRight fn arg arg' stepArg) fn arg' rfl)
  exact generalized (GradedLambda.app function argument) snApp function argument rfl

/-- SN of a lambda's body. -/
theorem GradedLambda.IsStronglyNormalizing.ofLam {body : GradedLambda}
    (snLam : GradedLambda.IsStronglyNormalizing (.lam body)) :
    GradedLambda.IsStronglyNormalizing body := by
  have generalized : ∀ (term : GradedLambda), GradedLambda.IsStronglyNormalizing term →
      ∀ (innerBody : GradedLambda), term = GradedLambda.lam innerBody →
        GradedLambda.IsStronglyNormalizing innerBody := by
    intro term snTerm
    induction snTerm with
    | intro term _ reductIH =>
        intro innerBody termEq
        subst termEq
        exact Acc.intro innerBody (fun body' stepBody =>
          reductIH (GradedLambda.lam body') (GradedLambda.Reduces.congLam innerBody body' stepBody)
            body' rfl)
  exact generalized (GradedLambda.lam body) snLam body rfl

/-- SN is forward-closed under reduction (a reduct of an SN term is SN). -/
theorem GradedLambda.IsStronglyNormalizing.ofReduces {source reduct : GradedLambda}
    (snSource : GradedLambda.IsStronglyNormalizing source)
    (step : GradedLambda.Reduces source reduct) :
    GradedLambda.IsStronglyNormalizing reduct :=
  snSource.inv step

/-! ## Tait reducibility candidates

The type-indexed reducibility predicate + the three candidate conditions.  The arrow candidate
INCLUDES SN of the term itself (saturated-set formulation), so CR1 is a direct projection rather
than needing the apply-to-a-reducible-variable trick. -/

/-- Tait reducibility, by recursion on the simple type.  At `base` it is just SN; at `arrow A B` it
is SN together with "sends reducible arguments to reducible results". -/
def GradedLambda.Reducible : SimpleType → GradedLambda → Prop
  | .base, term => GradedLambda.IsStronglyNormalizing term
  | .arrow domain codomain, term =>
      GradedLambda.IsStronglyNormalizing term ∧
        ∀ (argument : GradedLambda), GradedLambda.Reducible domain argument →
          GradedLambda.Reducible codomain (.app term argument)

/-- **The reducibility-candidate conditions** CR1 (reducible ⟹ SN), CR2 (forward closure under
reduction), CR3 (neutral head-expansion), proved by simultaneous induction on the type.  The
arrow-CR3 case nests an induction on `IsStronglyNormalizing argument`; its β-subcase is impossible
because the function head is neutral (`IsNeutral (lam _) = False`). -/
theorem GradedLambda.reducibilityConditions : ∀ (ty : SimpleType),
    (∀ (term : GradedLambda), GradedLambda.Reducible ty term →
        GradedLambda.IsStronglyNormalizing term) ∧
    (∀ (source reduct : GradedLambda), GradedLambda.Reducible ty source →
        GradedLambda.Reduces source reduct → GradedLambda.Reducible ty reduct) ∧
    (∀ (term : GradedLambda), GradedLambda.IsNeutral term →
        (∀ (reduct : GradedLambda), GradedLambda.Reduces term reduct →
          GradedLambda.Reducible ty reduct) →
        GradedLambda.Reducible ty term) := by
  intro ty
  induction ty with
  | base =>
      refine ⟨fun term red => red, fun source reduct redSource step => redSource.ofReduces step,
        fun term _ allReducts => ?_⟩
      exact Acc.intro term allReducts
  | arrow domain codomain ihDomain ihCodomain =>
      obtain ⟨cr1Domain, cr2Domain, _⟩ := ihDomain
      obtain ⟨_, cr2Codomain, cr3Codomain⟩ := ihCodomain
      refine ⟨fun term red => red.1, ?_, ?_⟩
      · intro source reduct redSource step
        exact ⟨redSource.1.ofReduces step, fun argument redArg =>
          cr2Codomain (GradedLambda.app source argument) (GradedLambda.app reduct argument)
            (redSource.2 argument redArg)
            (GradedLambda.Reduces.congAppLeft source reduct argument step)⟩
      · intro term neutralTerm allReducts
        refine ⟨Acc.intro term (fun reduct step => (allReducts reduct step).1), ?_⟩
        have appReducible : ∀ (argument : GradedLambda),
            GradedLambda.IsStronglyNormalizing argument →
              GradedLambda.Reducible domain argument →
                GradedLambda.Reducible codomain (GradedLambda.app term argument) := by
          intro argument snArg
          induction snArg with
          | intro argument _ argIH =>
              intro redArg
              refine cr3Codomain (GradedLambda.app term argument) True.intro ?_
              intro reduct stepApp
              cases stepApp with
              | beta body argument' => exact neutralTerm.elim
              | congAppLeft fn fn' arg stepFn => exact (allReducts fn' stepFn).2 argument redArg
              | congAppRight fn arg arg' stepArg =>
                  exact argIH arg' stepArg (cr2Domain argument arg' redArg stepArg)
        exact fun argument redArg => appReducible argument (cr1Domain argument redArg) redArg

/-- CR1: a reducible term is strongly normalizing. -/
theorem GradedLambda.Reducible.sn {ty : SimpleType} {term : GradedLambda}
    (red : GradedLambda.Reducible ty term) : GradedLambda.IsStronglyNormalizing term :=
  (GradedLambda.reducibilityConditions ty).1 term red

/-- CR2: reducibility is forward-closed under reduction. -/
theorem GradedLambda.Reducible.ofReduces {ty : SimpleType} {source reduct : GradedLambda}
    (red : GradedLambda.Reducible ty source) (step : GradedLambda.Reduces source reduct) :
    GradedLambda.Reducible ty reduct :=
  (GradedLambda.reducibilityConditions ty).2.1 source reduct red step

/-- CR3: a neutral term all of whose reducts are reducible is itself reducible. -/
theorem GradedLambda.Reducible.ofNeutral {ty : SimpleType} {term : GradedLambda}
    (neutral : GradedLambda.IsNeutral term)
    (allReducts : ∀ (reduct : GradedLambda), GradedLambda.Reduces term reduct →
      GradedLambda.Reducible ty reduct) :
    GradedLambda.Reducible ty term :=
  (GradedLambda.reducibilityConditions ty).2.2 term neutral allReducts

/-- A variable is reducible at every type (neutral with no reducts, via CR3) — the base case of the
fundamental theorem's closing-substitution environment. -/
theorem GradedLambda.Reducible.var (ty : SimpleType) (index : Nat) :
    GradedLambda.Reducible ty (GradedLambda.var index) :=
  GradedLambda.Reducible.ofNeutral True.intro (by intro reduct step; cases step)

end FX1Poly.Modal
