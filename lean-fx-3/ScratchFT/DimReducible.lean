import FX1Poly.Modal.SimpleStrongNormalization

/-! Scratch probe (DIM2-5 ii): the Tait reducibility predicate + candidate conditions CR1/CR2/CR3.
The arrow candidate INCLUDES SN (saturated-set style), so CR1 is a projection.  CR3-arrow nests an
induction on SN(argument); the β-case is discharged by `IsNeutral (lam _) = False`. -/

namespace FX1Poly.Modal

/-- Tait reducibility, by recursion on the simple type.  The arrow candidate includes SN of the term
itself (saturated-set formulation) so that CR1 is a direct projection. -/
def GradedLambda.Reducible : SimpleType → GradedLambda → Prop
  | .base, term => GradedLambda.IsStronglyNormalizing term
  | .arrow domain codomain, term =>
      GradedLambda.IsStronglyNormalizing term ∧
        ∀ (argument : GradedLambda), GradedLambda.Reducible domain argument →
          GradedLambda.Reducible codomain (.app term argument)

/-- **The reducibility-candidate conditions** CR1 (reducible ⟹ SN), CR2 (forward closure under
reduction), CR3 (neutral head-expansion), proved by simultaneous induction on the type. -/
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
      · -- CR2
        intro source reduct redSource step
        exact ⟨redSource.1.ofReduces step, fun argument redArg =>
          cr2Codomain (GradedLambda.app source argument) (GradedLambda.app reduct argument)
            (redSource.2 argument redArg)
            (GradedLambda.Reduces.congAppLeft source reduct argument step)⟩
      · -- CR3
        intro term neutralTerm allReducts
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

/-- A variable is reducible at every type (neutral with no reducts, via CR3). -/
theorem GradedLambda.Reducible.var (ty : SimpleType) (index : Nat) :
    GradedLambda.Reducible ty (GradedLambda.var index) :=
  GradedLambda.Reducible.ofNeutral True.intro (by intro reduct step; cases step)

#print axioms GradedLambda.Reducible
#print axioms GradedLambda.reducibilityConditions
#print axioms GradedLambda.Reducible.sn
#print axioms GradedLambda.Reducible.ofReduces
#print axioms GradedLambda.Reducible.ofNeutral
#print axioms GradedLambda.Reducible.var

end FX1Poly.Modal
