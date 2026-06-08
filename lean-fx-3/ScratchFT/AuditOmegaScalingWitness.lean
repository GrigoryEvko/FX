import FX1Poly.Modal.GradedComposition

/-! Audit scratch: build a genuine r=ω substitution-scaling witness for graded SR.

Term under test (de Bruijn):
  ctx0 = [g] where g : base -(1)-> (base -(1)-> base)        (g is de Bruijn 0 at top level)
  lambda body (under λx, ctx = [x:base, g]) :  (g x) x  =  app (app (var 1) (var 0)) (var 0)
  redex = (λx. (g x) x) g    -- apply the duplicating lambda to g? No: arg must have type base.

Actually the argument must have type `domain = base`. We need a closed-ish redex with a base-typed
argument that is USED (so argGrades is non-trivial). Use a free var `z : base` as the argument.

Context: [z : base, g : base-(1)->base-(1)->base]  (z = db 0, g = db 1)
  Under λx:  ctx = [x:base, z:base, g]  (x=0, z=1, g=2)
  body (g x) x = app (app (var 2) (var 0)) (var 0)
  lambda binder grade for x = a+b = ω (a=b=1), outer grades over [z,g] = [z↦0, g↦1]
  redex = app (lam body) (var 0)   -- arg = var 0 = z : base
  argGrades(z) over [z,g] = single 2 0 1 = [z↦1, g↦0]

After β: body[0 := z] = (g z) z. Grade must be:
  functionGrades(λ at outer scope) + binderGrade(ω) · argGrades(z)
  = [z↦0, g↦1]  +  ω·[z↦1, g↦0]
  = [0,1] + [ω·1, ω·0] = [0,1] + [ω,0] = [ω, 1]
So z↦ω (used twice after β — exactly the duplication), g↦1.  THIS is the r=ω scaling firing.
-/

namespace FX1Poly.Modal

abbrev gType : GType := .arrow UsageGrade.one GType.base (.arrow UsageGrade.one GType.base GType.base)

/-- ctx for the redex: [z : base, g : base-(1)->base-(1)->base]. -/
abbrev redexCtx : List GType := [GType.base, gType]

/-- The duplicating lambda body, under λx: ctx [x:base, z:base, g] = (g x) x. -/
abbrev dupBody : GradedLambda := .app (.app (.var 2) (.var 0)) (.var 0)

/-- The redex (λx. (g x) x) z. -/
abbrev omegaRedex : GradedLambda := .app (.lam dupBody) (.var 0)

/-! ## Step 1: type the lambda body, read off the actual grade vector (binder grade = ω?). -/

-- `g x` : g = var 2 in [x:base, z:base, g], type arrow 1 base (arrow 1 base base); x = var 0 : base.
-- inner app grade = functionGrades(var2) + 1·argGrades(var0)
theorem inner_gx_typed :
    HasUsage [GType.base, GType.base, gType]
      (GradeVector.add (GradeVector.single 3 2 UsageGrade.one)
        (GradeVector.scale UsageGrade.one (GradeVector.single 3 0 UsageGrade.one)))
      (.app (.var 2) (.var 0))
      (.arrow UsageGrade.one GType.base GType.base) :=
  HasUsage.app [GType.base, GType.base, gType] UsageGrade.one GType.base
    (.arrow UsageGrade.one GType.base GType.base)
    (GradeVector.single 3 2 UsageGrade.one) (GradeVector.single 3 0 UsageGrade.one)
    (.var 2) (.var 0)
    (HasUsage.var [GType.base, GType.base, gType] 2 gType rfl)
    (HasUsage.var [GType.base, GType.base, gType] 0 GType.base rfl)

-- (g x) x : function = inner (type arrow 1 base base), arg = var 0 : base, binder grade 1.
theorem dupBody_typed :
    HasUsage [GType.base, GType.base, gType]
      (GradeVector.add
        (GradeVector.add (GradeVector.single 3 2 UsageGrade.one)
          (GradeVector.scale UsageGrade.one (GradeVector.single 3 0 UsageGrade.one)))
        (GradeVector.scale UsageGrade.one (GradeVector.single 3 0 UsageGrade.one)))
      dupBody GType.base :=
  HasUsage.app [GType.base, GType.base, gType] UsageGrade.one GType.base GType.base
    (GradeVector.add (GradeVector.single 3 2 UsageGrade.one)
      (GradeVector.scale UsageGrade.one (GradeVector.single 3 0 UsageGrade.one)))
    (GradeVector.single 3 0 UsageGrade.one)
    (.app (.var 2) (.var 0)) (.var 0)
    inner_gx_typed
    (HasUsage.var [GType.base, GType.base, gType] 0 GType.base rfl)

/-- The body's grade vector, fully computed: head (binder x) = ω, then z↦0, g↦1.
This shows the binder grade of x in the lambda is genuinely ω (used twice). -/
theorem dupBody_grade_is_omega_at_head :
    (GradeVector.add
      (GradeVector.add (GradeVector.single 3 2 UsageGrade.one)
        (GradeVector.scale UsageGrade.one (GradeVector.single 3 0 UsageGrade.one)))
      (GradeVector.scale UsageGrade.one (GradeVector.single 3 0 UsageGrade.one)))
    = GradeVector.cons UsageGrade.omega
        (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil)) :=
  rfl

end FX1Poly.Modal

namespace FX1Poly.Modal

/-! ## Step 2: type the lambda (binder grade ω), the redex, then β-reduce.
NOTE: body (g x) x : base, so the lambda is arrow ω base base; g (=var 1 here) : gType. -/

theorem dupLam_typed :
    HasUsage [GType.base, gType]
      (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil))
      (.lam dupBody)
      (.arrow UsageGrade.omega GType.base GType.base) := by
  have h := dupBody_typed
  rw [dupBody_grade_is_omega_at_head] at h
  exact HasUsage.lam [GType.base, gType] UsageGrade.omega GType.base GType.base
    (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil))
    dupBody h

theorem omegaRedex_typed :
    HasUsage [GType.base, gType]
      (GradeVector.add
        (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil))
        (GradeVector.scale UsageGrade.omega
          (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)))
      omegaRedex GType.base :=
  HasUsage.app [GType.base, gType] UsageGrade.omega GType.base GType.base
    (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil))
    (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)
    (.lam dupBody) (.var 0)
    dupLam_typed
    (HasUsage.var [GType.base, gType] 0 GType.base rfl)

/-- THE CORE FACT: redex grade [z↦0,g↦1] + ω·[z↦1,g↦0] reduces to [ω, 1].
ω·[1,0] = [ω,0], NOT [1,0]. With + instead of scaled-add it would be [1,1]; with scale-by-1 it
would be [1,1]. Only the correct ρ + ω·σ gives [ω,1]. -/
theorem omegaRedex_grade_computed :
    (GradeVector.add
      (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil))
      (GradeVector.scale UsageGrade.omega
        (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)))
    = GradeVector.cons UsageGrade.omega (GradeVector.cons UsageGrade.one GradeVector.nil) :=
  rfl

/-! ## Step 3: β-reduce via the headline SR lemma. -/

/-- `(λx. (g x) x) z ↝_β (g z) z`: contractum keeps EXACT grade [z↦ω, g↦1]. Genuine r=ω witness. -/
theorem omegaRedex_betaPreserves :
    HasUsage [GType.base, gType]
      (GradeVector.cons UsageGrade.omega (GradeVector.cons UsageGrade.one GradeVector.nil))
      (GradedLambda.substAt 0 (.var 0) dupBody) GType.base := by
  have h := hasUsage_betaPreservation omegaRedex_typed
  rw [omegaRedex_grade_computed] at h
  exact h

theorem contractum_is_gzz :
    GradedLambda.substAt 0 (.var 0) dupBody = .app (.app (.var 1) (.var 0)) (.var 0) :=
  rfl

/-- Independent cross-check: type (g z) z DIRECTLY (no β) and confirm grade [z↦ω,g↦1]. -/
theorem contractum_typed_directly :
    HasUsage [GType.base, gType]
      (GradeVector.cons UsageGrade.omega (GradeVector.cons UsageGrade.one GradeVector.nil))
      (.app (.app (.var 1) (.var 0)) (.var 0)) GType.base := by
  have step : HasUsage [GType.base, gType]
      (GradeVector.add
        (GradeVector.add (GradeVector.single [GType.base, gType].length 1 UsageGrade.one)
          (GradeVector.scale UsageGrade.one
            (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)))
        (GradeVector.scale UsageGrade.one
          (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)))
      (.app (.app (.var 1) (.var 0)) (.var 0)) GType.base :=
    HasUsage.app [GType.base, gType] UsageGrade.one GType.base GType.base
      (GradeVector.add (GradeVector.single [GType.base, gType].length 1 UsageGrade.one)
        (GradeVector.scale UsageGrade.one
          (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)))
      (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)
      (.app (.var 1) (.var 0)) (.var 0)
      (HasUsage.app [GType.base, gType] UsageGrade.one GType.base
        (.arrow UsageGrade.one GType.base GType.base)
        (GradeVector.single [GType.base, gType].length 1 UsageGrade.one)
        (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)
        (.var 1) (.var 0)
        (HasUsage.var [GType.base, gType] 1 gType rfl)
        (HasUsage.var [GType.base, gType] 0 GType.base rfl))
      (HasUsage.var [GType.base, gType] 0 GType.base rfl)
  have ev : (GradeVector.add
        (GradeVector.add (GradeVector.single [GType.base, gType].length 1 UsageGrade.one)
          (GradeVector.scale UsageGrade.one
            (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)))
        (GradeVector.scale UsageGrade.one
          (GradeVector.single [GType.base, gType].length 0 UsageGrade.one)))
      = GradeVector.cons UsageGrade.omega (GradeVector.cons UsageGrade.one GradeVector.nil) := rfl
  rw [ev] at step
  exact step

end FX1Poly.Modal

namespace FX1Poly.Modal
-- Confirm the r=ω witnesses are axiom-clean (no propext/sorry making them vacuous).
#print axioms omegaRedex_betaPreserves
#print axioms omegaRedex_grade_computed
#print axioms contractum_typed_directly
-- Also confirm the headline SR lemma itself is axiom-clean.
#print axioms hasUsage_betaPreservation
#print axioms hasUsage_substitution
#print axioms HasUsage.preservedByReduces
end FX1Poly.Modal
