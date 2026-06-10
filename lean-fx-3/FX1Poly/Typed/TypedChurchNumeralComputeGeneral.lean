import FX1Poly.Typed.TypedChurchNumeralFaithful
import FX1Poly.Typed.TypedChurchNumeralInhabitants
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/TypedChurchNumeralComputeGeneral — the GENERAL Church-numeral iteration computation

`TypedChurchNumeralIteration` shipped the iteration computation for the CONCRETE numerals `one`/`two`/`three`
applied to CONCRETE fixtures (`A=Type@0`, `f=Type@0`, `x=Type@1`) — concrete because the docstring there notes
"`subst0` threads the lifting fold, which only fully computes on CONCRETE closed arguments".  This file removes
BOTH restrictions at once:

  **`churchNumeral_appliedReducesToIterate_general` (★)** — for EVERY depth `n` and ANY closed (symbolic)
  `typeA`, `handlerF`, `baseX`:

      (churchNumeralLambda n) typeA handlerF baseX  ↝*  iteratedApplication n handlerF baseX     (= f^n x)

  the polymorphic iterator genuinely applies its step `n` times to its base, for an arbitrary step and base.

The key that the concrete fixtures sidestepped is that, with SYMBOLIC arguments, the three β-contractums do not
fall out by `rfl`; each is reshaped through the shipped substitution homomorphism `subst_iteratedApplication`
(firing 121 / #1008: `subst σ (iteratedApplication n f x) = iteratedApplication n (subst σ f) (subst σ x)`):

  * **`churchNumeral_substType`** (β1, the A-binder) — applying the UNUSED type argument discards the `A`-binder:
    `subst0 (λf.λx. f^n x) typeA = λf.λx. f^n x` (the iterate references `f`/`x`, never `A`, so the lifted
    singleton fixes both bound variables — `rfl` after `subst_iteratedApplication`).
  * **`churchNumeral_substStep`** (β2, the f-binder) — applying the step substitutes `f := handlerF`, weakened
    once under the remaining `x`-binder: `subst0 (λx. f^n x) handlerF = λx. (weaken handlerF)^n x`.
  * **`iteratedApplication_subst0_weaken_step`** (β3, the x-binder — the symbolic HEART) — applying the base
    substitutes `x := baseX` and cancels the weakening on the step:
    `subst0 ((weaken handlerF)^n x) baseX = handlerF^n baseX`, via `subst_iteratedApplication` +
    `weaken_subst_singleton` (`subst0 (weaken handlerF) baseX = handlerF`) + the innermost-variable rule
    (`subst0 (var 0) baseX = baseX`).

Crucially there is NO double-weaken here (the obstruction that blocks the symbolic S-combinator rule): each of the
three bound variables is weakened at most once, so the shipped single-`weaken` cancellation suffices.  The general
computation is pure ASSEMBLY over shipped substitution metatheory — NOT a new de Bruijn commutation lemma — which
corrects the earlier "needs a multi-lemma de Bruijn effort" assessment of this task.  `iteratedApplication_subst0_
weaken_step` is the reusable symbolic-heart reshape for any future "apply the base into an iterate" reasoning.

This SUBSUMES the concrete `churchOne/Two/Three_appliedReducesToIterate`: each is this theorem at a concrete
`n` and concrete fixtures.  Everything is the raw `Step` relation; no typing derivation is consulted (the numerals'
typing + SN live in `TypedChurchNumeralTyping` / `…Faithful`).

## Zero-axiom verification

The three reshapes are `subst_iteratedApplication` rewrites closed by `rfl` (R1/R2: the `subst`-over-`lamCell`
push is definitional, the bound-variable images are `rfl`) or by `weaken_subst_singleton` + the innermost-`var`
`rfl` (the heart).  The reduction chains three `Step.beta` β-steps — each with its contractum rewritten to the
reshaped form via `rw [← reshape]` — lifted through function-position congruences (`Step.cong .gen_app ()` +
`StepChildren.here` with explicitly-pinned scopes), composed by `StepStar.trans`.  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **The symbolic heart (β3): applying the base into the iterate.**  `subst0 ((weaken stepFn)^n (var 0)) base =
stepFn^n base` — the final β-contractum reshape.  Via `subst_iteratedApplication` + `weaken_subst_singleton`
(`subst0 (weaken stepFn) base = stepFn`) + the innermost-variable rule (`subst0 (var 0) base = base`).  Reusable
for any "apply the base into an iterate" reasoning; the de Bruijn content the concrete fixtures avoided. -/
theorem iteratedApplication_subst0_weaken_step (depth : Nat) (stepFn base : RawTerm 0) :
    RawTerm.subst0 (iteratedApplication depth (RawTerm.weaken stepFn)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) base
      = iteratedApplication depth stepFn base := by
  unfold RawTerm.subst0
  rw [subst_iteratedApplication]
  have stepEq : RawTerm.subst (RawTermSubst.singleton base) (RawTerm.weaken stepFn) = stepFn :=
    RawTerm.weaken_subst_singleton stepFn base
  have baseEq : RawTerm.subst (RawTermSubst.singleton base)
      (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) = base := rfl
  rw [stepEq, baseEq]

/-- **β1: applying the (unused) type argument discards the `A`-binder.**  `subst0 (λ(f:A→A).λ(x:A). f^n x) typeA
= λ(f: typeA→typeA).λ(x: weaken typeA). f^n x`.  Under T2 the two inner lambdas carry the A-referencing domains
`A→A` / `A`, so the type substitution rewrites them (the step domain to `typeA→typeA`, the base domain to
`weaken typeA`); the body iterate references only `f`/`x` (`var 1`/`var 0`), never `A`, so the doubly-lifted
singleton fixes it (`subst_iteratedApplication` + `rfl`).  The substituted domains are discarded by the SUBSEQUENT
β. -/
theorem churchNumeral_substType (depth : Nat) (typeA : RawTerm 0) :
    RawTerm.subst0
        (lamCell churchNumeralStepBinderDomain
          (lamCell churchNumeralBaseBinderDomain
            (iteratedApplication depth
              (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
              (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))) typeA
      = lamCell (piTyCodeCell typeA (RawTerm.weaken typeA))
          (lamCell (RawTerm.weaken typeA)
            (iteratedApplication depth
              (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
              (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))) := by
  unfold RawTerm.subst0 churchNumeralStepBinderDomain churchNumeralBaseBinderDomain
  show lamCell _ (lamCell _ (RawTerm.subst
      (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton typeA)))
      (iteratedApplication depth _ _))) = _
  rw [subst_iteratedApplication]
  rfl

/-- **β2: applying the step argument substitutes it for `f`.**  `subst0 (λ(x: weaken typeA). f^n x) handlerF =
λ(x: weaken² typeA). (weaken handlerF)^n x` — the step is weakened once under the remaining `x`-binder; the base
domain `weaken typeA` is weakened again by the lifted singleton.  The substituted base domain is discarded by the
final β. -/
theorem churchNumeral_substStep (depth : Nat) (typeA handlerF : RawTerm 0) :
    RawTerm.subst0
        (lamCell (RawTerm.weaken typeA)
          (iteratedApplication depth
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))) handlerF
      = lamCell typeA
          (iteratedApplication depth (RawTerm.weaken handlerF)
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) := by
  unfold RawTerm.subst0
  show lamCell (RawTerm.subst (RawTermSubst.singleton handlerF) (RawTerm.weaken typeA))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerF))
        (iteratedApplication depth _ _)) = _
  rw [RawTerm.weaken_subst_singleton typeA handlerF, subst_iteratedApplication]
  rfl

/-- ★ **The general Church-numeral iteration computation.**  For every depth `n` and ANY closed `typeA`,
`handlerF`, `baseX`, the numeral applied to all three β-reduces (three steps) to its iterate:
`(churchNumeralLambda n) typeA handlerF baseX ↝* iteratedApplication n handlerF baseX` (= `f^n x`).  The
polymorphic iterator genuinely iterates its step `n` times over its base — for an ARBITRARY step and base, not
just concrete fixtures.  Subsumes the concrete `churchOne/Two/Three_appliedReducesToIterate`. -/
theorem churchNumeral_appliedReducesToIterate_general (depth : Nat) (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda depth) typeA) handlerF) baseX)
      (iteratedApplication depth handlerF baseX) := by
  -- The two inner lambdas after the type binder, with their (A-referencing) domain annotations.  Under T2 each
  -- `lamCell` carries a domain, so the three β-steps substitute through annotated lambdas; the domains are
  -- discarded by the SUBSEQUENT β (annotation discarded at contraction), so the final iterate is unchanged.
  -- The intermediate reducts are left as literal `subst0` expressions and the body content is normalised by the
  -- `churchNumeral_iterateBody_*` lemmas, so the proof never needs the closed form of a substituted domain.
  have step1 : Step (appCell (churchNumeralLambda depth) typeA)
      (lamCell (piTyCodeCell typeA (RawTerm.weaken typeA))
        (lamCell (RawTerm.weaken typeA)
          (iteratedApplication depth
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) := by
    rw [← churchNumeral_substType depth typeA]; exact Step.beta
  have step2 : Step
      (appCell (lamCell (piTyCodeCell typeA (RawTerm.weaken typeA))
        (lamCell (RawTerm.weaken typeA)
          (iteratedApplication depth
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) handlerF)
      (lamCell typeA
        (iteratedApplication depth (RawTerm.weaken handlerF)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) := by
    rw [← churchNumeral_substStep depth typeA handlerF]; exact Step.beta
  have step3 : Step
      (appCell (lamCell typeA
        (iteratedApplication depth (RawTerm.weaken handlerF)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) baseX)
      (iteratedApplication depth handlerF baseX) := by
    rw [← iteratedApplication_subst0_weaken_step depth handlerF baseX]; exact Step.beta
  exact StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons baseX .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons handlerF .childNil) step1))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          (.childCons baseX .childNil) step2))
      (StepStar.trans step3 (StepStar.refl _)))

end FX1Poly.Typed
