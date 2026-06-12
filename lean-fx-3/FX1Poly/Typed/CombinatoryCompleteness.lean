import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/CombinatoryCompleteness — `S K K x ↝* x` (SKK behaves as the identity)

`CombinatoryLogic` (#1015) shipped the S/K/I combinator basis as SN normal-form values with the I-rule and
K-rule.  This file delivers the classic combinatory-completeness identity:

  **`skkReducesToIdentity` (★)** — `S K K x ↝* x` for every `x`: the combinator `S K K` behaves as the identity
  when applied.  The reduction runs `S K K x ↝ Sa K x ↝ Sab x ↝ K x (K x) ↝* x`, where the first two β-steps
  contract `S K` and then `(S K) K` (the intermediate reducts `Sa = λy.λz. (Kz)(yz)` and `Sab = λz. (Kz)(Kz)`
  compute by `rfl` — crucially with the CONCRETE `K`, the under-binder `subst`-through-`weaken` collapses
  definitionally, where the general `S a b c` rule would need a weaken/subst commutation lemma), the third
  contracts `Sab x` to `K x (K x)`, and the final `K`-rule (`combinatorK_reduces`, #1015) selects `x`.

  **`skkApplied_conv_identityApplied`** — `S K K x` is convertible to `I x`: both reduce to `x`, so the two
  combinator terms agree definitionally when applied.  Combinatory completeness in miniature — `SKK` is `I`.

The fully general S-rule `S a b c ↝* (a c)(b c)` for arbitrary `a, b, c` is NOT proved here: with symbolic
arguments the intermediate `subst (lift (singleton b)) (weaken² a)` does not reduce to `weaken a` by `rfl` (it
needs a weaken/subst commutation lemma), so that remains a separate de Bruijn exercise.  `S K K` works precisely
because the concrete closed `K` makes every substitution compute.

Everything is the raw `Step`/`Conv` relations; no typing derivation is consulted.

## Zero-axiom verification

`skkReducesToIdentity` chains three `Step.beta` β-steps (the first two lifted through function-position
congruences `Step.cong .gen_app ()` + `StepChildren.here` with explicitly-pinned scopes; the intermediate reducts
`saTerm`/`sabTerm` are `rfl`-definitional contractums) with the shipped `combinatorK_reduces`, composed by
`StepStar.trans`.  `skkApplied_conv_identityApplied` is two `Conv.fromStepStar`s to the common reduct `x` joined
by `Conv.trans`/`Conv.sym`.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.
Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- The intermediate reduct `S a = λy. λz. ((weaken² a) z) (y z)` — the β-contractum of `appCell S a`.  The two
remaining λ-binders carry the Church domain annotation (`combinatorDomainAnn`, the closed `universeCodeCell`
domain that `combinatorS`'s binders are annotated with; it survives `subst`/`weaken` unchanged so the
contractum stays `rfl`-definitional under the T2 two-child λ). -/
def saTerm (a : RawTerm 0) : RawTerm 0 :=
  lamCell combinatorDomainAnn (lamCell combinatorDomainAnn (appCell
    (appCell (RawTerm.weaken (RawTerm.weaken a)) (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
      (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))))

/-- The intermediate reduct `S a b = λz. ((weaken a) z) ((weaken b) z)` — the β-contractum of `appCell (S a) b`
(definitional when `a`, `b` are concrete closed terms).  The remaining λ-binder carries the
`combinatorDomainAnn` domain annotation (the closed `universeCodeCell` that `combinatorS`'s binders use). -/
def sabTerm (a b : RawTerm 0) : RawTerm 0 :=
  lamCell combinatorDomainAnn (appCell
    (appCell (RawTerm.weaken a) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
    (appCell (RawTerm.weaken b) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))

/-- ★ **`S K K x ↝* x`** — the combinator `S K K` behaves as the identity when applied.  `S K K x` β-reduces
through `S K → λy.λz.(Kz)(yz)` and `(S K) K → λz.(Kz)(Kz)` (the intermediate reducts are `rfl`-definitional
because `K` is concrete and closed) to `K x (K x)`, which the K-rule then selects to `x`.  Combinatory
completeness: `SKK` is the identity. -/
theorem skkReducesToIdentity (arg : RawTerm 0) :
    StepStar (appCell (appCell (appCell combinatorS combinatorK) combinatorK) arg) arg := by
  have step1 : Step (appCell (appCell (appCell combinatorS combinatorK) combinatorK) arg)
      (appCell (appCell (saTerm combinatorK) combinatorK) arg) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons arg .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons combinatorK .childNil) HeadStep.beta.toStep)))
  have step2 : Step (appCell (appCell (saTerm combinatorK) combinatorK) arg)
      (appCell (sabTerm combinatorK combinatorK) arg) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons arg .childNil) HeadStep.beta.toStep)
  have step3 : Step (appCell (sabTerm combinatorK combinatorK) arg)
      (appCell (appCell combinatorK arg) (appCell combinatorK arg)) := HeadStep.beta.toStep
  exact StepStar.trans step1 (StepStar.trans step2 (StepStar.trans step3
    (combinatorK_reduces arg (appCell combinatorK arg))))

/-- `S K K x` is convertible to `I x`: both reduce to `x`, so `SKK` and `I` agree definitionally when applied. -/
theorem skkApplied_conv_identityApplied (arg : RawTerm 0) :
    Conv (appCell (appCell (appCell combinatorS combinatorK) combinatorK) arg)
      (appCell combinatorI arg) :=
  Conv.trans (Conv.fromStepStar (skkReducesToIdentity arg))
    (Conv.sym (Conv.fromStepStar (StepStar.trans (combinatorI_reduces arg) (StepStar.refl _))))

end FX1Poly.Typed
