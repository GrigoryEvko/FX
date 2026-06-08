import FX1Poly.Typed.CurryFixpointDivergence
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/CombinatoryLogic — the SKI combinator basis in the λ-fragment

The untyped FX term calculus realizes combinatory logic: the three primitive combinators

  `I = λx. x`,   `K = λx. λy. x`,   `S = λx. λy. λz. (x z) (y z)`

exist as closed `RawTerm 0`, each is a strongly-normalizing normal-form value, and `I`/`K` satisfy their
defining reduction rules:

  * **`combinator{I,K,S}_stronglyNormalizing`** — each combinator is a closed normal form (no outgoing `Step`,
    by `decide` on `isStepNormalForm`), hence strongly normalizing.  The bodies are λ-nested neutral applications
    of bound variables — no redex anywhere.

  * **`combinatorI_reduces`** — the I-rule `I a ↝ a` (a single `Step.beta`; `subst0 (var 0) a = a`).

  * **`combinatorK_reduces`** — the K-rule `K a b ↝* a` in two steps: a function-position β reduces `K a` to
    `λy. (weaken a)` (the under-binder substitution `subst0 (λy.x) a = λy.(weaken a)` computes by `rfl`), then
    the outer β contracts `(λy. weaken a) b` to `a` via the `subst0 (weaken a) b = a` cancellation
    (`weaken_subst_singleton`).

The S-rule (`S a b c ↝* (a c)(b c)`) and the combinatory-completeness identity `S K K x ↝* x` are deferred to a
follow-up (the 3-binder nested-weakening reduction needs the intermediate `Sa`/`Sab` terms discovered).

Everything is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

The SN facts use `isStronglyNormalizing_of_noStep` against `RawTerm.isStepNormalForm_blocks_step`, with normality
by `decide` (clean — `isStepNormalForm` inspects generators/structure, never compares `Fin` indices, so no
`propext` leak).  `combinatorI_reduces` is a bare `Step.beta`.  `combinatorK_reduces` composes a function-position
`Step.cong .gen_app ()` congruence with the outer β, the contractum rewritten by
`RawTerm.weaken_subst_singleton`.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.
Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `I = λx. x` — the identity combinator. -/
def combinatorI : RawTerm 0 := lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))

/-- `K = λx. λy. x` — the constant combinator (first projection). -/
def combinatorK : RawTerm 0 :=
  lamCell (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))

/-- `S = λx. λy. λz. (x z) (y z)` — the substitution/distribution combinator. -/
def combinatorS : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell
      (appCell (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))
      (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))))

/-- `I` is strongly normalizing — a closed normal-form value (`λx. x` has no outgoing `Step`). -/
theorem combinatorI_stronglyNormalizing : IsStronglyNormalizing combinatorI :=
  isStronglyNormalizing_of_noStep (fun target stp =>
    RawTerm.isStepNormalForm_blocks_step (by decide) target stp)

/-- `K` is strongly normalizing — a closed normal-form value (`λx. λy. x`, body a normal leaf). -/
theorem combinatorK_stronglyNormalizing : IsStronglyNormalizing combinatorK :=
  isStronglyNormalizing_of_noStep (fun target stp =>
    RawTerm.isStepNormalForm_blocks_step (by decide) target stp)

/-- `S` is strongly normalizing — a closed normal-form value (`λx. λy. λz. (xz)(yz)`, body neutral). -/
theorem combinatorS_stronglyNormalizing : IsStronglyNormalizing combinatorS :=
  isStronglyNormalizing_of_noStep (fun target stp =>
    RawTerm.isStepNormalForm_blocks_step (by decide) target stp)

/-- The **I-rule**: `I a ↝ a` — a single β-step (`subst0 (var 0) a = a`). -/
theorem combinatorI_reduces (a : RawTerm 0) : Step (appCell combinatorI a) a := Step.beta

/-- The **K-rule**: `K a b ↝* a` — `K a` β-reduces (in function position) to `λy. (weaken a)`, then the outer β
contracts that applied to `b` back to `a` (the `subst0 (weaken a) b = a` cancellation). -/
theorem combinatorK_reduces (a b : RawTerm 0) : StepStar (appCell (appCell combinatorK a) b) a := by
  have functionBeta : Step (appCell combinatorK a) (lamCell (RawTerm.weaken a)) := Step.beta
  have congStep : Step (appCell (appCell combinatorK a) b) (appCell (lamCell (RawTerm.weaken a)) b) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons b .childNil) functionBeta)
  have cancelEq : RawTerm.subst0 (RawTerm.weaken a) b = a := RawTerm.weaken_subst_singleton a b
  have outerBeta : Step (appCell (lamCell (RawTerm.weaken a)) b) (RawTerm.subst0 (RawTerm.weaken a) b) :=
    Step.beta
  rw [cancelEq] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

end FX1Poly.Typed
