import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility
import FX1Poly.Axis.Mode.FibrancyMode

/-! # FX1Poly/Typed/Engine/Classifier/LockModeIdentification — the kernel lock's obligation modality IS the
mode axis's fibrancy mode

`DimensionLockAccessibility` declares its own two-element `ObligationModality` (`.fibrant` / `.dimensional`)
and its own accessibility dispatcher, and its header says what that is:

> "The mode-axis-free specialization of MTT's TM/VAR 2-cell check for the single affine lock."

MODE-AXIS-FREE.  The mode axis independently declares `FibrancyKind` (`.fibrant` / `.exotype`), whose
`exotype` docstring reads "outer, non-fibrant types, WHERE THE INTERVAL / DIMENSIONAL FORMERS LIVE" — the same
two modes, declared twice, in two directories that do not import each other.  The duplicate exists because the
typed layer was built before `Axis/Mode/` did; it is not a design decision.

This file makes the identification a THEOREM rather than an observation, and it is the first brick of the
re-founding (LOCK-MODE-0): everything downstream rides on it, so it is proved before anything is moved.

## What is identified

  * **`obligationModalityToFibrancyKind` / `fibrancyKindToObligationModality`** with both round-trips — the
    MODE SET is the same two-element set (`.fibrant ↦ .fibrant`, `.dimensional ↦ .exotype`).
  * **`TypingContext.bindingFibrancyMode`** — the mode a binding SITS AT, read structurally off the telescope:
    a `cons` binding is at `.fibrant`, the `lockCons`-bound dimension is at `.exotype`, and both binders are
    transparent to bindings behind them (`locks(Gamma, x :^mu A) = locks(Gamma)`).
  * **★ THE SEMANTIC HALF (`isAccessibleAtModality_isModeMatch`)** — the kernel's bespoke two-branch
    dispatcher is EXACTLY "the binding's mode equals the use's mode":

        context.isAccessibleAtModality index modality
          = decide (context.bindingFibrancyMode index = obligationModalityToFibrancyKind modality)

    The mode-set iso alone would be cosmetic.  This is the row that says the kernel's ACCESSIBILITY is a mode
    fact, so the bespoke predicate can be retired onto the mode axis without a behaviour change.

## Why an EXACT match is the right mode-theoretic reading (and not a mismatch)

`fibrancyModeGraph` carries a generator `iota : exotype -> fibrant`, so it is tempting to read the kernel's
exact-match as contradicting the mode theory — if there is an arrow `e -> f`, why is the dimension not usable
fibrantly?  It is not a contradiction, and the confusion is worth recording because it is easy to re-derive:

  * `iota` is a **1-cell** — a modality you may APPLY (a lock you may push a term under).
  * MTT's TM/VAR rule does not ask for a 1-cell.  It asks for a **2-cell** `alpha : locks(Gamma') => mu`.
  * `fibrancyModeSignature.twoCell := fun _ _ => Empty` — "no non-trivial 2-cell GENERATORS"; the mode theory
    is THIN (MATT Example 2.5).  So the only 2-cells are identities, and `alpha` exists iff
    `locks(Gamma') = mu`.

An exact mode match IS the TM/VAR check over a thin mode theory.  The kernel's predicate was right; it was
just written without the vocabulary.  A consequence worth stating once: thin ⟹ no 2-cells ⟹ the polygraph
2-cell decision engine can never be load-bearing for THIS lock.  That is the mathematics, not a wiring gap.

## Zero-axiom

Structural recursion over the telescope with the `Fin` index destructured by the propext-free `⟨0, _⟩` /
`⟨position + 1, _⟩` pattern (the `TypingContext.lookup` recipe), full-enumeration matches on both two-element
sorts (no wildcard arm), and `rfl`-closed leaves.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Axis FX1Poly.Universe

/-! ## The mode set -/

/-- The kernel's obligation modality read as a fibrancy mode: a FIBRANT use position is the fibrant mode; a
DIMENSIONAL use position is the exotype mode (where, per its own docstring, the interval/dimensional formers
live). -/
def obligationModalityToFibrancyKind : ObligationModality → FibrancyKind
  | .fibrant => .fibrant
  | .dimensional => .exotype

/-- The inverse reading: the mode axis's fibrancy mode as a kernel obligation modality. -/
def fibrancyKindToObligationModality : FibrancyKind → ObligationModality
  | .fibrant => .fibrant
  | .exotype => .dimensional

/-- Round-trip, kernel side: reading an obligation modality as a mode and back is the identity. -/
theorem fibrancyKindToObligationModality_toFibrancyKind (modality : ObligationModality) :
    fibrancyKindToObligationModality (obligationModalityToFibrancyKind modality) = modality := by
  cases modality with
  | fibrant => rfl
  | dimensional => rfl

/-- Round-trip, mode-axis side: reading a fibrancy mode as an obligation modality and back is the identity. -/
theorem obligationModalityToFibrancyKind_toObligationModality (mode : FibrancyKind) :
    obligationModalityToFibrancyKind (fibrancyKindToObligationModality mode) = mode := by
  cases mode with
  | fibrant => rfl
  | exotype => rfl

/-! ## The mode a binding sits at -/

/-- **The mode of the binding `index` resolves to**, read structurally off the telescope: a `cons` binding is
an ordinary value at the FIBRANT mode; the `lockCons`-bound dimension is at the EXOTYPE mode.  Both binders are
transparent to bindings behind them — the MTT CX/EXTEND reading `locks(Gamma, x :^mu A) = locks(Gamma)`, which
is why the recursive arms of `cons` and `lockCons` coincide. -/
def TypingContext.bindingFibrancyMode {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Fin scope → FibrancyKind
  | _, .empty, emptyIndex =>
      absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => FibrancyKind.fibrant
  | _, .lockCons _ _, ⟨0, _⟩ => FibrancyKind.exotype
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.bindingFibrancyMode ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.bindingFibrancyMode ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-! ## The two halves of the kernel dispatcher, each a mode match -/

/-- Fibrant accessibility is "the binding sits at the fibrant mode". -/
theorem TypingContext.isFibrantlyAccessibleAt_isModeMatch {profile : PolyProfile} :
    {scope : Nat} → (context : TypingContext profile scope) → (index : Fin scope) →
    context.isFibrantlyAccessibleAt index
      = decide (context.bindingFibrancyMode index = FibrancyKind.fibrant)
  | _, .empty, emptyIndex =>
      absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => rfl
  | _, .lockCons _ _, ⟨0, _⟩ => rfl
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.isFibrantlyAccessibleAt_isModeMatch ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.isFibrantlyAccessibleAt_isModeMatch ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-- Dimensional accessibility is "the binding sits at the exotype mode". -/
theorem TypingContext.isDimensionallyAccessibleAt_isModeMatch {profile : PolyProfile} :
    {scope : Nat} → (context : TypingContext profile scope) → (index : Fin scope) →
    context.isDimensionallyAccessibleAt index
      = decide (context.bindingFibrancyMode index = FibrancyKind.exotype)
  | _, .empty, emptyIndex =>
      absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => rfl
  | _, .lockCons _ _, ⟨0, _⟩ => rfl
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.isDimensionallyAccessibleAt_isModeMatch ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.isDimensionallyAccessibleAt_isModeMatch ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-! ## ★ The identification -/

/-- **★ THE IDENTIFICATION.**  The kernel's bespoke accessibility dispatcher IS the mode-theoretic question:
a binding is usable at an obligation modality exactly when the mode it sits at EQUALS the mode the obligation
demands.  So `ObligationModality` is not an independent notion — it is `FibrancyKind` under another name, and
`isAccessibleAtModality` is TM/VAR's 2-cell check over the thin fibrancy mode theory (where a 2-cell
`locks(Gamma') => mu` exists iff the two are equal).

This is what licenses retiring the bespoke enum onto `Axis/Mode/FibrancyMode` WITHOUT a behaviour change: the
predicate the kernel already computes and the mode fact are the same Bool. -/
theorem TypingContext.isAccessibleAtModality_isModeMatch {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality) :
    context.isAccessibleAtModality index modality
      = decide (context.bindingFibrancyMode index = obligationModalityToFibrancyKind modality) := by
  cases modality with
  | fibrant => exact context.isFibrantlyAccessibleAt_isModeMatch index
  | dimensional => exact context.isDimensionallyAccessibleAt_isModeMatch index

/-- The identification stated from the mode-axis side: a binding is usable at the obligation modality read off
a fibrancy mode exactly when it sits at that mode. -/
theorem TypingContext.isAccessibleAtModality_ofFibrancyKind {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (mode : FibrancyKind) :
    context.isAccessibleAtModality index (fibrancyKindToObligationModality mode)
      = decide (context.bindingFibrancyMode index = mode) := by
  rw [context.isAccessibleAtModality_isModeMatch index (fibrancyKindToObligationModality mode),
    obligationModalityToFibrancyKind_toObligationModality mode]

/-! ## The lock's two poles, in mode vocabulary -/

/-- The locked dimension sits at the EXOTYPE mode — the mode the interval/dimensional formers live at. -/
theorem TypingContext.lockedDimensionIsAtExotypeMode {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).bindingFibrancyMode ⟨0, isLtZeroSucc⟩ = FibrancyKind.exotype :=
  rfl

/-- An ordinary `cons` binding sits at the FIBRANT mode. -/
theorem TypingContext.consBindingIsAtFibrantMode {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.cons bindingType).bindingFibrancyMode ⟨0, isLtZeroSucc⟩ = FibrancyKind.fibrant :=
  rfl

/-- **The two modes are distinct**, so the identification is not degenerate: the lock genuinely separates two
modes, which is precisely what the one-object `dimensionUsePositionModeGraph` (`Mode := Unit`) cannot express.
This is the non-degeneracy the re-founding rides on. -/
theorem lockSeparatesTwoDistinctModes :
    obligationModalityToFibrancyKind .fibrant ≠ obligationModalityToFibrancyKind .dimensional :=
  fun modesEqual => FibrancyKind.noConfusion modesEqual

end FX1Poly.Typed
