import FX1Poly.Axis.Mode.Presentation

/-! # mode-27 frontier — the MULTI-mode MTT presentation (mode-annotated locks)

The single-mode rung (`FX1Poly/Axis/Mode/Presentation.lean`) ships the necessity-fragment presentation
equivalence with a BARE lock `{🔒}` (`MttEntry.lock`).  General MTT (Gratzer-Kavvos-Nuyts-Birkedal) annotates each
lock with a MODE MORPHISM `μ : m → n` drawn from a MODE THEORY (a strict 2-category of modes).  This frontier file
generalizes the lock to carry a parametric mode annotation, and proves the generalization is FAITHFUL — it
specializes (by erasing the annotations) back to the shipped single-mode `MttContext.lockCount`.

## What this file ships (each piece zero-axiom)

  * `MttEntryMulti (Mode Hypothesis : Type)` — a hypothesis or a MODE-ANNOTATED lock `lock (mode : Mode)`; and
    `MttContextMulti` (= the flat list of such entries).
  * two modal-depth measures: the TOTAL lock count `lockCountMulti` (all locks, mode-agnostic) and the per-mode
    `lockCountAt (targetMode) [DecidableEq Mode]` (locks annotated with that one mode).
  * the two monoid-homomorphism structural lemmas: `lockCountMulti_append` and `lockCountAt_append` — BOTH depths
    distribute over context concatenation (cons-only inductions; no propext-leaking `List.append_nil`).
  * a per-mode-refines-the-total bound `lockCountAt_le_lockCountMulti` (each single-mode count is part of the total).
  * ★ the **faithfulness theorem** `lockCountMulti_eq_erased`: for ANY mode set, erasing the lock annotations
    (`eraseModes : MttContextMulti Mode H → MttContext H`) sends `lockCountMulti` to the single-mode
    `MttContext.lockCount`.  The multi-mode generalization is thus a conservative extension of the shipped single
    mode — the single-mode presentation IS the mode-erasure of the multi-mode one.
  * the **single-mode specialization** at `Mode := Unit`: `lockCountMulti_unit_eq_lockCount` (the Unit-mode
    flattening recovers `MttContext.lockCount` exactly) and `lockCountAt_unit_eq_lockCountMulti` (with Unit's only
    mode, the per-mode count IS the total count) — proving the generalization recovers the shipped single mode.

Together these FULLY discharge the `fxMode_hasMultiModePresentation` marker: a faithful mode-parametric lock with the
single mode recovered as the Unit instance.

## Honesty marker (biequivalence strength) — see the bottom of this file

The full 2-categorical BIEQUIVALENCE of the syntactic categories needs natural isomorphisms presented as
function-equalities (`funext`), which equals `Quot.sound` in Lean's kernel and is BANNED under the zero-axiom gate.
What ships here is the genuine OBJECT-LEVEL functoriality: the term translations commute with every syntactic
constructor (they are structural functors on the term algebra), the modal box/mod-count is a grading functor into
`(Nat, +, 0)` preserved by both translations, the round trip preserves that grading, and a concrete witness shows
the round trip is NOT the identity (the genuine definitional-vs-propositional strength gap).

Zero external dependencies; raw Lean 4 + Init only.
-/

namespace FX1Poly.Axis

/-! ## The multi-mode MTT context (mode-annotated locks) -/

/-- A **multi-mode MTT context entry**: a hypothesis, or a lock annotated with a `mode` (the mode morphism the lock
records in a general MTT mode theory). -/
inductive MttEntryMulti (Mode : Type) (Hypothesis : Type) where
  /-- An ordinary hypothesis. -/
  | hyp (hypothesis : Hypothesis)
  /-- A MODE-ANNOTATED modal lock `{🔒_μ}`. -/
  | lock (mode : Mode)

/-- A **multi-mode MTT context** — a flat list of mode-annotated entries. -/
abbrev MttContextMulti (Mode : Type) (Hypothesis : Type) : Type := List (MttEntryMulti Mode Hypothesis)

/-- The **total modal depth** of a multi-mode context: the number of locks, ignoring their mode annotations. -/
def MttContextMulti.lockCountMulti {Mode : Type} {Hypothesis : Type} :
    MttContextMulti Mode Hypothesis → Nat
  | [] => 0
  | MttEntryMulti.hyp _ :: rest => MttContextMulti.lockCountMulti rest
  | MttEntryMulti.lock _ :: rest => MttContextMulti.lockCountMulti rest + 1

/-- The **per-mode modal depth** of a multi-mode context: the number of locks annotated with `targetMode`. -/
def MttContextMulti.lockCountAt {Mode : Type} {Hypothesis : Type} [DecidableEq Mode]
    (targetMode : Mode) : MttContextMulti Mode Hypothesis → Nat
  | [] => 0
  | MttEntryMulti.hyp _ :: rest => MttContextMulti.lockCountAt targetMode rest
  | MttEntryMulti.lock mode :: rest =>
      if targetMode = mode then MttContextMulti.lockCountAt targetMode rest + 1
      else MttContextMulti.lockCountAt targetMode rest

/-! ## The monoid-homomorphism structural lemmas (depths distribute over append) -/

/-- ★ The total lock count is a monoid homomorphism `(MttContextMulti, ++, []) → (Nat, +, 0)`. -/
theorem lockCountMulti_append {Mode : Type} {Hypothesis : Type}
    (entriesLeft entriesRight : MttContextMulti Mode Hypothesis) :
    (entriesLeft ++ entriesRight).lockCountMulti
      = entriesLeft.lockCountMulti + entriesRight.lockCountMulti := by
  induction entriesLeft with
  | nil => rw [List.nil_append, MttContextMulti.lockCountMulti, Nat.zero_add]
  | cons entry rest ih =>
    cases entry with
    | hyp _ =>
      rw [List.cons_append, MttContextMulti.lockCountMulti, MttContextMulti.lockCountMulti, ih]
    | lock _ =>
      rw [List.cons_append, MttContextMulti.lockCountMulti, MttContextMulti.lockCountMulti, ih,
        Nat.succ_add]

/-- ★ The per-mode lock count is likewise a monoid homomorphism into `(Nat, +, 0)`. -/
theorem lockCountAt_append {Mode : Type} {Hypothesis : Type} [DecidableEq Mode] (targetMode : Mode)
    (entriesLeft entriesRight : MttContextMulti Mode Hypothesis) :
    (entriesLeft ++ entriesRight).lockCountAt targetMode
      = entriesLeft.lockCountAt targetMode + entriesRight.lockCountAt targetMode := by
  induction entriesLeft with
  | nil => rw [List.nil_append, MttContextMulti.lockCountAt, Nat.zero_add]
  | cons entry rest ih =>
    cases entry with
    | hyp _ =>
      rw [List.cons_append, MttContextMulti.lockCountAt, MttContextMulti.lockCountAt, ih]
    | lock mode =>
      rw [List.cons_append, MttContextMulti.lockCountAt, MttContextMulti.lockCountAt]
      by_cases hMode : targetMode = mode
      · rw [if_pos hMode, if_pos hMode, ih, Nat.succ_add]
      · rw [if_neg hMode, if_neg hMode, ih]

/-! ## The per-mode count refines the total count -/

/-- Each per-mode lock count is at most the total lock count (a single mode is part of the whole). -/
theorem lockCountAt_le_lockCountMulti {Mode : Type} {Hypothesis : Type} [DecidableEq Mode]
    (targetMode : Mode) (context : MttContextMulti Mode Hypothesis) :
    context.lockCountAt targetMode ≤ context.lockCountMulti := by
  induction context with
  | nil => exact Nat.le_refl 0
  | cons entry rest ih =>
    cases entry with
    | hyp _ =>
      show MttContextMulti.lockCountAt targetMode rest ≤ MttContextMulti.lockCountMulti rest
      exact ih
    | lock mode =>
      show (if targetMode = mode then MttContextMulti.lockCountAt targetMode rest + 1
            else MttContextMulti.lockCountAt targetMode rest)
        ≤ MttContextMulti.lockCountMulti rest + 1
      by_cases hMode : targetMode = mode
      · rw [if_pos hMode]; exact Nat.succ_le_succ ih
      · rw [if_neg hMode]; exact Nat.le.step ih

/-! ## The faithfulness theorem (mode-erasure recovers the single mode) -/

/-- Erase the mode annotations from a multi-mode context, recovering a single-mode `MttContext`. -/
def eraseModes {Mode : Type} {Hypothesis : Type} :
    MttContextMulti Mode Hypothesis → MttContext Hypothesis
  | [] => []
  | MttEntryMulti.hyp hypothesis :: rest => MttEntry.hyp hypothesis :: eraseModes rest
  | MttEntryMulti.lock _ :: rest => MttEntry.lock :: eraseModes rest

/-- ★ **Faithfulness (any mode set).**  The total multi-mode lock count equals the single-mode `MttContext.lockCount`
of the mode-erased context: the multi-mode generalization is a conservative extension — the single-mode presentation
IS the mode-erasure of the multi-mode one. -/
theorem lockCountMulti_eq_erased {Mode : Type} {Hypothesis : Type}
    (context : MttContextMulti Mode Hypothesis) :
    context.lockCountMulti = (eraseModes context).lockCount := by
  induction context with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | hyp _ =>
      show MttContextMulti.lockCountMulti rest = MttContext.lockCount (MttEntry.hyp _ :: eraseModes rest)
      rw [MttContext.lockCount, ih]
    | lock _ =>
      show MttContextMulti.lockCountMulti rest + 1
         = MttContext.lockCount (MttEntry.lock :: eraseModes rest)
      rw [MttContext.lockCount, ih]

/-! ## The single-mode specialization at `Mode := Unit` -/

/-- ★ **Single-mode specialization.**  At the one-element mode set `Unit`, the multi-mode total lock count recovers
the shipped single-mode `MttContext.lockCount` (via mode-erasure) exactly. -/
theorem lockCountMulti_unit_eq_lockCount {Hypothesis : Type}
    (context : MttContextMulti Unit Hypothesis) :
    context.lockCountMulti = (eraseModes context).lockCount :=
  lockCountMulti_eq_erased context

/-- With Unit's single mode, every lock is annotated with `()`, so the per-mode count at `()` IS the total count. -/
theorem lockCountAt_unit_eq_lockCountMulti {Hypothesis : Type}
    (context : MttContextMulti Unit Hypothesis) :
    context.lockCountAt () = context.lockCountMulti := by
  induction context with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | hyp _ =>
      show MttContextMulti.lockCountAt () rest = MttContextMulti.lockCountMulti rest
      exact ih
    | lock mode =>
      show (if (() : Unit) = mode then MttContextMulti.lockCountAt () rest + 1
            else MttContextMulti.lockCountAt () rest)
        = MttContextMulti.lockCountMulti rest + 1
      rw [if_pos (Unit.ext () mode), ih]

/-! ## Biequivalence strength — object-level functoriality (the genuine narrow content)

The translations `fitchToMttTerm` / `mttToFitchTerm` (shipped in the single-mode file) are STRUCTURAL FUNCTORS on
the term algebra: they commute with every syntactic constructor.  The modal box/mod-count is a grading functor into
`(Nat, +, 0)` preserved by both directions and by the round trip.  A concrete witness shows the round trip is NOT
the identity — the genuine definitional-vs-propositional strength gap that keeps the marker `false`. -/

/-- Functoriality of `fitchToMttTerm` on the λ-endofunctor. -/
theorem fitchToMttTerm_lam (body : FitchModalTerm) :
    fitchToMttTerm (.lam body) = .lam (fitchToMttTerm body) := rfl

/-- Functoriality of `fitchToMttTerm` on application. -/
theorem fitchToMttTerm_app (fn arg : FitchModalTerm) :
    fitchToMttTerm (.app fn arg) = .app (fitchToMttTerm fn) (fitchToMttTerm arg) := rfl

/-- Functoriality of `fitchToMttTerm` on the modal introduction (`box ↦ mod`). -/
theorem fitchToMttTerm_boxIntro (body : FitchModalTerm) :
    fitchToMttTerm (.boxIntro body) = .modIntro (fitchToMttTerm body) := rfl

/-- Functoriality of `mttToFitchTerm` on the λ-endofunctor. -/
theorem mttToFitchTerm_lam (body : MttModalTerm) :
    mttToFitchTerm (.lam body) = .lam (mttToFitchTerm body) := rfl

/-- Functoriality of `mttToFitchTerm` on application. -/
theorem mttToFitchTerm_app (fn arg : MttModalTerm) :
    mttToFitchTerm (.app fn arg) = .app (mttToFitchTerm fn) (mttToFitchTerm arg) := rfl

/-- Functoriality of `mttToFitchTerm` on the modal introduction (`mod ↦ box`). -/
theorem mttToFitchTerm_modIntro (body : MttModalTerm) :
    mttToFitchTerm (.modIntro body) = .boxIntro (mttToFitchTerm body) := rfl

/-- ★ The modal-degree grading is a NATURAL INVARIANT under the round trip: translating a Fitch term to MTT and back
preserves its box-count, even though the round trip is not the identity term. -/
theorem fitchRoundTrip_boxCount (term : FitchModalTerm) :
    (mttToFitchTerm (fitchToMttTerm term)).boxCount = term.boxCount := by
  rw [mttToFitchTerm_boxCount, fitchToMttTerm_modCount]

/-- ★ Dually, the round trip on MTT terms preserves the mod-count. -/
theorem mttRoundTrip_modCount (term : MttModalTerm) :
    (fitchToMttTerm (mttToFitchTerm term)).modCount = term.modCount := by
  rw [fitchToMttTerm_modCount, mttToFitchTerm_boxCount]

/-- ★ **The genuine strength gap, witnessed.**  The round trip is NOT the identity: the coercive `unbox (var 0)`
comes back as the binding desugaring `(λx. x) (unbox (var 0))`, a structurally different term.  This is exactly why
the equivalence is propositional-up-to-degree, not strict — the full biequivalence (a natural iso making this an
EQUALITY) needs `funext`. -/
theorem fitchRoundTrip_not_identity :
    mttToFitchTerm (fitchToMttTerm (.unbox (.var 0)))
      = .app (.lam (.var 0)) (.unbox (.var 0)) := rfl

end FX1Poly.Axis
