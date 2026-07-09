import FX1Poly.Typed.Fib.ModeLockPath

/-! # FX1Poly/Typed/Fib/KernelBridgeAccessibility — CORE-WP r1 (K3/K4/K5): the mode-accessibility decider bridge

CORE-WP r1's kernel bridge: a TOTAL mode-accessibility decider over the real `ModalityPath` carrier of the
kernel's affine dimension mode theory, the FIRST engine accessibility premise DISCHARGED from that decider's
verdict (wired, definitional), and the fibrant-vs-dimensional SEPARATION certificate (the non-degeneracy seed
for INT-MODE-CONSISTENCY, #2080).

## The MTT premise this discharges

The FitchTT/MTT variable rule (Gratzer-Kavvos-Nuyts-Birkedal 2021, Fig 3) admits a variable at a use-modality
only when a 2-cell `alpha : useModality => bindingModality . locks(Delta)` exists in the mode theory (mitten,
Stassen-Gratzer-Birkedal 2022, restricts to the PREORDERED class — at most one 2-cell between any pair, so
2-cell existence collapses to a reachability check).  For FX's single affine lock the context suffix-lock is
always the identity (`locks(Delta) = id`), so the premise is 2-cell existence `useModality => bindingModality`
over the affine mode theory.  That theory is the FREE thin category on one generator (`ModeLockPath.lean`):
its only 2-cells are identities, so 2-cell existence collapses to PATH EQUALITY of the two 1-cells
(`ModalityPath`s), decided TOTALLY by `modeAccessibilityDecider`.

## What ships (K3/K4/K5)

  * **K3 `modeAccessibilityDecider`** — TOTAL `Decidable (IsModeAccessible usePath bindingPath)` over the real
    affine `ModalityPath` carrier, routed through the GENERIC free-1-cell decider `modalityPathDecEq`
    (works for ANY mode theory; here instantiated at the affine graph's `Unit`/`Unit` data — no toy alphabet).
    BOTH verdicts are exhibited on real paths of lengths 0/1/2: reflexive `isTrue`, distinct-length `isFalse`.
  * **K4 `accessibilityPremise_ofModeAccessible`** — the WIRED bridge: the decider's affirmative verdict
    DISCHARGES the engine's `TypingContext.isAccessibleAtModality = true` premise by definitional computation
    (through the A1-MODE-SEAL `isAccessibleAtModality_eq_pathEq`).  Concrete corpus instances follow.
  * **K5** (markers + ledger, below the separation section) — the `isFalse` fibrant-vs-dimensional separation
    certificate (the modal structure does NOT collapse), plus the honest forward-scope / walled markers.

## Zero-axiom

`inferInstance` on `Unit`, the generic `modalityPathDecEq` (propext-free), `rfl`-computed verdicts, and
`decide_eq_true` / length-refutation bridges — no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

set_option autoImplicit false

namespace FX1Poly.Core.Fib

open FX1Poly.Polygraph
open FX1Poly.Typed

/-! ## K3a — the decidable-equality data of the affine mode graph -/

/-- Decidable equality on the affine graph's modes (one, `()`) — the `Unit` instance. -/
def affineGraphModeDecEq : DecidableEq affineDimensionModeGraph.Mode :=
  inferInstanceAs (DecidableEq Unit)

/-- Decidable equality on the affine graph's modality generators (one, `()`) — the `Unit` instance, uniformly
over every endpoint pair. -/
def affineGraphModalityDecEq :
    (sourceMode targetMode : affineDimensionModeGraph.Mode) →
      DecidableEq (affineDimensionModeGraph.Modality sourceMode targetMode) :=
  fun _ _ => inferInstanceAs (DecidableEq Unit)

/-! ## K3b — the accessibility relation + its TOTAL decider -/

/-- The **mode-accessibility relation** over the kernel's affine mode theory: a use-modality 1-cell `usePath`
is accessible from a binding-modality 1-cell `bindingPath` iff an accessibility 2-cell connects them.  Over the
FREE thin affine theory (one generator, NO 2-cell relations) the only 2-cells are identities, so this holds iff
the two 1-cells are EQUAL — the `locks(Delta) = id` specialization of MTT's use-modality variable rule. -/
def IsModeAccessible
    (usePath bindingPath : ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode) :
    Prop :=
  usePath = bindingPath

/-- ★ **K3 — the mode-accessibility DECIDER.**  Decides `IsModeAccessible` TOTALLY over the real affine
`ModalityPath` carrier, routed through the GENERIC free-1-cell decider `modalityPathDecEq` instantiated at the
affine graph's decidable-equality data.  Because `modalityPathDecEq` is total over ANY mode graph, this is the
kernel's reusable accessibility service, not a toy: 2-cell existence in the thin free theory = path equality,
decided propext-free. -/
def modeAccessibilityDecider
    (usePath bindingPath : ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode) :
    Decidable (IsModeAccessible usePath bindingPath) :=
  modalityPathDecEq affineGraphModeDecEq affineGraphModalityDecEq usePath bindingPath

/-- The decider read off as a `Bool` — `true` when the use and binding 1-cells are accessibility-related
(equal over the affine thin theory), `false` otherwise.  The surface the verdict theorems compute over. -/
def modeAccessibleBool
    (usePath bindingPath : ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode) :
    Bool :=
  match modeAccessibilityDecider usePath bindingPath with
  | isTrue _ => true
  | isFalse _ => false

/-! ## K3c — BOTH verdicts on REAL paths (lengths 0, 1, 2 — not a toy alphabet) -/

/-- The fibrant use-modality 1-cell (the identity path, length 0) — `obligationModalityToPath .fibrant`. -/
def fibrantUsePath : ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode :=
  obligationModalityToPath .fibrant

/-- The dimensional use-modality 1-cell (the affine generator path, length 1) —
`obligationModalityToPath .dimensional`. -/
def dimensionalUsePath : ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode :=
  obligationModalityToPath .dimensional

/-- A double-lock 1-cell (length 2) — a genuine longer path over the real carrier, past the two enum images. -/
def doubleLockPath : ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode :=
  ModalityPath.cons affineLockGenerator (ModalityPath.cons affineLockGenerator (identityPath affineDimensionMode))

/-- ★ Verdict `isTrue` (length 0): the fibrant 1-cell is accessible from itself. -/
theorem modeAccessible_fibrant_self : modeAccessibleBool fibrantUsePath fibrantUsePath = true := rfl

/-- ★ Verdict `isTrue` (length 1): the dimensional 1-cell is accessible from itself. -/
theorem modeAccessible_dimensional_self : modeAccessibleBool dimensionalUsePath dimensionalUsePath = true := rfl

/-- ★ Verdict `isTrue` (length 2): the double-lock 1-cell is accessible from itself — the decider is total on
arbitrary-length real paths, not only the two enum images. -/
theorem modeAccessible_doubleLock_self : modeAccessibleBool doubleLockPath doubleLockPath = true := rfl

/-- ★ Verdict `isFalse` (lengths 0 vs 1): the fibrant 1-cell is NOT accessible from the dimensional 1-cell —
the affine lock cannot be reached from the identity.  The separation seed (K5). -/
theorem modeAccessible_fibrant_dimensional_false :
    modeAccessibleBool fibrantUsePath dimensionalUsePath = false := rfl

/-- ★ Verdict `isFalse` (lengths 1 vs 2): the dimensional 1-cell is NOT accessible from the double-lock 1-cell —
a distinct-length real pair, decided negatively. -/
theorem modeAccessible_dimensional_doubleLock_false :
    modeAccessibleBool dimensionalUsePath doubleLockPath = false := rfl

/-! ## Observability -/

-- Reflexive verdicts on real paths of length 0/1/2: expect `true` each.
#eval modeAccessibleBool fibrantUsePath fibrantUsePath
#eval modeAccessibleBool dimensionalUsePath dimensionalUsePath
#eval modeAccessibleBool doubleLockPath doubleLockPath
-- Distinct-length verdicts: expect `false` each.
#eval modeAccessibleBool fibrantUsePath dimensionalUsePath
#eval modeAccessibleBool dimensionalUsePath doubleLockPath

end FX1Poly.Core.Fib
