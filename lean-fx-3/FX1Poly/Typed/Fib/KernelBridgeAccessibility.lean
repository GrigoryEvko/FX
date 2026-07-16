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
open FX1Poly.Core

/-! ## K3a — the decidable-equality data of the affine mode graph -/

/-- Decidable equality on the affine graph's modes (one, `()`) — the `Unit` instance. -/
def affineGraphModeDecEq : DecidableEq dimensionUsePositionModeGraph.Mode :=
  inferInstanceAs (DecidableEq Unit)

/-- Decidable equality on the affine graph's modality generators (one, `()`) — the `Unit` instance, uniformly
over every endpoint pair. -/
def affineGraphModalityDecEq :
    (sourceMode targetMode : dimensionUsePositionModeGraph.Mode) →
      DecidableEq (dimensionUsePositionModeGraph.Modality sourceMode targetMode) :=
  fun _ _ => inferInstanceAs (DecidableEq Unit)

/-! ## K3b — the accessibility relation + its TOTAL decider -/

/-- The **mode-accessibility relation** over the kernel's affine mode theory: a use-modality 1-cell `usePath`
is accessible from a binding-modality 1-cell `bindingPath` iff an accessibility 2-cell connects them.  Over the
FREE thin affine theory (one generator, NO 2-cell relations) the only 2-cells are identities, so this holds iff
the two 1-cells are EQUAL — the `locks(Delta) = id` specialization of MTT's use-modality variable rule. -/
def IsModeAccessible
    (usePath bindingPath : ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode) :
    Prop :=
  usePath = bindingPath

/-- ★ **K3 — the mode-accessibility DECIDER.**  Decides `IsModeAccessible` TOTALLY over the real affine
`ModalityPath` carrier, routed through the GENERIC free-1-cell decider `modalityPathDecEq` instantiated at the
affine graph's decidable-equality data.  Because `modalityPathDecEq` is total over ANY mode graph, this is the
kernel's reusable accessibility service, not a toy: 2-cell existence in the thin free theory = path equality,
decided propext-free. -/
def modeAccessibilityDecider
    (usePath bindingPath : ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode) :
    Decidable (IsModeAccessible usePath bindingPath) :=
  modalityPathDecEq affineGraphModeDecEq affineGraphModalityDecEq usePath bindingPath

/-- The decider read off as a `Bool` — `true` when the use and binding 1-cells are accessibility-related
(equal over the affine thin theory), `false` otherwise.  The surface the verdict theorems compute over. -/
def modeAccessibleBool
    (usePath bindingPath : ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode) :
    Bool :=
  match modeAccessibilityDecider usePath bindingPath with
  | isTrue _ => true
  | isFalse _ => false

/-! ## K3c — BOTH verdicts on REAL paths (lengths 0, 1, 2 — not a toy alphabet) -/

/-- The fibrant use-modality 1-cell (the identity path, length 0) — `obligationModalityToPath .fibrant`. -/
def fibrantUsePath : ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode :=
  obligationModalityToPath .fibrant

/-- The dimensional use-modality 1-cell (the affine generator path, length 1) —
`obligationModalityToPath .dimensional`. -/
def dimensionalUsePath : ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode :=
  obligationModalityToPath .dimensional

/-- A double-lock 1-cell (length 2) — a genuine longer path over the real carrier, past the two enum images. -/
def doubleLockPath : ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode :=
  ModalityPath.cons affineLockGenerator (ModalityPath.cons affineLockGenerator (identityPath dimensionUsePositionMode))

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

/-! ## K4 — the FIRST discharged premise: the decider verdict WIRES the engine's accessibility check

The engine's LIVE accessibility premise `TypingContext.isAccessibleAtModality index modality = true` is consumed
in the substitution leg (`HasTypeUnionSubstUnionTyped`) and in the table-arm usability conjunct
(`isSubjectUsableAtModality`).  K4 discharges that premise FROM the K3 decider's verdict.  This is the honest
WIRED K4 shape (NOT a decorative wrapper): the premise IS a decidable `Bool = true`, and the A1-MODE-SEAL
`isAccessibleAtModality_eq_pathEq` makes the engine check DEFINITIONALLY the mode theory's path-equality decision,
so the bridge is `decide_eq_true` over that sealed equation. -/

/-- ★★ **K4 — THE DISCHARGED PREMISE (WIRED).**  The mode-accessibility decider's affirmative verdict — exactly
the `IsModeAccessible` witness `modeAccessibilityDecider` returns in its `isTrue` branch — DISCHARGES the engine's
accessibility premise `context.isAccessibleAtModality index modality = true`, by definitional computation through
the A1-MODE-SEAL.  The kernel bridge: a mode-theory decision becomes a typing-side premise, no re-proof. -/
theorem accessibilityPremise_ofModeAccessible {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality)
    (accessible :
        IsModeAccessible (obligationModalityToPath modality) (bindingModalityPath context index)) :
    context.isAccessibleAtModality index modality = true := by
  rw [isAccessibleAtModality_eq_pathEq]
  exact decide_eq_true accessible

/-- ★ **K4 — the NEGATIVE bridge (the separation direction).**  When the decider REFUTES accessibility, the
engine's premise is `false`: the use-modality cannot be admitted where the binding-modality forbids it.  This is
the leg that KILLS a mis-modalled variable use (the SR-breaker) FROM the mode decision. -/
theorem accessibilityRefuted_ofNotModeAccessible {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality)
    (notAccessible :
        ¬ IsModeAccessible (obligationModalityToPath modality) (bindingModalityPath context index)) :
    context.isAccessibleAtModality index modality = false := by
  rw [isAccessibleAtModality_eq_pathEq]
  exact decide_eq_false notAccessible

/-- ★ **K4 corpus instance (ACCEPT).**  The locked dimension `var 0` under `Gamma.lockCons` is accessible at the
DIMENSIONAL modality THROUGH the decider bridge: its binding-modality path is the affine generator, which is
`obligationModalityToPath .dimensional`, so `accessibilityPremise_ofModeAccessible` fires by `rfl`.  Reproduces
the engine's `dimensionIsAccessibleDimensionally` (so `pathApp p (var 0)` types) — now DISCHARGED FROM the
mode-accessibility decision, not by a bespoke computation. -/
theorem lockedDimensionAccessibleDimensionallyViaBridge {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .dimensional = true :=
  accessibilityPremise_ofModeAccessible (restContext.lockCons dimensionType) ⟨0, isLtZeroSucc⟩ .dimensional rfl

/-- ★ **K4 corpus instance (REJECT / separation).**  The locked dimension `var 0` under `Gamma.lockCons` is NOT
accessible at the FIBRANT modality THROUGH the decider bridge: `obligationModalityToPath .fibrant` is the identity
path (length 0), the binding path is the affine generator (length 1), so the decider REFUTES (lengths `0 != 1`)
and `accessibilityRefuted_ofNotModeAccessible` fires.  Reproduces `dimensionIsNotAccessibleFibrantly` — the
canonical SR-breaker `pair (var 0) (var 0)` is killed FROM the mode-accessibility decision. -/
theorem lockedDimensionRefutedFibrantlyViaBridge {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .fibrant = false :=
  accessibilityRefuted_ofNotModeAccessible (restContext.lockCons dimensionType) ⟨0, isLtZeroSucc⟩ .fibrant
    (fun pathEq => Nat.noConfusion (congrArg ModalityPath.length pathEq))

/-! ## K5 — the SEPARATION / non-degeneracy certificate (the INT-MODE-CONSISTENCY seed, #2080)

The decider's `isFalse` verdict is a NON-DEGENERACY certificate: two genuinely-distinct kernel modalities are
NOT accessibility-related, so the affine lock cannot collapse into the identity (the modal structure survives).
This is the seed for INT-MODE-CONSISTENCY (#2080) — the mode theory's model certifies the kernel's modal
structure does not degenerate. -/

/-- ★★ **K5 — the non-degeneracy SEED (SEPARATION).**  The FIBRANT modality (identity path) is NOT accessible
from the DIMENSIONAL modality (affine generator path): there is no accessibility 2-cell fibrant <= dimensional,
refuted at the `Nat` level by their distinct 1-cell lengths (`0 != 1`).  Concretely: the locked affine dimension
CANNOT be smuggled into a fibrant position — the affine lock does not collapse into the unlocked identity.  The
`isFalse` face of `modeAccessibilityDecider`, promoted to a Prop-level non-degeneracy certificate. -/
theorem fibrantNotAccessibleFromDimensional : ¬ IsModeAccessible fibrantUsePath dimensionalUsePath :=
  fun accessible => Nat.noConfusion (congrArg ModalityPath.length accessible)

/-- ★ **K5 — the two kernel modalities are DISTINCT 1-cells** (the non-degeneracy in its plainest form): the
fibrant and dimensional use-modalities are unequal `ModalityPath`s.  Together with `fibrantNotAccessibleFromDimensional`
this certifies the affine mode theory is not the trivial (one-1-cell) theory — the lock generator adds a genuine,
inaccessible degree of freedom. -/
theorem fibrantUsePath_ne_dimensionalUsePath : fibrantUsePath ≠ dimensionalUsePath :=
  fun pathsEqual => Nat.noConfusion (congrArg ModalityPath.length pathsEqual)

/-! ## K5 — the CORE-WP r1 honesty ledger

WIRED (shipped, machine-checked, zero-axiom):
  * K2 — the affine dimension lock as a RELATION-FREE `ModeSignature`, its own dimension-2 word problem decided
    by the free decider (`kernelAffineFreeDimTwoDecision_holds`); the `admitByRowAware` cross-arc a stated
    NON-MATCH (relation-free => free decision direct).
  * K3 — the mode-accessibility decider, TOTAL over the real `ModalityPath` carrier, both verdicts on real paths.
  * K4 — the FIRST engine accessibility premise discharged FROM the decider verdict (the WIRED shape: the premise
    is a decidable `Bool = true`, the bridge is `decide_eq_true` over the A1-MODE-SEAL — NOT a decorative wrapper).
  * K5 — the fibrant-vs-dimensional non-degeneracy SEED (the affine lock does not collapse into the identity).

FORWARD SCOPE (honest `false`, named for the next rungs):
  * the parameterized mode-decision SERVICE over first-class mode-theory VALUES (#2055 CORE-WP-MODESVC / #2061
    CORE-WP-MODEVALUE): r1 ships the concrete affine instance, not the generic architecture.
  * the END-TO-END checker demonstrator (#2084 INT-CHECKER-E2E): a full kernel typing derivation with EVERY mode
    premise discharged by computation — r1 discharges the FIRST premise, not a whole derivation.

WALLED (honest `false`, permanent):
  * the GENERAL multi-mode dimension-2 mode-2-cell decision (mode theories WITH relations, cross-signature):
    permanently `false` (`fxMode_hasDecidableTwoCellEquality`, Post-Markov undecidability).  The kernel's OWN
    affine theory escapes the wall because it is relation-free (the FREE decision applies); the wall is for the
    saturated walking-adjunction arc, not this bridge. -/

/-- ★★ **Honesty marker — the mode-accessibility DECIDER ships (CORE-WP r1 K3).**  `modeAccessibilityDecider`
is a total `Decidable (IsModeAccessible ...)` over the real affine `ModalityPath` carrier (through the generic
`modalityPathDecEq`), with both verdicts exhibited on real length-0/1/2 paths.  `= true`. -/
def fxKernelBridge_hasModeAccessibilityDecision : Bool := true

/-- ★★ **Honesty marker — the FIRST engine accessibility premise is DISCHARGED (CORE-WP r1 K4, WIRED).**  From
the decider's verdict, `context.isAccessibleAtModality index modality = true/false` follows by definitional
computation (through the A1-MODE-SEAL), with concrete accept/reject corpus instances
(`lockedDimensionAccessibleDimensionallyViaBridge` / `lockedDimensionRefutedFibrantlyViaBridge`).  This is the
honest WIRED K4 shape — the premise is a decidable `Bool = true`, not a decorative K4 wrapper.  `= true`. -/
def fxKernelBridge_hasDischargedAccessibilityPremise : Bool := true

/-- ★★ **Honesty marker — the non-degeneracy SEPARATION certificate ships (CORE-WP r1 K5).**  The decider's
`isFalse` face proves the fibrant modality is NOT accessible from the dimensional modality
(`fibrantNotAccessibleFromDimensional`), so the affine lock does not collapse into the identity — the
INT-MODE-CONSISTENCY (#2080) non-degeneracy seed.  `= true`. -/
def fxKernelBridge_hasModeSeparationCertificate : Bool := true

/-- ★ **Honesty marker (`false`) — the PARAMETERIZED mode-decision SERVICE is FORWARD SCOPE.**  CORE-WP r1 ships
the CONCRETE affine-lock accessibility decider and its discharged premise, NOT the generic architecture that
parameterizes decisions over first-class mode-theory VALUES (#2055 CORE-WP-MODESVC / #2061 CORE-WP-MODEVALUE).
That generalization — the reusable `Core/Fib` service over an arbitrary `ModeSignature` — is the next rung.
`= false`. -/
def fxKernelBridge_hasParameterizedModeDecisionService : Bool := false

/-- ★ **Honesty marker (`false`) — the END-TO-END checker demonstrator is FORWARD SCOPE.**  r1 discharges the
FIRST engine accessibility premise from the mode decision; the full demonstrator (#2084 INT-CHECKER-E2E) — a
complete kernel typing derivation with EVERY mode premise discharged by computation — is not yet assembled.
`= false`. -/
def fxKernelBridge_hasEndToEndCheckerDemo : Bool := false

/-- ★ **Honesty marker (`false`, PERMANENT) — the GENERAL multi-mode dimension-2 decision stays WALLED.**  The
kernel bridge decides the affine lock's DIMENSION-1 accessibility (path equality) and its relation-free
DIMENSION-2 word problem (the free decider); it does NOT decide the GENERAL dimension-2 mode-2-cell equality for
mode theories WITH relations across signatures — that is `fxMode_hasDecidableTwoCellEquality`, permanently
`false` by Post-Markov undecidability.  Stated honestly: the wall is for the saturated arc, not this bridge; the
affine theory escapes it by being relation-free.  `= false`. -/
def fxKernelBridge_hasGeneralMultiModeTwoCellDecision : Bool := false

end FX1Poly.Core.Fib
