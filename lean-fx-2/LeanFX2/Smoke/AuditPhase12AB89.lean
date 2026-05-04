import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.SubstHet
import LeanFX2.Term.Pointwise
import LeanFX2.Algo.Eval
import LeanFX2.Algo.WHNF
import LeanFX2.Algo.Soundness
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.Step
import LeanFX2.Bridge
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext

/-! # Smoke/AuditPhase12AB89 — heterogeneous Funext FINAL HEADLINE.

Phase 12.A.B8.B (CUMUL-8.B).  Ships the **headline heterogeneous
Funext theorem** — the full heterogeneous-payload form for arbitrary
distinct apply payloads `applyARaw, applyBRaw` (not just rfl).
Consumes the `Step.eqArrowHet` reduction rule landed in this same
phase and lifts it through `Conv.fromStep` to a typed `Conv` between
`Term.funextIntroHet ... applyARaw applyBRaw` and the canonical
pointwise-refl funext witness instantiated at `applyARaw`.

## What this audit establishes

This audit is the **final HoTT zero-axiom headline** in the kernel.
After this ships, the kernel has the FULL HoTT zero-axiom foundation:

* `Univalence` (rfl-fragment via `Step.eqType`) — Phase 12.A.B8.6
* `UnivalenceHet` (heterogeneous via `Step.eqTypeHet`) — Phase 12.A.B8.7
* `funext` (rfl-fragment via `Step.eqArrow`) — Phase 12.A.B8.7
* `FunextHet` (heterogeneous via `Step.eqArrowHet`) — Phase 12.A.B8.B

ALL FOUR reported by `#print axioms` as
"does not depend on any axioms".  No `propext`, no `Quot.sound`, no
`Classical.choice`, no user-declared axiom.

## Cascade summary (this phase)

5 files extended, 1 new audit file (this).  All zero-axiom under
strict policy.  Audit gates:

* **Reduction (Layer 2):**
  - `Step.eqArrowHet` — the headline reduction rule
  - `Step.par.eqArrowHet` — parallel-reduction analog
  - `Step.toPar` — extended with the eqArrowHet arm

* **Bridge (Layer 4):**
  - `Step.par.toRawBridge` — extended with the eqArrowHet arm
    (collapses to `RawStep.par.refl _` via raw alignment)

* **Cumul (Layer 2):**
  - `ConvCumul.iotaEqArrowHetCumul` — ConvCumul lift for eqArrowHet,
    mirror of `iotaEqArrowCumul` / `iotaEqTypeHetCumul`
  - `Step.toConvCumul` — extended with the eqArrowHet arm

* **HoTT (Layer 6 — headline):**
  - `FunextHet` — the headline heterogeneous Funext theorem with
    body `Conv.fromStep (Step.eqArrowHet ...)`

## Architectural raw-alignment trick (recap)

Both source `Term.funextIntroHet ... applyARaw applyBRaw` and target
`Term.funextRefl ... applyARaw` project to the SAME raw form
`RawTerm.lam (RawTerm.refl applyARaw)` (the `funextIntroHet` ctor's
raw uses `applyARaw` and coincides with `funextRefl`'s raw at the
same payload — see `Term.funextIntroHet` docstring).  The rule
changes the type only — `Ty.id (Ty.arrow ...) (lam applyARaw)
(lam applyBRaw)` reduces to `Ty.piTy domainType (Ty.id
codomainType.weaken applyARaw applyARaw)` while the raw data is
preserved.  Same architectural payoff as `cumulUpInner` / `eqType` /
`eqArrow` / `eqTypeHet`.

## Relationship to the rfl-fragment `funext`

`LeanFX2.funext` (Phase 12.A.B8.7) handles the rfl-fragment only —
both endpoints share the SAME apply payload
(`Term.funextReflAtId → Term.funextRefl` via `Step.eqArrow`).

`LeanFX2.FunextHet` handles the heterogeneous case — ANY two
distinct apply payloads
(`Term.funextIntroHet ... applyARaw applyBRaw → Term.funextRefl ...
applyARaw` via `Step.eqArrowHet`).

Together the two cover the FULL heterogeneous Funext at the kernel
level — `Step.eqArrow` for refl, `Step.eqArrowHet` for arbitrary,
and the union is full Funext definitional.  Both ship as zero-axiom
theorems under strict policy. -/

namespace LeanFX2

/-! ## §1. The Step constructor itself. -/

#print axioms Step.eqArrowHet

/-! ## §2. Parallel-reduction lift. -/

#print axioms Step.par.eqArrowHet

/-! ## §3. Step → Par lift (extended with the new arm). -/

#print axioms Step.toPar

/-! ## §4. Bridge cascade — typed→raw projection (extended). -/

#print axioms Step.par.toRawBridge

/-! ## §5. ConvCumul cascade — ConvCumul ctor + Step→ConvCumul lift. -/

#print axioms ConvCumul.iotaEqArrowHetCumul
#print axioms Step.toConvCumul

/-! ## §6. THE FINAL HEADLINE — full HoTT zero-axiom foundation. -/

#print axioms FunextHet

/-! ## §7. Regression — the other three HoTT headlines stay zero-axiom. -/

#print axioms Univalence
#print axioms UnivalenceHet
#print axioms funext

/-! ## §8. Pattern 3 + W8 regression — full kernel infrastructure clean. -/

#print axioms ConvCumul.subst_compatible
#print axioms ConvCumul.subst_compatible_paired_allais
#print axioms ConvCumulHomo.subst_compatible_paired_allais

/-! ## §9. Term ctors + subst infrastructure regression. -/

#print axioms Term.funextIntroHet
#print axioms Term.funextRefl
#print axioms Term.rename
#print axioms Term.subst
#print axioms Term.substHet
#print axioms Term.subst_pointwise

/-! ## §10. WHNF + headStep? regression — algorithmic layer clean. -/

#print axioms Term.headStep?
#print axioms Term.headStep?_sound

end LeanFX2
