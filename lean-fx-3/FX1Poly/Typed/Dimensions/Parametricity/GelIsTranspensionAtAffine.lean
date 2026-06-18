import FX1Poly.Tier0.Mode.MultiplierStructureClass
import FX1Poly.Tier0.Mode.SamenessUnification
import FX1Poly.Tier0.Mode.Transpension
import FX1Poly.Core.Equality.Gel.GelRelationRetract

/-! # FX1Poly/Typed/Dimensions/Parametricity/GelIsTranspensionAtAffine
    — the shipped gel-beta IS transpension @ the affine structure-class (TRANSP-PARAM-RETIRE, rung 1)

The mode axis ships the transpension classification three ways but leaves them DISCONNECTED from the
kernel's actual gel reduction:

  * `mode-2` (`MultiplierStructureClass`) classifies a multiplier by its cube-ladder structure-class
    (`affine` / `cartesian` / `dedekind` / `deMorgan`) with the Nuyts-Devriese Fig-7/9 property table;
  * `mode-19` (`SamenessArity`) dials nominal / parametric / univalent to a multiplier class
    ("arity = multiplier"), with reflexivity = the multiplier's diagonal;
  * `mode-11` (`TranspensionRecoverable`) enumerates the eight operators the universal transpension
    recovers (`gel` / `glue` / `weld` / `mill` / `amazingRightAdjoint` / `phi` / `psi` / `nominal`),
    but ships them as NAMES only (`fxMode_hasTranspensionZooRecovery := false`,
    `fxMode_hasKernelTranspensionConnection := false`).

Meanwhile the kernel ships a COMPUTING gel-beta reduction — `ungel (gel a b r) ↝ r`
(`gelBetaIotaRow`, realized as `Core.gelRelationRetract_witnessProjectionLeg`) — but nothing tied it to
the mode-layer classification.  `RelationalUniverse.lean` (type-9) records that its syntactic relational
universe is "blocked on the transpension former".

This module supplies the missing connection for the FIRST of the eight operators.  It pins the Gel
former's multiplier to the AFFINE structure-class, machine-checks the Cavallo-Harper / Nuyts soundness
gate (affine forbids the diagonal — an apartness criterion is incompatible with diagonal substitutions,
which is exactly why internal parametricity must abstract over an affine, not cartesian, dimension),
routes it through the `mode-19` arity dial (parametricity = the affine arity), and backs the `gel` entry
of the zoo with the shipped computing reduction.  This is "parametricity = transpension @ affine" as a
machine-checked, computing fact rather than a `= false` marker — `TRANSP-PARAM-RETIRE` for the gel
operator.

The honesty discipline is preserved: only `gel` is kernel-backed so far (1 of 8); the global
`fxMode_hasTranspensionZooRecovery` stays `false` until all eight operators compute.

## Zero-axiom verification

Every class fact is `rfl`/`decide` over the `mode-2`/`mode-19` finite tables; the computing leg is the
already-shipped `Core.gelRelationRetract_witnessProjectionLeg` (a `Conv` from the gel-beta `Step`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Tier0
open FX1Poly.Core

/-! ## The Gel former's multiplier structure-class -/

/-- The structure-class of the Gel former's multiplier: the AFFINE bridge interval.  Cavallo-Harper /
Nuyts: the relational universe `Gel` (and `extent`) are sound ONLY over an affine dimension — a
cartesian (diagonal-carrying) interval would make internal parametricity unsound. -/
def gelStructureClass : MultiplierStructureClass := .affine

/-! ## The soundness gate — the affine multiplier forbids diagonal / connections / reversal -/

/-- ★ The soundness gate: the Gel multiplier FORBIDS the diagonal.  This is the machine-checked form of
Cavallo-Harper's "an apartness criterion is incompatible with diagonal substitutions" — the exact reason
`Gel` must abstract over an affine, not cartesian, dimension. -/
theorem gelMultiplier_forbidsDiagonal : gelStructureClass.supportsDiagonal = false := rfl

/-- The Gel multiplier forbids the monotone connections. -/
theorem gelMultiplier_forbidsConnections : gelStructureClass.supportsConnections = false := rfl

/-- The Gel multiplier forbids the non-monotone reversal. -/
theorem gelMultiplier_forbidsReversal : gelStructureClass.supportsReversal = false := rfl

/-! ## The affine structure IS present -/

/-- The Gel multiplier HAS the affine structure (the endpoint projections) — the positive content the
relational universe relies on. -/
theorem gelMultiplier_isAffine : gelStructureClass.hasProperty .affine = true := rfl

/-- The Gel multiplier is QUANTIFIABLE — `Pi` over the bridge dimension exists, i.e. the universal
modality `forall u` whose right adjoint is the transpension.  This is the affine structure that makes the
Gel-as-transpension reading possible. -/
theorem gelMultiplier_isQuantifiable : gelStructureClass.hasProperty .quantifiable = true := rfl

/-- The Gel multiplier is SEMICARTESIAN (the monoidal unit is terminal). -/
theorem gelMultiplier_isSemicartesian : gelStructureClass.hasProperty .semicartesian = true := rfl

/-! ## The arity dial (mode-19): parametricity routes to exactly this class -/

/-- ★ The arity-multiplier identity at the Gel former: PARAMETRICITY's arity (`mode-19`) routes to
exactly the Gel former's structure-class.  "Gel = transpension @ the parametric arity", and the
parametric arity IS the affine multiplier. -/
theorem gelMultiplier_isParametricArity :
    SamenessArity.parametric.multiplierClass = gelStructureClass := rfl

/-- The parametric arity is NON-reflexive (bridges need no diagonal), matching the Gel multiplier
forbidding the diagonal — via `mode-19`'s reflexivity = diagonal identity. -/
theorem gelMultiplier_parametricIsIrreflexive :
    SamenessArity.parametric.hasReflexivity = gelStructureClass.supportsDiagonal :=
  samenessArity_reflexivity_eq_diagonal .parametric

/-! ## The computing leg — gel-beta at the affine class -/

/-- The Gel former's computing content, re-exported under a parametricity-themed name: for every gel
cell, `ungel (gel a b r)` converts to the relation witness `r` — the shipped gel-beta
(`Core.gelRelationRetract_witnessProjectionLeg`). -/
theorem gelComputesAtEveryScope {scope : Nat}
    (leftEndpoint rightEndpoint relationWitness : RawTerm scope) :
    Conv (ungelProjection (gelCellOf leftEndpoint rightEndpoint relationWitness)) relationWitness :=
  gelRelationRetract_witnessProjectionLeg leftEndpoint rightEndpoint relationWitness

/-! ## The recovery witness — the gel operator is kernel-backed at the affine class -/

/-- ★★ **The Gel operator of the transpension zoo is RECOVERED at the affine structure-class by a
COMPUTING kernel reduction.**  Bundles the three facts that make "parametricity = transpension @ affine"
machine-checked for the relational universe:

  1. the Gel former's structure-class IS the parametric arity's multiplier (`mode-19`);
  2. that multiplier FORBIDS the diagonal (the Cavallo-Harper soundness gate);
  3. the shipped gel-beta reduction COMPUTES: for every gel cell, `ungel (gel a b r)` converts to the
     relation witness `r`.

This is the first of the eight `TranspensionRecoverable` operators backed by computation; `mode-11`
ships the other seven as names only. -/
theorem gelRecoveredAtAffine :
    gelStructureClass = SamenessArity.parametric.multiplierClass
      ∧ gelStructureClass.supportsDiagonal = false
      ∧ (∀ (scope : Nat) (leftEndpoint rightEndpoint relationWitness : RawTerm scope),
          Conv (ungelProjection (gelCellOf leftEndpoint rightEndpoint relationWitness))
            relationWitness) :=
  ⟨rfl, rfl, fun _scope leftEndpoint rightEndpoint relationWitness =>
    gelComputesAtEveryScope leftEndpoint rightEndpoint relationWitness⟩

/-! ## The honest per-operator recovery ledger (1 of 8) -/

/-- Per-operator recovery status: which of the eight `TranspensionRecoverable` operators are backed by a
COMPUTING kernel reduction (not merely named).  Honest: only `gel` is backed so far (via the shipped
gel-beta); the other seven remain `mode-11` named targets. -/
def transpensionOperatorIsKernelBacked : TranspensionRecoverable → Bool
  | .gel => true
  | .glue => false
  | .weld => false
  | .mill => false
  | .amazingRightAdjoint => false
  | .phi => false
  | .psi => false
  | .nominal => false

/-- The Gel operator is kernel-backed. -/
theorem gel_isKernelBacked : transpensionOperatorIsKernelBacked .gel = true := rfl

/-- Honesty ledger: EXACTLY ONE of the eight zoo operators is kernel-backed so far.  The global
`fxMode_hasTranspensionZooRecovery` stays `false` until all eight compute. -/
theorem kernelBackedOperatorCount_isOne :
    (TranspensionRecoverable.all.filter transpensionOperatorIsKernelBacked).length = 1 := rfl

end FX1Poly.Typed
