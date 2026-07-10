import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaGen
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDecisionGen
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadBespokeFreeWalk — the transitive-constant META-WALK
(POLY-TAB r6, the r4 gold standard for the monad lane)

Beyond `#assert_no_axioms`, POLY-TAB's re-founding wants a BESPOKE-FREE certificate: the born-generic soundness leg
and decision assembly must have NO `MonadSaturatedTwoCellConv` anywhere in their transitive definition-dependency
closure (importing the bespoke FILE is fine; DEPENDING on the bespoke CONSTANT is not).  This file supplies two
build-failing commands that walk the constant closure (`collectDependencies`, `DependencyAudit`):

  * **`#assert_constant_free_of TARGET needle NEEDLE`** — throws if `NEEDLE` appears in `TARGET`'s transitive
    constant closure (the bespoke-free gate).
  * **`#assert_constant_depends_on TARGET needle NEEDLE`** — throws if `NEEDLE` does NOT appear (the
    NEEDLE-DETECTOR CONTROL: proves the walk is not vacuously passing — it CAN find the needle when present).

★ **The walk is EXHAUSTIVE (`includeStdlib := true`).**  It does NOT prune internal names, because a structure-field
body (e.g. a canonicalization's completeness field) is lifted by Lean into an INTERNAL auxiliary def, and a
pruning walk (`includeStdlib := false`) would silently DROP that auxiliary — hiding a bespoke reference behind it and
turning the gate UNSOUND.  The needle-detector controls below (positive controls on the bespoke deciders
`monadMonotoneMapOf_mapEqOfConv` / `monadSaturatedTwoCellDecision`) confirm the exhaustive walk detects the needle
exactly when present. -/

namespace FX1PolyAudit

open Lean Elab Command

/-- Build-failing bespoke-free gate: `TARGET`'s FULL transitive constant closure (exhaustive, no internal pruning)
must NOT contain `NEEDLE`. -/
elab "#assert_constant_free_of " targetSyntax:ident " needle " needleSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  let needleName := needleSyntax.getId
  if !environment.contains targetName then
    throwError "unknown target in bespoke-free walk: {targetName}"
  if !environment.contains needleName then
    throwError "unknown needle in bespoke-free walk: {needleName}"
  let dependencies := collectDependencies environment targetName (includeStdlib := true) (fuel := 4000000)
  if dependencies.contains needleName then
    throwError "bespoke-free walk FAILED: {targetName} transitively depends on the bespoke constant {needleName}"
  else
    logInfo m!"bespoke-free walk ok: {targetName} has NO {needleName} in its FULL constant closure \
      ({dependencies.size} constants walked)"

/-- The NEEDLE-DETECTOR CONTROL: `TARGET`'s FULL transitive constant closure MUST contain `NEEDLE` (else the
`free_of` walk would be vacuously passing). -/
elab "#assert_constant_depends_on " targetSyntax:ident " needle " needleSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  let needleName := needleSyntax.getId
  if !environment.contains targetName then
    throwError "unknown target in needle-detector control: {targetName}"
  if !environment.contains needleName then
    throwError "unknown needle in needle-detector control: {needleName}"
  let dependencies := collectDependencies environment targetName (includeStdlib := true) (fuel := 4000000)
  if dependencies.contains needleName then
    logInfo m!"needle-detector control ok: {targetName} DOES transitively depend on {needleName} \
      (the walk detects the needle when present)"
  else
    throwError "needle-detector control FAILED: {targetName} does NOT depend on {needleName} — the \
      bespoke-free walk would be vacuously passing"

/-! ## The born-generic Δ soundness leg + decision ASSEMBLY are BESPOKE-FREE (exhaustive walk) -/

#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadIsMonotoneMapCongruence
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadMonotoneMapOf_mapEqOfConvGen
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadDecideSaturatedConvOverGen
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadSaturatedGenDecisionModulo
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv

/-! ## WAVE 2: the born-generic normalize + the fully bespoke-free native decider are BESPOKE-FREE (exhaustive walk)

The completeness port `monadNormalizeGen` (`WalkingMonad/MonadNormalizeGen`) and the terminal native decider it
inhabits (`monadSaturatedCanonicalizationGenNative` / `decideSaturatedConvOverMonadNative`) have NO
`MonadSaturatedTwoCellConv` anywhere in their FULL transitive constant closure — unlike the INTERIM decider (whose
completeness field rode the bespoke normalize through `monadSaturated_to_generic`), recorded as `depends_on` below.
This is the wave-2 flip: the `false → true` of `fxMonad_hasGenericNativeDecider`. -/

#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadNormalizeGen
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadSaturatedCanonicalizationGenNative
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.decideSaturatedConvOverMonadNative
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv

/-! ## The NEEDLE-DETECTOR CONTROLS: the BESPOKE deciders DO depend on `MonadSaturatedTwoCellConv` -/

#assert_constant_depends_on FX1Poly.Polygraph.monadMonotoneMapOf_mapEqOfConv
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_depends_on FX1Poly.Polygraph.monadSaturatedTwoCellDecision
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv

/-! ## The interim needle-detector controls were RETIRED with the interim decider (MONAD-R7 r2, S5)

At r6 two additional needle-detector controls recorded the HONEST wave-1 residual: the INTERIM decider
(`monadSaturatedCanonicalizationGenViaBridge` / `decideSaturatedConvOverMonadInterim`, whose completeness field
transported the bespoke normalize `monadConvOfMapEq_ofNormalize` through `monadSaturated_to_generic`) DID depend on
`MonadSaturatedTwoCellConv` — a `depends_on` (NOT `free_of`) statement, and a second confirmation that the
exhaustive walk sees through a structure-field internal auxiliary that a pruning walk would drop.  MONAD-R7 r2 (S5)
RETIRED the interim decider (superseded by the fully bespoke-free `decideSaturatedConvOverMonadNative`), so those two
`depends_on` controls are gone with it.  The BESPOKE needle-detector controls above (`monadMonotoneMapOf_mapEqOfConv`
/ `monadSaturatedTwoCellDecision`) remain and still positively confirm the exhaustive walk finds
`MonadSaturatedTwoCellConv` whenever present — so the native `free_of` gates are not vacuously passing. -/

end FX1PolyAudit
