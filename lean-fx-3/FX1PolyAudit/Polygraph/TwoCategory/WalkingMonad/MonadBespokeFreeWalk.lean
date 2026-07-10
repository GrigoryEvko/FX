import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaGen
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem

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

The walk uses `includeStdlib := false` so it stays inside the FX/Init closure (Lean-core plumbing cannot introduce
an FX1Poly constant like `MonadSaturatedTwoCellConv`), keeping it fast and exact for the FX needle. -/

namespace FX1PolyAudit

open Lean Elab Command

/-- Build-failing bespoke-free gate: `TARGET`'s transitive constant closure must NOT contain `NEEDLE`. -/
elab "#assert_constant_free_of " targetSyntax:ident " needle " needleSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  let needleName := needleSyntax.getId
  if !environment.contains targetName then
    throwError "unknown target in bespoke-free walk: {targetName}"
  if !environment.contains needleName then
    throwError "unknown needle in bespoke-free walk: {needleName}"
  let dependencies := collectDependencies environment targetName (includeStdlib := false) (fuel := 2000000)
  if dependencies.contains needleName then
    throwError "bespoke-free walk FAILED: {targetName} transitively depends on the bespoke constant {needleName}"
  else
    logInfo m!"bespoke-free walk ok: {targetName} has NO {needleName} in its constant closure \
      ({dependencies.size} FX/Init constants walked)"

/-- The NEEDLE-DETECTOR CONTROL: `TARGET`'s transitive constant closure MUST contain `NEEDLE` (else the walk would
be vacuously passing above). -/
elab "#assert_constant_depends_on " targetSyntax:ident " needle " needleSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  let needleName := needleSyntax.getId
  if !environment.contains targetName then
    throwError "unknown target in needle-detector control: {targetName}"
  if !environment.contains needleName then
    throwError "unknown needle in needle-detector control: {needleName}"
  let dependencies := collectDependencies environment targetName (includeStdlib := false) (fuel := 2000000)
  if dependencies.contains needleName then
    logInfo m!"needle-detector control ok: {targetName} DOES transitively depend on {needleName} \
      (the walk detects the needle when present)"
  else
    throwError "needle-detector control FAILED: {targetName} does NOT depend on {needleName} — the \
      bespoke-free walk would be vacuously passing"

/-! ## The born-generic Δ soundness leg + decision assembly are BESPOKE-FREE -/

#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadIsMonotoneMapCongruence
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadMonotoneMapOf_mapEqOfConvGen
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadDecideSaturatedConvOverGen
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadSaturatedGenDecisionModulo
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv

/-! ## The NEEDLE-DETECTOR CONTROL: the BESPOKE soundness leg DOES depend on `MonadSaturatedTwoCellConv` -/

#assert_constant_depends_on FX1Poly.Polygraph.monadMonotoneMapOf_mapEqOfConv
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_constant_depends_on FX1Poly.Polygraph.monadSaturatedTwoCellDecision
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv

end FX1PolyAudit
