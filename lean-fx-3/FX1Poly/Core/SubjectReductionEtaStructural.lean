import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.StepEta

/-! # Foundation/PolyCell/Core/SubjectReductionEtaStructural

Subject-reduction arms for the structurally recognizable eta rules.

This file intentionally handles only eta rules whose source/target do
not require binder freshness or strengthening:

* pair eta: `pair (fst p) (snd p) -> p`
* modal eta: `modIntro (modElim m) -> m`
* Glue eta: `glueIntro (glueElim g) g -> g`

Function and path eta depend on `RawTerm.strengthen` and live in the
separate binder-eta task.  Clock and parametricity eta are reserved
until their generators exist in the current `Generator` enum.
-/

namespace FX1Poly.Core

/-- **SR-eta arm: pair eta preserves `HasCertifiedCellDim0`.**

If the eta source `pair (fst p) (snd p)` is certified, then the
projected pair term `p` is certified.  The certificate is recovered
from the argument spine of the certified `fst p` child. -/
theorem HasCertifiedCellDim0.preservedByEtaPair
    {profile : PolyProfile} {scope : Nat}
    {pairTerm : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.etaPairSource pairTerm)) :
    HasCertifiedCellDim0 (profile := profile) pairTerm := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons fstCell _restSpine =>
        generalize hSort : (ChildSpec.termSameScope.cellSort) = innerSort
          at fstCell
        cases fstCell with
        | gen _ _ fstInnerSpine =>
          exact .intro .term (fstInnerSpine.headAtDim0 rfl)

/-- **SR-eta arm: modal intro/elim eta preserves `HasCertifiedCellDim0`.**

If the eta source `modIntro (modElim m)` is certified, then the modal
term `m` is certified.  Profile-level modality admissibility is not
proved here; this arm only projects the already-certified child carried
by the raw structural source. -/
theorem HasCertifiedCellDim0.preservedByEtaModIntro
    {profile : PolyProfile} {scope : Nat}
    {modalTerm : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.etaModIntroSource modalTerm)) :
    HasCertifiedCellDim0 (profile := profile) modalTerm := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons modElimCell _restSpine =>
        generalize hSort : (ChildSpec.termSameScope.cellSort) = innerSort
          at modElimCell
        cases modElimCell with
        | gen _ _ modElimInnerSpine =>
          exact .intro .term (modElimInnerSpine.headAtDim0 rfl)

/-- **SR-eta arm: Glue intro/elim eta preserves `HasCertifiedCellDim0`.**

If the eta source `glueIntro (glueElim g) g` is certified, then the
glued term `g` is certified.  The source stores `g` directly as the
second child, so the proof is a single spine projection. -/
theorem HasCertifiedCellDim0.preservedByEtaGlueIntro
    {profile : PolyProfile} {scope : Nat}
    {gluedTerm : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.etaGlueIntroSource gluedTerm)) :
    HasCertifiedCellDim0 (profile := profile) gluedTerm := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      exact .intro .term ((outerSpine.tail).headAtDim0 rfl)

end FX1Poly.Core
