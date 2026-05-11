import LeanFX2.Foundation.Polygraph.Dim2Diamond

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

/-! K11.17 — `Diamond.toDim2Cell` dim-2 polygraph embedding for the
cd_lemma diamond coherence.  Each `#print axioms` line below must
report "does not depend on any axioms". -/

/-- Smoke: diamond cell between two β rules. -/
def diamondBetaAppBetaFstPair_smoke : PolyCell 2 0 0 :=
  Diamond.toDim2Cell StepLabel.betaApp StepLabel.betaFstPair

/-- Smoke: diamond cell between two cong rules. -/
def diamondAppLeftAppRight_smoke : PolyCell 2 0 0 :=
  Diamond.toDim2Cell StepLabel.appLeft StepLabel.appRight

/-- Smoke: trivial diamond (label paired with itself). -/
def diamondReflexiveBetaApp_smoke : PolyCell 2 0 0 :=
  Diamond.toDim2Cell StepLabel.betaApp StepLabel.betaApp

/-- Sanity: the embedding's body reduces by `rfl`. -/
example :
    Diamond.toDim2Cell StepLabel.betaApp StepLabel.betaFstPair =
      PolyCell.cell StepLabel.betaApp.toDim1Cell
                    StepLabel.betaFstPair.toDim1Cell 0 := rfl

#print axioms Diamond.toDim2Cell
#print axioms diamondBetaAppBetaFstPair_smoke
#print axioms diamondAppLeftAppRight_smoke
#print axioms diamondReflexiveBetaApp_smoke

end LeanFX2.Smoke
