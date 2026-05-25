import LeanFX2.Foundation._deprecated_polygraph.Dim1Equivalence

namespace LeanFX2.Smoke

open LeanFX2.Foundation._deprecated_polygraph

/-! K11.15 + K11.16 — `Dim1Cell.toStepLabel?` extraction + the
`StepLabel ⇌ Dim1Cell` roundtrip equivalence.  Each `#print axioms`
line below must report "does not depend on any axioms".

K11.15 ships:
* `StepLabel.fromIndex? : Nat -> Option StepLabel` decoding a numeric
  index in 0..109 back to the matching `StepLabel`.
* `Dim1Cell.toStepLabel? : PolyCell 1 0 0 -> Option StepLabel`
  extracting the label encoded in a dim-1 cell at the trivial
  boundary.

K11.16 ships:
* `StepLabel.fromIndex_index` — every label's index decodes to itself.
* `Dim1Cell.toStepLabel?_toDim1Cell` — full polygraph-level roundtrip
  via `cellIdx` reduction + `fromIndex_index`. -/

/-- Smoke: decode of `appLeft`'s index. -/
def stepLabelDecodeFirst_smoke : Option StepLabel := StepLabel.fromIndex? 0

/-- Smoke: decode of `eqArrowHet`'s index. -/
def stepLabelDecodeLast_smoke : Option StepLabel := StepLabel.fromIndex? 109

/-- Smoke: decode of an out-of-range index yields `none`. -/
def stepLabelDecodeOutOfRange_smoke : Option StepLabel :=
  StepLabel.fromIndex? 9999

/-- Smoke: full extraction on a representative cell. -/
def stepLabelExtractMid_smoke : Option StepLabel :=
  Dim1Cell.toStepLabel? StepLabel.betaApp.toDim1Cell

/-- Sanity: out-of-range decode is `none`. -/
example : StepLabel.fromIndex? 9999 = none := rfl

/-- Sanity: representative roundtrip. -/
example : Dim1Cell.toStepLabel? StepLabel.betaApp.toDim1Cell
        = some StepLabel.betaApp := rfl

#print axioms StepLabel.fromIndex?
#print axioms Dim1Cell.toStepLabel?
#print axioms StepLabel.fromIndex_index
#print axioms Dim1Cell.toStepLabel?_toDim1Cell
#print axioms stepLabelDecodeFirst_smoke
#print axioms stepLabelDecodeLast_smoke
#print axioms stepLabelDecodeOutOfRange_smoke
#print axioms stepLabelExtractMid_smoke

end LeanFX2.Smoke
