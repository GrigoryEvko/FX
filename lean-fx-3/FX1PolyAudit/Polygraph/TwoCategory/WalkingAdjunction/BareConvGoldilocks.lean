import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvGoldilocks

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.BareConvGoldilocks — zero-axiom gate

Per-declaration zero-axiom gate for the bare-`TwoCellConv` Goldilocks candidate: the two new bare-conv moments
(`RawTwoCellExpr.rSum` / `RawTwoCellExpr.crossSum`) and their step / conv invariance (all four `_eq` lemmas,
including the interchange critical pair); the whiskerExchange separating pair (`whiskerExchangeLHS` /
`whiskerExchangeRHS`, the faithful `whiskerExchange_convFull`, the equal `whiskerSum`, the distinct `crossSum`,
and the resulting `whiskerExchange_not_twoCellConv`); the whiskerSum-only + full-family candidates
(`bareConvCandidateWS` / `bareConvCandidate`) with soundness and decidability
(`adjunctionDecideBareConvCandidate`); the incompleteness witness (`bareConvCandidateWS_not_complete`) and the
crossSum refinement (`bareConvCandidate_excludes_whiskerExchange`); the non-vacuity smokes
(`bareConvCandidate_accepts_parallelUnits` / `bareConvCandidate_rejects_snake`); and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.rSum
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.crossSum
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.rSum_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.rSum_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.crossSum_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.crossSum_eq
#assert_no_axioms FX1Poly.Polygraph.whiskerExchangeLHS
#assert_no_axioms FX1Poly.Polygraph.whiskerExchangeRHS
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_convFull
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_whiskerSum_eq
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_rSum_eq
#assert_no_axioms FX1Poly.Polygraph.whiskerExchangeLHS_crossSum
#assert_no_axioms FX1Poly.Polygraph.whiskerExchangeRHS_crossSum
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_crossSum_differs
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_not_twoCellConv
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidateWS
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidateWS_of_twoCellConv
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate_of_twoCellConv
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideBareConvCandidate
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidateWS_not_complete
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate_excludes_whiskerExchange
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_crossSum_not_determined
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate_accepts_parallelUnits
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate_rejects_snake
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvSeparatingFamilyCharacterized

end FX1PolyAudit
