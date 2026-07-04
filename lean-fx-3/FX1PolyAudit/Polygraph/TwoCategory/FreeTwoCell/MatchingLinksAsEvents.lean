import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLinksAsEvents

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingLinksAsEvents — zero-axiom gate

Per-declaration zero-axiom gate for the links-as-events self-replay: the stored-edge
completeness, the two directional view transports, the Bool-level self-replay equality, and
the additive exchange decomposition (the private lookup/root plumbing is covered
transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.sameComponent_ofLinkMember
#assert_no_axioms FX1Poly.Polygraph.foldConnected_ofLinksView
#assert_no_axioms FX1Poly.Polygraph.linksView_ofFoldConnected
#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents_selfLinks
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_overLinks_exchange
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasLinksAsEventsExchange

end FX1PolyAudit
