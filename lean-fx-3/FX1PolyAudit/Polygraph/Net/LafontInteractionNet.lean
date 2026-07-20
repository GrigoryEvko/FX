import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.LafontInteractionNet

/-! # FX1PolyAudit.Polygraph.Net.LafontInteractionNet — zero-axiom gate (NET-10)

Per-declaration zero-axiom gate for the Lafont interaction-net engine: the representation (agents with a
single principal port, rules, nets), the reduction step, the ORTHOGONALITY dividend (single-principal-port
⇒ unique partner ⇒ distinct active pairs are disjoint), and the STRONG-CONFLUENCE payoff (disjoint-redex
commutation = the one-step diamond, proved as a literal list equality), plus the honest general-graph wall
marker and the concrete fires.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- Bool / decidable-if micro-kit
#assert_no_axioms FX1Poly.Polygraph.lfnBandTrueLeft
#assert_no_axioms FX1Poly.Polygraph.lfnBandTrueRight
#assert_no_axioms FX1Poly.Polygraph.lfnIfEqTrue

-- representation (T1): agents, rules, nets
#assert_no_axioms FX1Poly.Polygraph.lfnAgent
#assert_no_axioms FX1Poly.Polygraph.lfnAgent.mk
#assert_no_axioms FX1Poly.Polygraph.lfnInteractionRule
#assert_no_axioms FX1Poly.Polygraph.lfnInteractionRule.mk
#assert_no_axioms FX1Poly.Polygraph.lfnRuleTable

-- hand-rolled append + expansion
#assert_no_axioms FX1Poly.Polygraph.lfnCat
#assert_no_axioms FX1Poly.Polygraph.lfnCatNil
#assert_no_axioms FX1Poly.Polygraph.lfnCatAssoc
#assert_no_axioms FX1Poly.Polygraph.lfnAgentAction
#assert_no_axioms FX1Poly.Polygraph.lfnAgentActionAtLeft
#assert_no_axioms FX1Poly.Polygraph.lfnAgentActionAtRight
#assert_no_axioms FX1Poly.Polygraph.lfnAgentActionAtOther
#assert_no_axioms FX1Poly.Polygraph.lfnNetExpand
#assert_no_axioms FX1Poly.Polygraph.lfnNetExpandSingleton
#assert_no_axioms FX1Poly.Polygraph.lfnNetExpandCat

-- rule lookup + reduction (T1)
#assert_no_axioms FX1Poly.Polygraph.lfnFindAgent
#assert_no_axioms FX1Poly.Polygraph.lfnLookupRule
#assert_no_axioms FX1Poly.Polygraph.lfnFireResolved
#assert_no_axioms FX1Poly.Polygraph.lfnFireRedex
#assert_no_axioms FX1Poly.Polygraph.lfnAgentPointsTo
#assert_no_axioms FX1Poly.Polygraph.lfnIsActivePair
#assert_no_axioms FX1Poly.Polygraph.lfnNetStep

-- orthogonality (T2)
#assert_no_axioms FX1Poly.Polygraph.lfnAgentPointsToFunctional
#assert_no_axioms FX1Poly.Polygraph.lfnIsActivePairPointsLR
#assert_no_axioms FX1Poly.Polygraph.lfnIsActivePairPointsRL
#assert_no_axioms FX1Poly.Polygraph.lfnActivePairPartnerUnique
#assert_no_axioms FX1Poly.Polygraph.lfnActivePairsShareImpliesEqual

-- strong confluence / disjoint-redex commutation (T3)
#assert_no_axioms FX1Poly.Polygraph.lfnNetAvoids
#assert_no_axioms FX1Poly.Polygraph.lfnNetExpandIdOfAvoids
#assert_no_axioms FX1Poly.Polygraph.lfnAgentActionCommute
#assert_no_axioms FX1Poly.Polygraph.lfnNetExpandCommute
#assert_no_axioms FX1Poly.Polygraph.lfnDisjointRedexCommute

-- honest wall
#assert_no_axioms FX1Poly.Polygraph.lfnHasGeneralGraphDiamond

-- concrete fires (T4) + supporting data
#assert_no_axioms FX1Poly.Polygraph.lfnDemoAgentA
#assert_no_axioms FX1Poly.Polygraph.lfnDemoAgentB
#assert_no_axioms FX1Poly.Polygraph.lfnDemoResult
#assert_no_axioms FX1Poly.Polygraph.lfnDemoRule
#assert_no_axioms FX1Poly.Polygraph.lfnDemoTable
#assert_no_axioms FX1Poly.Polygraph.lfnDemoNet
#assert_no_axioms FX1Poly.Polygraph.lfnFireExample
#assert_no_axioms FX1Poly.Polygraph.lfnDemoAnnih
#assert_no_axioms FX1Poly.Polygraph.lfnDemoTable2
#assert_no_axioms FX1Poly.Polygraph.lfnPairOneA
#assert_no_axioms FX1Poly.Polygraph.lfnPairOneB
#assert_no_axioms FX1Poly.Polygraph.lfnSpectator
#assert_no_axioms FX1Poly.Polygraph.lfnPairTwoA
#assert_no_axioms FX1Poly.Polygraph.lfnPairTwoB
#assert_no_axioms FX1Poly.Polygraph.lfnTwoRedexNet
#assert_no_axioms FX1Poly.Polygraph.lfnCommuteExample
#assert_no_axioms FX1Poly.Polygraph.lfnControlAgentA
#assert_no_axioms FX1Poly.Polygraph.lfnControlAgentB
#assert_no_axioms FX1Poly.Polygraph.lfnControlNet
#assert_no_axioms FX1Poly.Polygraph.lfnControlNotActive
#assert_no_axioms FX1Poly.Polygraph.lfnActiveExample

end FX1PolyAudit
