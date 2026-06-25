import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Semantics.GameSemantics

/-! # FX1PolyAudit/AuditTier0TermGameSemantics — zero-axiom gate for term-24 (game semantics)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Semantics/GameSemantics.lean`: the polarity duality
(`Polarity` / `Polarity.flip` / `flip_flip` / `flip_ne`), arenas + dual arenas (`Arena` / `dualArena` /
`dualArena_polarity` / `dualArena_involutive_pointwise`), even plays + the Opponent projection (`EvenPlay` /
`opponentMoves`), arena-legality (`RespectsArena` / `respectsArena_prefixClosed`), deterministic strategies
with the determinacy theorem (`Strategy` / `Strategy.determinedByOpponent`), and the answer-game witness
(`answerArena` / `answerStrategy` / `answerStrategy_acceptsAnswer` / `answerStrategy_opponentMoves` /
`answerStrategy_respectsArena`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Polarity + the duality involution
#assert_no_axioms FX1Poly.Core.Polarity
#assert_no_axioms FX1Poly.Core.Polarity.flip
#assert_no_axioms FX1Poly.Core.Polarity.flip_flip
#assert_no_axioms FX1Poly.Core.Polarity.flip_ne

-- Arenas + the dual arena (pointwise-involutive)
#assert_no_axioms FX1Poly.Core.Arena
#assert_no_axioms FX1Poly.Core.dualArena
#assert_no_axioms FX1Poly.Core.dualArena_polarity
#assert_no_axioms FX1Poly.Core.dualArena_involutive_pointwise

-- Even plays + the Opponent projection + arena-legality
#assert_no_axioms FX1Poly.Core.EvenPlay
#assert_no_axioms FX1Poly.Core.opponentMoves
#assert_no_axioms FX1Poly.Core.RespectsArena
#assert_no_axioms FX1Poly.Core.respectsArena_prefixClosed

-- The arena algebra: sum/empty arenas + the star-autonomous De Morgan duality
#assert_no_axioms FX1Poly.Core.arenaSum
#assert_no_axioms FX1Poly.Core.emptyArena
#assert_no_axioms FX1Poly.Core.dualArena_sum_deMorgan

-- Strategies + determinacy (a strategy is a function of Opponent's moves)
#assert_no_axioms FX1Poly.Core.Strategy
#assert_no_axioms FX1Poly.Core.Strategy.determinedByOpponent

-- The answer-game witness
#assert_no_axioms FX1Poly.Core.answerArena
#assert_no_axioms FX1Poly.Core.answerStrategy
#assert_no_axioms FX1Poly.Core.answerStrategy_acceptsAnswer
#assert_no_axioms FX1Poly.Core.answerStrategy_opponentMoves
#assert_no_axioms FX1Poly.Core.answerStrategy_respectsArena

end FX1PolyAudit
