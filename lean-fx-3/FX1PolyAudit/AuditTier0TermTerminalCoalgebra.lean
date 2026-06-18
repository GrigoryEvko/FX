import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Codata.TerminalCoalgebra

/-! # FX1PolyAudit/AuditTier0TermTerminalCoalgebra — zero-axiom gate for term-3 (terminal coalgebra)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Codata/TerminalCoalgebra.lean`: the terminal
coalgebra of the stream functor — the carrier `FinalStream` with its co-structure `head` / `tail`, the
source coalgebra `StreamCoalgebra` + `iterate`, the anamorphism `ana` with its coalgebra-homomorphism laws
(`ana_head` / `ana_tail` / `ana_isHom`) and terminality (`ana_unique`), bisimulation (`IsBisimulation`)
with the coinduction principle (`bisim_observe`), the bisimilarity (`observationallyEqual` +
`observationallyEqual_isBisimulation`), and the self-mediation (`structureCoalgebra` +
`ana_structureCoalgebra`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — in particular no funext (equality is observational throughout). -/

namespace FX1PolyAudit

-- The terminal coalgebra carrier + its co-structure (observations / destructors)
#assert_no_axioms FX1Poly.Core.FinalStream
#assert_no_axioms FX1Poly.Core.FinalStream.head
#assert_no_axioms FX1Poly.Core.FinalStream.tail

-- The constructor + Lambek's lemma (the structure map is an iso ⇒ FinalStream is a fixpoint)
#assert_no_axioms FX1Poly.Core.FinalStream.cons
#assert_no_axioms FX1Poly.Core.FinalStream.head_cons
#assert_no_axioms FX1Poly.Core.FinalStream.tail_cons
#assert_no_axioms FX1Poly.Core.FinalStream.cons_head_tail

-- The source coalgebra + the anamorphism (corecursion)
#assert_no_axioms FX1Poly.Core.StreamCoalgebra
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.iterate
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.ana

-- The coalgebra-homomorphism laws (existence) + terminality (uniqueness up to bisimulation)
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.ana_head
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.ana_tail
#assert_no_axioms FX1Poly.Core.IsStreamCoalgebraHom
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.ana_isHom
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.ana_unique

-- Anamorphism fusion (UP functoriality) + coalgebra-homomorphism extensionality
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.ana_fusion
#assert_no_axioms FX1Poly.Core.StreamCoalgebra.coalgebraHom_ext

-- Bisimulation + the coinduction principle + the bisimilarity
#assert_no_axioms FX1Poly.Core.IsBisimulation
#assert_no_axioms FX1Poly.Core.FinalStream.bisim_observe
#assert_no_axioms FX1Poly.Core.FinalStream.observationallyEqual
#assert_no_axioms FX1Poly.Core.FinalStream.observationallyEqual_isBisimulation

-- The terminal object mediates itself (the op-dual of mediate_selfCocone)
#assert_no_axioms FX1Poly.Core.FinalStream.structureCoalgebra
#assert_no_axioms FX1Poly.Core.FinalStream.ana_structureCoalgebra

-- The concrete computing witness (corecursion produces a genuine infinite object)
#assert_no_axioms FX1Poly.Core.FinalStream.constStream
#assert_no_axioms FX1Poly.Core.FinalStream.constStream_observe
#assert_no_axioms FX1Poly.Core.FinalStream.constStream_unfold

end FX1PolyAudit
