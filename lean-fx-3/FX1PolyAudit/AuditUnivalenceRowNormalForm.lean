import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.UnivalenceRowNormalForm

/-! # FX1PolyAudit/AuditUnivalenceRowNormalForm — zero-axiom gate for the univalence-row normalizer

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/UnivalenceRowNormalForm.lean`: the
bottom-up structural normalizer (`RawTerm.headIsUniverseCode`, `RawTerm.univNFRoot`, `RawTerm.univNF`,
`RawTermChildren.univNF`), the root-firing characterizations, and the confluence invariant
(`univNF_preservesStep` — a single univalence step preserves the normal form).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — confluence in computable form, no Acc.rec / SN / Newman. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.headIsUniverseCode
#assert_no_axioms FX1Poly.Core.RawTerm.univNFRoot
#assert_no_axioms FX1Poly.Core.RawTerm.univNF
#assert_no_axioms FX1Poly.Core.RawTermChildren.univNF
#assert_no_axioms FX1Poly.Core.univNF_universeCode
#assert_no_axioms FX1Poly.Core.univNFRoot_idCodeUniverse
#assert_no_axioms FX1Poly.Core.univNFRoot_equivCode
#assert_no_axioms FX1Poly.Core.univNF_preservesStep

end FX1PolyAudit
