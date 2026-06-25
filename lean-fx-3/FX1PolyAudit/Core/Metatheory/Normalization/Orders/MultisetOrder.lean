import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Orders.MultisetOrder

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Orders.MultisetOrder

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Orders.MultisetOrder`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The Dershowitz-Manna multiset ordering + its well-foundedness, the foundational termination order.
-- Mechanized zero-axiom over Init only: a true multiset is the quotient of List by permutation, but Quot.sound
-- is banned, so MultisetRedOne is an existential on plain List (prefix ++ removed :: suffix shrinks to
-- prefix ++ added ++ suffix, added all below removed).  isWellFounded is the Dershowitz-Manna theorem via the
-- nested-Acc argument (emptyAccessible + consAccessible with the accAppendBelow inner helper).  Inversion by
-- obtain + cases prefixList (clean List split, no indexed-cases propext leak).  replaceHead/underContext make
-- the order constructible.  Zero-axiom.
#assert_no_axioms FX1Poly.Core.MultisetRedOne

#assert_no_axioms FX1Poly.Core.MultisetRedOne.replaceHead

#assert_no_axioms FX1Poly.Core.MultisetRedOne.underContext

#assert_no_axioms FX1Poly.Core.MultisetRedOne.emptyAccessible

#assert_no_axioms FX1Poly.Core.MultisetRedOne.consAccessible

#assert_no_axioms FX1Poly.Core.MultisetRedOne.isWellFounded

end FX1PolyAudit
