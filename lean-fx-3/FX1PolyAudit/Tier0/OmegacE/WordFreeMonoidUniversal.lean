import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.WordFreeMonoidUniversal

/-! # FX1PolyAudit.Tier0.OmegacE.WordFreeMonoidUniversal

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.WordFreeMonoidUniversal`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- FREE-MONOID UNIVERSAL PROPERTY: OmegacEWord is the FREE monoid on its generators — for any target monoid
-- (explicit multiply/unit + laws) and generator interpretation, foldOut is the unique extending monoid
-- homomorphism.  The categorical "free" characterization (how to map OUT of the free structure), the basis
-- for the word-problem decision and normal-form targets.  All zero-axiom (List.foldr + structural list
-- inductions).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_empty

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_append

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_singleton

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_unique

-- UNIVERSAL-PROPERTY CONSEQUENCES: hom_ext (two monoid homs out of the free monoid agreeing on generators
-- are equal — uniqueness packaged for direct use) and length_eq_foldOut (word length IS the canonical free-
-- monoid hom into (ℕ,+,0) sending each generator to 1 — the textbook universal-property instance).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.hom_ext

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.length_eq_foldOut

end FX1PolyAudit
