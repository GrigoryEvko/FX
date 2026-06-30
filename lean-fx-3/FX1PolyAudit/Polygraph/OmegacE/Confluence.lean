import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.Confluence

/-! # FX1PolyAudit.Polygraph.OmegacE.Confluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.Confluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- CONFLUENCE / CHURCH-ROSSER (Confluence.lean): the decidability enabler. Joinable (∃ common reduct) is
-- reflexive/symmetric, contains RewritesMany, embeds into ConvertibleModulo, preserves length. The standard
-- metatheorem churchRosser_of_confluence (confluence ⟹ Church-Rosser, trans case merges common reducts via
-- the diamond) + convertibleModulo_iff_joinable_of_churchRosser (under CR, convertible = joinable, reducing
-- the symm-trans closure to a searchable ∃). HasConfluence/HasChurchRosser are PROPERTIES (discharged per
-- concrete system); decidability additionally needs a terminating normalizer (the slices below).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.refl

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.symm

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.ofRewritesMany

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.toConvertible

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.length_preserved

#assert_no_axioms FX1Poly.OmegacE.HasConfluence

#assert_no_axioms FX1Poly.OmegacE.HasChurchRosser

#assert_no_axioms FX1Poly.OmegacE.churchRosser_of_confluence

#assert_no_axioms FX1Poly.OmegacE.convertibleModulo_iff_joinable_of_churchRosser

-- NEWMAN'S LEMMA (Confluence.lean): confluence from the checkable local confluence. HasLocalConfluence (peak
-- of two single steps joinable — critical-pair-checkable) + IsTerminating (every word Acc under reduction) ⟹
-- HasConfluence (newman), via confluenceFromAccessible (Acc.rec well-founded tiling: local-confluence peak +
-- two strictly-smaller IH applications). THE tool to discharge HasConfluence on a concrete system; with
-- churchRosser_of_confluence + WordProblem's decision, a terminating locally-confluent system has a decidable
-- word problem. Acc.rec is propext-free here (constant-shaped motive).
#assert_no_axioms FX1Poly.OmegacE.HasLocalConfluence

#assert_no_axioms FX1Poly.OmegacE.IsTerminating

#assert_no_axioms FX1Poly.OmegacE.confluenceFromAccessible

#assert_no_axioms FX1Poly.OmegacE.newman

-- TERMINATION FROM A LENGTH MEASURE (Confluence.lean): IsLengthReducingSystem (every rule strictly shortens)
-- ⟹ IsTerminating (IsTerminating_of_lengthReducing), via length_lt_of_lengthReducing (one step strictly
-- decreases length) + Subrelation.accessible into InvImage (·<·) length (Nat.lt well-founded). Discharges the
-- termination hypothesis of the convergent-presentation decision from a CHECKABLE measure — with newman, a
-- concrete length-reducing system needs only local confluence + a reducer.
#assert_no_axioms FX1Poly.OmegacE.IsLengthReducingSystem

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesOneStep.length_lt_of_lengthReducing

#assert_no_axioms FX1Poly.OmegacE.IsTerminating_of_lengthReducing

end FX1PolyAudit
