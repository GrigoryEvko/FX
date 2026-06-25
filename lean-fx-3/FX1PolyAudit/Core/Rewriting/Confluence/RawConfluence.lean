import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Confluence.RawConfluence

/-! # FX1PolyAudit.Core.Rewriting.Confluence.RawConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Confluence.RawConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Unconditional raw confluence, discharged through the TABLE route
-- (StepStar.tableRouteConfluence above): global Church-Rosser for the raw StepStar relation with
-- no strong-normalization assumption (raw beta+iota is not SN).  The historical bespoke route
-- (ParStep per-iota mirror + complete development + Takahashi triangle) is RETIRED — the abstract
-- DiamondProperty/Confluent.ofTriangle vocabulary above survives for the table lane's own
-- Takahashi argument (TableTakahashiTriangle).
#assert_no_axioms FX1Poly.Core.StepStar.rawConfluence

-- The Newman-precursor strip property, unconditional via the table route
-- (StepStar.tableRouteStrip): a single Step out of a source joins against any StepStar chain out
-- of it.  A distinct statement from rawConfluence (one-vs-many vs many-vs-many);
-- confluence_of_strip turns it into the same Church-Rosser result.  No SN assumption.
#assert_no_axioms FX1Poly.Core.StepStar.rawStrip

-- Raw Conv (= StepStar.Join) is an unconditional equivalence relation.  Conv.refl / Conv.sym are structural;
-- Conv.trans is the consequence of Church-Rosser, discharged by StepStar.rawConfluence (which supplies the
-- confluence hypothesis), so Conv.trans + Conv.equivalence + the calc-enabling Trans instance hold
-- unconditionally, with no strong-normalization premise (raw beta+iota is not SN).  This is the foundation the
-- raw-layer conversion checker rests on.
#assert_no_axioms FX1Poly.Core.Conv.trans

#assert_no_axioms FX1Poly.Core.Conv.equivalence

#assert_no_axioms FX1Poly.Core.Conv.instTrans

-- Uniqueness of normal forms with no termination hypothesis.  StepStar.rawConfluence joins any two
-- reductions of a common source, so two normal reducts coincide whether or not the source terminates, making
-- "the normal form" a well-defined partial function on all raw terms.  The proof reuses Conv.eq_of_noStep +
-- isStepNormalForm_blocks_step, joining via rawConfluence.
#assert_no_axioms FX1Poly.Core.normalForm_unique_of_confluence

-- Conv equals normal-form equality with no SN hypothesis.  rawConfluence + normalForm_unique_of_confluence
-- discharge the per-term confluence witnesses, so the iff holds for any two terms that reduce to normal forms.
-- This separates decidable Conv into existence-of-normal-forms (the SN obligation, gated) and
-- correctness-of-normal-form-comparison (pure confluence, unconditional).  The decidable wrapper decides Conv
-- via instDecidableEqRawTerm given the normal-form witnesses, no SN premise.
#assert_no_axioms FX1Poly.Core.Conv.iff_normalForms_eq_of_confluence

#assert_no_axioms FX1Poly.Core.Conv.decidableOfNormalForms

-- The Path-B decider (polycell.md §2.3) with the confluence hypothesis discharged.  Conv.iff_normalForm_eq /
-- Conv.decidableOfNormalizer take a Normalizer and StepStar.HasConfluence; rawConfluence discharges the latter,
-- so a Normalizer alone decides Conv as normal-form equality.  The Normalizer (a total normal-form function)
-- remains the SN obligation (raw beta+iota has no global normalizer); the separate confluence assumption a
-- normalizer construction would otherwise also supply is what this discharges.
#assert_no_axioms FX1Poly.Core.Normalizer.conv_iff_normalForm_eq

#assert_no_axioms FX1Poly.Core.Normalizer.decidableConv

end FX1PolyAudit
