import LeanFX2.Foundation.Polygraph.GeneratorOutputType
import LeanFX2.Tools.DependencyAudit

/-! # AuditGeneratorOutputType — zero-axiom audit for the P2.2 Π/Σ + recursor families.

Smoke gates for accelerate-P2.2 (#2123) — per-Generator outputType
extractors, currently covering 12 of the 74 ctors (Π/Σ + closed-type
recursors).

## Coverage

Twelve extractors + twelve matching `rfl` theorems across two families:

**Π/Σ family** (6 ctors at `LeanFX2/Term.lean:104-146`):

* `Generator.outputTypeApp` — non-dep function application.
* `Generator.outputTypeLam` — non-dep function intro.
* `Generator.outputTypeLamPi` — dependent Π intro.
* `Generator.outputTypePair` — Σ pair intro.
* `Generator.outputTypeFst` — Σ first projection.
* `Generator.outputTypeSnd` — dependent Σ second projection.

**Closed-type recursor family** (6 ctors at `LeanFX2/Term.lean:152-234`):

* `Generator.outputTypeBoolElim` — dependent bool eliminator (output is
  `motiveType.subst0 Ty.bool scrutineeRaw`).
* `Generator.outputTypeNatElim` — non-dep nat eliminator.
* `Generator.outputTypeNatRec` — non-dep nat recursor.
* `Generator.outputTypeListElim` — non-dep list eliminator.
* `Generator.outputTypeOptionMatch` — non-dep option matcher.
* `Generator.outputTypeEitherMatch` — non-dep either matcher.

Plus the P2.0-shipped `Generator.outputTypeAppPi` (in `Generator.lean`)
for dependent function application — 13 of 74 outputType ctors covered.

All clean = P2.2 Π/Σ + recursor extractor PASS.  The remaining 61
extractors (HOTT / cubical / modal / type-code / record / codata /
session / effect / P-S vocabulary / transpFill) land in subsequent
P2.2 batches.
-/

namespace LeanFX2.SmokeGeneratorOutputType

#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeApp
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeApp_matches_Term_app
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLam
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLam_matches_Term_lam
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLamPi
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLamPi_matches_Term_lamPi
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypePair
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypePair_matches_Term_pair
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeFst
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeFst_matches_Term_fst
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSnd
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSnd_matches_Term_snd
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeBoolElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeBoolElim_matches_Term_boolElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatElim_matches_Term_natElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatRec
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatRec_matches_Term_natRec
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeListElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeListElim_matches_Term_listElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOptionMatch
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOptionMatch_matches_Term_optionMatch
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEitherMatch
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEitherMatch_matches_Term_eitherMatch

#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeApp
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeApp_matches_Term_app
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLam
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLam_matches_Term_lam
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLamPi
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeLamPi_matches_Term_lamPi
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypePair
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypePair_matches_Term_pair
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeFst
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeFst_matches_Term_fst
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSnd
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSnd_matches_Term_snd
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeBoolElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeBoolElim_matches_Term_boolElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatElim_matches_Term_natElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatRec
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeNatRec_matches_Term_natRec
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeListElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeListElim_matches_Term_listElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOptionMatch
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOptionMatch_matches_Term_optionMatch
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEitherMatch
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEitherMatch_matches_Term_eitherMatch

end LeanFX2.SmokeGeneratorOutputType
