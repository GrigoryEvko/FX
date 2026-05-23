import LeanFX2.Foundation.Polygraph.GeneratorOutputType
import LeanFX2.Tools.DependencyAudit

/-! # AuditGeneratorOutputType — zero-axiom audit for the P2.2 Π/Σ family.

Smoke gates for accelerate-P2.2 (#2123) — the per-Generator outputType
extractor family, Π/Σ portion (6 of the 74 ctors).

## Coverage

Six extractors + six matching `rfl` theorems covering the Π/Σ core:

* `Generator.outputTypeApp` / `_matches_Term_app` — non-dep function
  application.
* `Generator.outputTypeLam` / `_matches_Term_lam` — non-dep function
  intro.
* `Generator.outputTypeLamPi` / `_matches_Term_lamPi` — dependent Π
  function intro.
* `Generator.outputTypePair` / `_matches_Term_pair` — Σ pair intro.
* `Generator.outputTypeFst` / `_matches_Term_fst` — Σ first
  projection.
* `Generator.outputTypeSnd` / `_matches_Term_snd` — Σ second
  projection (dependent — output is
  `secondType.subst0 firstType (RawTerm.fst pairRaw)`).

The P2.0-shipped `Generator.outputTypeAppPi` covers dependent function
application; combined with these 6, the Π/Σ family is structurally
complete (7 of 74 outputType ctors).

All clean = P2.2 Π/Σ-family extractor PASS.  The remaining 67
extractors (closed-type / HOTT / cubical / modal / type-code / record
/ codata / session / effect ctors) land in subsequent P2.2 batches.
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

end LeanFX2.SmokeGeneratorOutputType
