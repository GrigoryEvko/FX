import LeanFX2.Foundation.Polygraph.GeneratorOutputType
import LeanFX2.Tools.DependencyAudit

/-! # AuditGeneratorOutputType — zero-axiom audit for the P2.2 Π/Σ + recursor + HOTT families.

Smoke gates for accelerate-P2.2 (#2123) — per-Generator outputType
extractors, currently covering 19 of the 74 ctors (Π/Σ + closed-type
recursors + HOTT identity / observational / strict identity / equiv-app).

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

**HoTT identity + observational + strict-identity + equivApp family**
(7 ctors at `LeanFX2/Term.lean:236-294, 791-797`):

* `Generator.outputTypeRefl` — HoTT identity-type reflexivity:
  `Ty.id carrier rawWitness rawWitness`.
* `Generator.outputTypeIdJ` — non-dep HoTT J eliminator.
* `Generator.outputTypeOeqRefl` — observational reflexivity:
  `Ty.oeq carrier rawWitness rawWitness`.
* `Generator.outputTypeOeqJ` — non-dep observational J eliminator.
* `Generator.outputTypeIdStrictRefl` — strict-identity reflexivity
  (carries `mode = Mode.strict` hypothesis):
  `Ty.idStrict carrier rawWitness rawWitness`.
* `Generator.outputTypeIdStrictRec` — non-dep strict-identity
  recursor (carries `mode = Mode.strict` hypothesis).
* `Generator.outputTypeEquivApp` — equivalence application:
  `Ty.equiv carrierA carrierB → carrierA → carrierB`.

Plus the P2.0-shipped `Generator.outputTypeAppPi` (in `Generator.lean`)
for dependent function application — 20 of 74 outputType ctors covered.

All clean = P2.2 Π/Σ + recursor + HOTT extractor PASS.  The remaining
54 extractors (cubical / modal / type-code / record / codata /
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
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeRefl
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeRefl_matches_Term_refl
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdJ
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdJ_matches_Term_idJ
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqRefl
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqRefl_matches_Term_oeqRefl
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqJ
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqJ_matches_Term_oeqJ
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRefl
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRefl_matches_Term_idStrictRefl
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRec
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRec_matches_Term_idStrictRec
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEquivApp
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEquivApp_matches_Term_equivApp
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModIntro
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModIntro_matches_Term_modIntro
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModElim_matches_Term_modElim
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSubsume
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSubsume_matches_Term_subsume
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval0
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval0_matches_Term_interval0
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval1
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval1_matches_Term_interval1
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalOpp
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalOpp_matches_Term_intervalOpp
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalMeet
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalMeet_matches_Term_intervalMeet
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalJoin
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalJoin_matches_Term_intervalJoin

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
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeRefl
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeRefl_matches_Term_refl
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdJ
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdJ_matches_Term_idJ
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqRefl
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqRefl_matches_Term_oeqRefl
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqJ
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeOeqJ_matches_Term_oeqJ
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRefl
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRefl_matches_Term_idStrictRefl
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRec
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIdStrictRec_matches_Term_idStrictRec
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEquivApp
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeEquivApp_matches_Term_equivApp
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModIntro
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModIntro_matches_Term_modIntro
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeModElim_matches_Term_modElim
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSubsume
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeSubsume_matches_Term_subsume
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval0
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval0_matches_Term_interval0
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval1
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeInterval1_matches_Term_interval1
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalOpp
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalOpp_matches_Term_intervalOpp
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalMeet
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalMeet_matches_Term_intervalMeet
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalJoin
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeIntervalJoin_matches_Term_intervalJoin

end LeanFX2.SmokeGeneratorOutputType
