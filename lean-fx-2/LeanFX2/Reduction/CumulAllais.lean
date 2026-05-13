import LeanFX2.Reduction.CumulAllais.EnvRelation
import LeanFX2.Reduction.CumulAllais.ClosedArms
import LeanFX2.Reduction.CumulAllais.TypeCodeArms
import LeanFX2.Reduction.CumulAllais.DataIntroArms
import LeanFX2.Reduction.CumulAllais.PathArms
import LeanFX2.Reduction.CumulAllais.RecordSessionArms
import LeanFX2.Reduction.CumulAllais.MultiSubtermArms
import LeanFX2.Reduction.CumulAllais.CumulPromotionArms
import LeanFX2.Reduction.CumulAllais.EliminatorArms

/-! # Reduction/CumulAllais — Pattern 3 per-Term-ctor subst arms (Allais ICFP'18) (shim)

Per-Term-ctor `Term.substHet` arms for the Allais et al. ICFP'18
paired-environment simulation framework.  Each arm discharges one
ctor's obligation in the Allais `Simulation.alg` discipline: given
pointwise compat between two `TermSubstHet`s at the same
`SubstHet sigma`, lift to ConvCumul on the substituted source Term
ctor.

## Reference

Allais, Atkey, Chapman, McBride, McKinna, *A Type and Scope Safe
Universe of Syntaxes with Binding*, ICFP 2018 / JFP 2021
(arxiv:1804.00119).  See `Generic/Simulation.agda` in
`gallais/generic-syntax`; FX memory
`reference_pattern_allais_simulation`.

## Carving

This file is now a re-export shim.  The previous 1903-line module
has been carved into nine semantic sub-modules:

| Sub-module           | Family                                      |
| -------------------- | ------------------------------------------- |
| EnvRelation          | PointwiseCompat predicate + refl/sym/trans  |
| ClosedArms           | unit / boolTrue / boolFalse / natZero / var / universeCode / equivReflId / funextRefl / equivReflIdAtId / funextReflAtId / funextIntroHet |
| TypeCodeArms         | CUMUL-2.4 typed type-code constructors (arrowCode, piTyCode, sigmaTyCode, productCode, sumCode, listCode, optionCode, eitherCode, idCode, equivCode) |
| DataIntroArms        | equivIntroHet / equivApp / uaIntroHet / uaToEquiv / equivApply / natSucc / optionSome / eitherInl / eitherInr / modIntro / modElim / subsume |
| PathArms             | Cubical path-fragment: interval0/1 / intervalOpp/Meet/Join / pathLam / pathApp / glueIntro / glueElim / transp / hcomp |
| RecordSessionArms    | recordIntro / recordProj / refineIntro / refineElim / codataUnfold / codataDest / sessionSend / sessionRecv / effectPerform |
| MultiSubtermArms     | listNil / optionNone / refl / fst / snd / app / appPi / pair / listCons / idJ / oeqRefl / oeqJ / oeqFunext / idStrictRefl / idStrictRec / boolElim |
| CumulPromotionArms   | cumulUp + lam / lamPi binder arms           |
| EliminatorArms       | natElim / natRec / listElim / optionMatch / eitherMatch |

The recursive HEADLINE that glues these arms via Term-induction
lives in `Reduction/CumulPairedEnv.lean` (the fundamental lemma
`Term.subst_compatible_pointwise_allais`).  This file is the
catalogue.

## Shared cast-elim primitives

The `pair` / `snd` / `appPi` / `lam` / `lamPi` / `boolElim` /
`oeqFunext` arms use `ConvCumul.cast_eq_both_benton` to peel
`Ty.X_substHet_commute` casts.  Source:
`Reduction/CumulCastElim.lean`.

## Audit

All shipped arms verified zero-axiom under strict policy in
`Smoke/AuditCumulSubstCompat.lean`.

## Root status

Layer 3 reduction aggregator. -/
