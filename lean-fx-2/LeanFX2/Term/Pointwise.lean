import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure
import LeanFX2.Term.Pointwise.IdentitySubst
import LeanFX2.Term.Pointwise.VariableAndIntroArms
import LeanFX2.Term.Pointwise.ApplicationAndSigmaArms
import LeanFX2.Term.Pointwise.EliminatorArms
import LeanFX2.Term.Pointwise.IdentityAndUniverseCodeArms
import LeanFX2.Term.Pointwise.CubicalAndStructuralArms
import LeanFX2.Term.Pointwise.EffectAndHoTTHetArms

/-! # LeanFX2.Term.Pointwise — Term pointwise congruence (shim)

Carved into 8 sub-modules along the constructor-family axis.  Each
sub-module ships a coherent group of weaken-subst-singleton arms (plus,
in slice 1, the shared pointwise/composition infrastructure that every
arm consumes).

| Sub-module | Family |
| --- | --- |
| `PointwiseAndCompositionInfrastructure` | TermSubst pointwise equality + composition + cast HEq + consSingleton |
| `IdentitySubst` | typed identity-substitution erasure helpers |
| `VariableAndIntroArms` | var, unit, lambdas, booleans, nats zero/succ, list nil/cons, option none/some, eithers, intervals + ops, path lambda, modal intro/elim/subsume |
| `ApplicationAndSigmaArms` | app, appPi, pair, fst, snd |
| `EliminatorArms` | boolElim, natElim, natRec, listElim, optionMatch, eitherMatch |
| `IdentityAndUniverseCodeArms` | refl, idJ, oeq*, idStrict*, universe codes, equivReflId(AtId) |
| `CubicalAndStructuralArms` | funextRefl(AtId), glueIntro, transp, hcomp, recordIntro, refine*, codataUnfold, sessionSend/Recv |
| `EffectAndHoTTHetArms` | effectPerform (incl. carrier-congruence helpers), uaToEquiv, pathApp, glueElim, recordProj, codataDest, equivIntroHet, equivApp/Apply, uaIntroHet, funextIntroHet, cumulUp |

## Root status

Kernel — shim re-exporting the eight Pointwise sub-modules. -/
