import LeanFX2.Term.PreservesTerm.TierZeroAndUnary
import LeanFX2.Term.PreservesTerm.TierTwoBinary
import LeanFX2.Term.PreservesTerm.EliminatorConstantMotive
import LeanFX2.Term.PreservesTerm.EliminatorIdentityFamily
import LeanFX2.Term.PreservesTerm.EliminatorModalFamily
import LeanFX2.Term.PreservesTerm.EliminatorCubicalFamily
import LeanFX2.Term.PreservesTerm.InlineDestructors
import LeanFX2.Term.PreservesTerm.EliminatorShallowBeta
import LeanFX2.Term.PreservesTerm.BetaCastWallDemolition
import LeanFX2.Term.PreservesTerm.HeterogeneousElim
import LeanFX2.Term.PreservesTerm.SchematicValueCtors
import LeanFX2.Term.PreservesTerm.TypeCodeLifts
import LeanFX2.Term.PreservesTerm.TwoTyAtomsAndCong
import LeanFX2.Term.PreservesTerm.TwoTyEliminators

/-! # LeanFX2.Term.PreservesTerm — Term substitution preservation (shim)

Given a typed source `sourceTerm : Term context sourceType sourceRaw`
and a raw parallel step `RawStep.par sourceRaw targetRaw`, this module
constructs a typed target `targetTerm : Term context sourceType
targetRaw` together with a typed parallel step
`Step.par sourceTerm targetTerm`.

Carved into 11 sub-modules along the per-tier / per-ctor-family axis:

| Sub-module | Family |
| --- | --- |
| `TierZeroAndUnary` | Tier 0 atoms (unit/bool/nat/list/option/interval/var/universeCode); Tier 1 unary cong + binders (cumulUp/natSucc/optionSome/.../lam/lamPi/pathLam) |
| `TierTwoBinary` | Tier 2 binary cong + sessionRecv (intervalMeet/Join/glueIntro/hcomp/codataUnfold/sessionSend/listCons/equivApp/sessionRecv/refineIntro) |
| `EliminatorConstantMotive` | Tier 3 eliminators with fixed result type (natElim/natRec/listElim/optionMatch/eitherMatch/effectPerform) |
| `EliminatorCubicalFamily` | Cubical cong (hcompPath; pathLam/intervalOpp/pathApp/transp/glueElim/intervalMeet/intervalJoin/glueIntro/hcomp live in TierZeroAndUnary, EliminatorShallowBeta, TierTwoBinary) |
| `InlineDestructors` | Destructors for canonical Term values (modIntro/recordIntro/refineIntro/glueIntro/lam/codataUnfold) |
| `EliminatorShallowBeta` | Tier 3 single-child β-firing eliminators (transp/pathApp/appPi/app cong-only; modElim/recordProj/refineElim/glueElim/codataDest full) |
| `BetaCastWallDemolition` | Full lifts via two-Ty existential (app/pathApp) plus pathLamDestruct/reflDestruct/idReflDestruct |
| `HeterogeneousElim` | Σ-type fst/snd; identity elimination (idJ/oeqJ/idStrictRec); type-changing boolElim |
| `SchematicValueCtors` | Schematic-payload value ctors (oeqRefl/idStrictRefl/refl/equivReflId/equivReflIdAtId/uaIntroHet/equivIntroHet/oeqFunext + deferred funext stubs) |
| `TypeCodeLifts` | Schematic-payload type-code ctors (arrowCode/piTyCode/sigmaTyCode/productCode/sumCode/listCode/optionCode/eitherCode/idCode/equivCode) |
| `TwoTyAtomsAndCong` | Tier 0/1/2 lifts re-expressed at two-Ty existential |
| `TwoTyEliminators` | Tier 3 eliminator lifts re-expressed at two-Ty existential + project-wide coverage status |

## Root status

Zero-axiom; this shim file has no theorem bodies — every shipped
declaration lives in one of the sub-modules above. -/
