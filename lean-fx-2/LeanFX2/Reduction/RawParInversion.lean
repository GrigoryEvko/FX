import LeanFX2.Reduction.RawParInversion.AtomicCtors
import LeanFX2.Reduction.RawParInversion.ModalAndAdvanced
import LeanFX2.Reduction.RawParInversion.CubicalAndIdentity
import LeanFX2.Reduction.RawParInversion.RedexParents
import LeanFX2.Reduction.RawParInversion.TypeCodes

/-! # LeanFX2.Reduction.RawParInversion — `RawStep.par` inversion (shim)

For each `RawTerm` constructor `C`, the lemma `RawStep.par.C_inv`
states: when `RawStep.par (C args) target`, `target` has the same
shape `C args'` with appropriate parallel-step relations on the
sub-terms (or `target = C args` for nullary canonical ctors).

These work because `RawStep.par` is indexed only by `scope : Nat`
(no Ty indices), so Lean's `cases` tactic decomposes the inductive
without dependent-elimination conflicts.  Per
`feedback_lean_match_arity_axioms.md`, single-Nat-indexed inductives
do NOT trigger propext+Quot.sound on `cases`.

These are exactly what `RawStep.par.cd_lemma`'s deep cases need:
from "subterm reduces to canonical via the IH" we recover the
canonical structure of the IH's target, allowing the deep-rule's
contraction shape to be matched.

Carved into 5 sub-modules along the RawTerm-ctor family axis:

| Sub-module | Family |
| --- | --- |
| `AtomicCtors` | lam, var, pair, refl, unit, bool/nat/list/option/either intro |
| `ModalAndAdvanced` | modIntro/modElim/subsume/cumulUpMarker, refineIntro/refineElim, recordIntro/recordProj, codataUnfold/codataDest, sessionSend/sessionRecv, effectPerform |
| `CubicalAndIdentity` | interval{0,1,Opp,Meet,Join}, pathLam/pathApp, uaToEquiv, pathCompose, idToEquiv, oeqTrans, equivCompose, glueIntro/glueElim, transp, hcomp, oeqRefl/oeqJ/oeqFunext, idStrictRefl/idStrictRec, equivIntro/equivApp |
| `RedexParents` | app/fst/snd, boolElim/natElim/natRec, listElim/optionMatch/eitherMatch, idJ |
| `TypeCodes` | arrowCode/piTyCode/sigmaTyCode/productCode/sumCode/listCode/optionCode/eitherCode/idCode/equivCode, equivApply, universeCode |

## Root status

Layer 2 raw-reduction aggregator.  Kernel `theorem`s with bodies, zero-axiom. -/
