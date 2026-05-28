import LeanFX2.Foundation.PolyCell.Core.CdLemma
import LeanFX2.Foundation.PolyCell.Core.StepBetaEtaPreservesShape

/-! # Foundation/PolyCell/Core/StepEtaCriticalPairs

First betaEta confluence interface for the raw eta cascade.

The current `Step.betaEta` relation is the sum of:

* the existing beta+iota `Step` relation, including its congruence rule;
* root-only `Step.eta`.

It does not yet add eta congruence under arbitrary generator children.
Consequently, classical examples such as reducing eta under an outer
application are not one-step branchings in the current formal relation.
This file therefore ships the honest foundation for M8f: the betaEta join
shape, closure embeddings from beta+iota `StepStar`, and the beta-only
fragment of the future betaEta local Church-Rosser theorem.
-/

namespace LeanFX2.Foundation.PolyCell.Core

namespace Step
namespace betaEtaStar

/-- Embed a beta+iota `StepStar` chain into the beta+iota+eta closure. -/
theorem ofStepStar {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : StepStar sourceTerm targetTerm) :
    Step.betaEtaStar sourceTerm targetTerm := by
  induction chain with
  | refl term =>
      exact Step.betaEtaStar.refl term
  | trans headStep _ tailIH =>
      exact Step.betaEtaStar.trans (Or.inl headStep) tailIH

/-- Embed an eta-only `etaStar` chain into the beta+iota+eta closure. -/
theorem ofEtaStar {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : Step.etaStar sourceTerm targetTerm) :
    Step.betaEtaStar sourceTerm targetTerm := by
  induction chain with
  | refl term =>
      exact Step.betaEtaStar.refl term
  | trans headStep _ tailIH =>
      exact Step.betaEtaStar.trans (Or.inr headStep) tailIH

end betaEtaStar
end Step

/-- The local join shape for two one-step beta+iota-or-eta reductions from
the same source. -/
def BetaEtaPairJoin {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (_leftStep : Step.betaEta sourceTerm leftReduct)
    (_rightStep : Step.betaEta sourceTerm rightReduct) : Prop :=
  ∃ commonReduct : RawTerm scope,
    Step.betaEtaStar leftReduct commonReduct ∧
      Step.betaEtaStar rightReduct commonReduct

/-- Future target statement for local Church-Rosser over the betaEta
one-step relation.  This is intentionally separate from `CdLemmaStatement`,
which remains the beta+iota-only theorem. -/
def CdLemmaStatementBetaEta : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    (leftStep : Step.betaEta sourceTerm leftReduct) →
    (rightStep : Step.betaEta sourceTerm rightReduct) →
    BetaEtaPairJoin leftStep rightStep

namespace BetaEtaPairJoin

/-- Same-reduct closure for betaEta local joins. -/
theorem ofReductsEqual {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step.betaEta sourceTerm leftReduct}
    {rightStep : Step.betaEta sourceTerm rightReduct}
    (reductsEqual : leftReduct = rightReduct) :
    BetaEtaPairJoin leftStep rightStep := by
  cases reductsEqual
  exact ⟨leftReduct, Step.betaEtaStar.refl _,
    Step.betaEtaStar.refl _⟩

/-- A betaEta step trivially joins with itself. -/
theorem sameStep {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (sameStepWitness : Step.betaEta sourceTerm targetTerm) :
    BetaEtaPairJoin sameStepWitness sameStepWitness :=
  ofReductsEqual rfl

/-- Reverse the two branches of a betaEta local join. -/
theorem swap {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step.betaEta sourceTerm leftReduct}
    {rightStep : Step.betaEta sourceTerm rightReduct} :
    BetaEtaPairJoin leftStep rightStep →
      BetaEtaPairJoin rightStep leftStep :=
  fun join =>
    Exists.elim join
      (fun commonReduct chains =>
        ⟨commonReduct, chains.2, chains.1⟩)

/-- Lift an existing beta+iota local join into the betaEta join shape. -/
theorem ofStepPairJoin {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct}
    (join : StepPairJoin leftStep rightStep) :
    BetaEtaPairJoin (Or.inl leftStep) (Or.inl rightStep) :=
  Exists.elim join
    (fun commonReduct chains =>
      ⟨ commonReduct
      , Step.betaEtaStar.ofStepStar chains.1
      , Step.betaEtaStar.ofStepStar chains.2 ⟩)

/-- The shipped beta+iota `cd_lemma` covers the beta-only fragment of the
future betaEta local Church-Rosser theorem. -/
theorem ofCdLemmaForStepSteps {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    BetaEtaPairJoin (Or.inl leftStep) (Or.inl rightStep) :=
  ofStepPairJoin (cd_lemma leftStep rightStep)

/-- Eta-pair versus a beta+iota step inside the first projected occurrence.

Source:
`pair (fst pairTerm) (snd pairTerm)`.

Left branch reduces the `pairTerm` under `fst`; right branch contracts
eta-pair at the root.  The join first reduces the remaining `pairTerm`
under `snd`, then contracts eta-pair for `updatedPairTerm`. -/
theorem etaPairFirstCong {scope : Nat}
    {pairTerm updatedPairTerm : RawTerm scope}
    (pairStep : Step pairTerm updatedPairTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pair ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.childCons
              (.mkGen .gen_snd ()
                (.childCons pairTerm .childNil))
              .childNil) : RawTermChildren [0] scope)
            (Step.cong .gen_fst ()
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                pairStep)))))
      (Or.inr (Step.eta.etaPair pairTerm)) := by
  exact
    ⟨ updatedPairTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_pair ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.mkGen .gen_fst ()
                (.childCons updatedPairTerm .childNil)) : RawTerm scope)
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                (Step.cong .gen_snd ()
                  (StepChildren.here
                    (parentScope := scope) (headShift := 0)
                    (restShifts := [])
                    (.childNil : RawTermChildren [] scope)
                    pairStep))))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaPair updatedPairTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl pairStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-pair versus a beta+iota step inside the second projected occurrence.

This is the symmetric sibling of `etaPairFirstCong`: the left branch
reduces under `snd`, while the join replays the same step under `fst`
before contracting eta-pair. -/
theorem etaPairSecondCong {scope : Nat}
    {pairTerm updatedPairTerm : RawTerm scope}
    (pairStep : Step pairTerm updatedPairTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pair ()
          (StepChildren.there
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.mkGen .gen_fst ()
              (.childCons pairTerm .childNil)) : RawTerm scope)
            (StepChildren.here
              (parentScope := scope) (headShift := 0)
              (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.cong .gen_snd ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  pairStep))))))
      (Or.inr (Step.eta.etaPair pairTerm)) := by
  exact
    ⟨ updatedPairTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_pair ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons
                (.mkGen .gen_snd ()
                  (.childCons updatedPairTerm .childNil))
                .childNil) : RawTermChildren [0] scope)
              (Step.cong .gen_fst ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  pairStep)))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaPair updatedPairTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl pairStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-modal-intro versus a beta+iota step inside the eliminated modal
occurrence.

Source:
`modIntro (modElim modalTerm)`.

The congruence branch reduces under `modElim`; the eta branch contracts
the source to `modalTerm`.  The join contracts eta for the updated modal
term on the congruence side and replays the original step on the eta side. -/
theorem etaModIntroCong {scope : Nat}
    {modalTerm updatedModalTerm : RawTerm scope}
    (modalStep : Step modalTerm updatedModalTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_modIntro ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_modElim ()
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                modalStep)))))
      (Or.inr (Step.eta.etaModIntro modalTerm)) := by
  exact
    ⟨ updatedModalTerm
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaModIntro updatedModalTerm))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl modalStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-Glue-intro versus a beta+iota step inside the eliminated Glue
occurrence.

Source:
`glueIntro (glueElim gluedTerm) gluedTerm`.

The left branch reduces the first occurrence under `glueElim`; the join
replays the same step at the second occurrence and then contracts eta for
the updated Glue term. -/
theorem etaGlueIntroFirstCong {scope : Nat}
    {gluedTerm updatedGluedTerm : RawTerm scope}
    (gluedStep : Step gluedTerm updatedGluedTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_glueIntro ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.childCons gluedTerm .childNil) :
              RawTermChildren [0] scope)
            (Step.cong .gen_glueElim ()
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                gluedStep)))))
      (Or.inr (Step.eta.etaGlueIntro gluedTerm)) := by
  exact
    ⟨ updatedGluedTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_glueIntro ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.mkGen .gen_glueElim ()
                (.childCons updatedGluedTerm .childNil)) : RawTerm scope)
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                gluedStep))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaGlueIntro updatedGluedTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl gluedStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-Glue-intro versus a beta+iota step inside the direct Glue
occurrence.

This is the symmetric sibling of `etaGlueIntroFirstCong`: the left branch
reduces the second occurrence, while the join replays the same step under
`glueElim` before contracting eta. -/
theorem etaGlueIntroSecondCong {scope : Nat}
    {gluedTerm updatedGluedTerm : RawTerm scope}
    (gluedStep : Step gluedTerm updatedGluedTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_glueIntro ()
          (StepChildren.there
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.mkGen .gen_glueElim ()
              (.childCons gluedTerm .childNil)) : RawTerm scope)
            (StepChildren.here
              (parentScope := scope) (headShift := 0)
              (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              gluedStep))))
      (Or.inr (Step.eta.etaGlueIntro gluedTerm)) := by
  exact
    ⟨ updatedGluedTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_glueIntro ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons updatedGluedTerm .childNil) :
                RawTermChildren [0] scope)
              (Step.cong .gen_glueElim ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  gluedStep)))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaGlueIntro updatedGluedTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl gluedStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-lambda versus a beta+iota step replayed through the weakened
function occurrence.

Source:
`lam (app (weaken innerFunction) newestVar)`.

When the inner function itself steps, the congruence branch replays that
step under weakening in the function slot of the eta source.  The join
contracts eta for the updated function on the congruence side and replays
the original function step on the eta side. -/
theorem etaLamFunctionCong {scope : Nat}
    {innerFunction updatedFunction : RawTerm scope}
    (functionStep : Step innerFunction updatedFunction) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_app ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                (Step.weaken functionStep))))))
      (Or.inr (Step.eta.etaLam innerFunction)) := by
  exact
    ⟨ updatedFunction
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaLam updatedFunction))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl functionStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-path-lambda versus a beta+iota step replayed through the weakened
path occurrence.

This is the cubical-path sibling of `etaLamFunctionCong`, using the
current raw `pathLam/pathApp` eta source. -/
theorem etaPathLamFunctionCong {scope : Nat}
    {innerPath updatedPath : RawTerm scope}
    (pathStep : Step innerPath updatedPath) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pathLam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_pathApp ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                (Step.weaken pathStep))))))
      (Or.inr (Step.eta.etaPathLam innerPath)) := by
  exact
    ⟨ updatedPath
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaPathLam updatedPath))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl pathStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-lambda versus an arbitrary under-binder function congruence step,
provided that the reduct strengthens back to a source-scope reduct.

This is the resolver-facing version of `etaLamFunctionCong`: it does not
assume the under-binder step was syntactically built by `Step.weaken`.
Instead, it consumes the exact strengthening evidence a future inversion
lemma must produce. -/
theorem etaLamStrengthenedFunctionCong {scope : Nat}
    {innerFunction : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    {updatedFunction : RawTerm scope}
    (underBinderStep :
      Step (RawTerm.weaken innerFunction) updatedUnderBinder)
    (strengthenSuccess :
      RawTerm.strengthen updatedUnderBinder = some updatedFunction)
    (functionStep : Step innerFunction updatedFunction) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_app ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                underBinderStep)))))
      (Or.inr (Step.eta.etaLam innerFunction)) := by
  have underBinderEq :
      updatedUnderBinder = RawTerm.weaken updatedFunction :=
    (RawTerm.strengthen_sound updatedUnderBinder updatedFunction
      strengthenSuccess).symm
  cases underBinderEq
  exact
    ⟨ updatedFunction
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaLam updatedFunction))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl functionStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-path-lambda sibling of `etaLamStrengthenedFunctionCong`.

The premise shape is the same: an arbitrary step under the weakened path
slot is accepted once strengthening identifies a source-scope reduct and
the source-level path step is supplied. -/
theorem etaPathLamStrengthenedFunctionCong {scope : Nat}
    {innerPath : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    {updatedPath : RawTerm scope}
    (underBinderStep :
      Step (RawTerm.weaken innerPath) updatedUnderBinder)
    (strengthenSuccess :
      RawTerm.strengthen updatedUnderBinder = some updatedPath)
    (pathStep : Step innerPath updatedPath) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pathLam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_pathApp ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                underBinderStep)))))
      (Or.inr (Step.eta.etaPathLam innerPath)) := by
  have underBinderEq :
      updatedUnderBinder = RawTerm.weaken updatedPath :=
    (RawTerm.strengthen_sound updatedUnderBinder updatedPath
      strengthenSuccess).symm
  cases underBinderEq
  exact
    ⟨ updatedPath
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaPathLam updatedPath))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl pathStep)
        (Step.betaEtaStar.refl _) ⟩

end BetaEtaPairJoin

/-- Current root eta kinds represented by `Step.eta`.

This finite catalog is deliberately limited to constructors whose generators
exist today.  Clock, parametricity, and record eta are future generator-table
work, not reserved cases here. -/
inductive EtaStepKind : Type where
  | etaLam
  | etaPair
  | etaPathLam
  | etaModIntro
  | etaGlueIntro
  deriving DecidableEq

namespace EtaStepKind

/-- Complete current eta-root catalog. -/
def all : List EtaStepKind :=
  [ .etaLam
  , .etaPair
  , .etaPathLam
  , .etaModIntro
  , .etaGlueIntro
  ]

/-- Source-head generator for a current root eta rule. -/
def sourceGenerator : EtaStepKind → Generator
  | .etaLam => .gen_lam
  | .etaPair => .gen_pair
  | .etaPathLam => .gen_pathLam
  | .etaModIntro => .gen_modIntro
  | .etaGlueIntro => .gen_glueIntro

/-- Does this eta root share beta's source-head generator? -/
def hasBetaSourceGenerator (etaKind : EtaStepKind) : Bool :=
  if etaKind.sourceGenerator = RootStepKind.beta.sourceGenerator then
    true
  else
    false

theorem all_length :
    all.length = 5 := rfl

theorem sourceGenerator_etaLam :
    sourceGenerator .etaLam = .gen_lam := rfl

theorem sourceGenerator_etaPair :
    sourceGenerator .etaPair = .gen_pair := rfl

theorem sourceGenerator_etaPathLam :
    sourceGenerator .etaPathLam = .gen_pathLam := rfl

theorem sourceGenerator_etaModIntro :
    sourceGenerator .etaModIntro = .gen_modIntro := rfl

theorem sourceGenerator_etaGlueIntro :
    sourceGenerator .etaGlueIntro = .gen_glueIntro := rfl

/-- Root beta has source generator `gen_app`, while every current root eta
rule has a different source generator.  Any beta/eta interaction in the
current relation therefore goes through `Step.cong` on the beta+iota side,
not through a same-root beta/eta overlap. -/
theorem currentEtaRoots_doNotShareBetaSource :
    all.map hasBetaSourceGenerator =
      [false, false, false, false, false] := rfl

end EtaStepKind

end LeanFX2.Foundation.PolyCell.Core
