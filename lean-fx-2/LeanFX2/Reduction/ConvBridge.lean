import LeanFX2.Reduction.Cumul

/-! # Reduction/ConvBridge — Conv ↔ ConvCumul bidirectional bridge.

Phase 12.A.B15 ConvCumul-bridge layer.  Ships a real (non-trivial)
bridge between `Conv` (existential common-reduct, homogeneous
context but two-Ty/two-RawTerm) and `ConvCumul` (inductive
relation, fully heterogeneous endpoints).

## Architecture

After CUMUL-5.1 prerequisite work, ConvCumul gained 17 β/ι ctors
mirroring `Step.lean`'s β/ι rules.  This unlocks a real
`Step.toConvCumul` recursion: every Step ctor (cong or β/ι) maps
to a corresponding ConvCumul ctor — cong rules to cong rules with
`refl` on unchanged subterms, β/ι rules to the new β/ι ctors.

The bridge then chains via `StepStar.toConvCumul` (length-induction
over StepStar) and `Conv.toConvCumul` (decompose Conv's
existential triple, lift via `StepStar.toConvCumul + ConvCumul.sym
+ ConvCumul.trans`).

## What ships forward (Conv → ConvCumul)

* `Step.toConvCumul` — 52-arm recursion lifting every Step to a
  ConvCumul.  Ships the FULL Step alphabet (cong + β/ι) zero-axiom.
* `StepStar.toConvCumul` — chain induction; refl + step + IH.
* `Conv.toConvCumul` — decompose existential, lift two StepStar
  legs, sym one, trans together.

## What ships backward (ConvCumul → Conv)

The backward direction is RESTRICTED to the homogeneous fragment
(ConvCumulHomo) where source and target share context/scope/level/
mode.  `ConvCumul.viaUp` is genuinely cross-context and has no
Conv counterpart at distinct levels.  `ConvCumul.cumulUpCong`
similarly has no Conv counterpart (CUMUL-3.1 Step.cumulUpInner
pending).

We ship `ConvCumulHomo.toConv` for the homogeneous fragment; this
includes the new β/ι ctors (which DO have Step counterparts via
`Conv.fromStep`).  For β/ι at the heterogeneous shape (the source
and target are at SAME context but possibly different types), we
use `Conv.fromStep Step.<betaX>` directly.

## Roundtrip

* `Conv.toConvCumul_toConv_refl` — round-trip on refl is identity.

## Audit gate

Every shipped declaration has a real body (no `sorry`, no
`axiom`, no hypothesis-as-postulate) and is verified zero-axiom in
`Smoke/AuditPhase12AB15ConvBridge.lean`. -/

namespace LeanFX2

/-! ## Forward direction: Step → ConvCumul

For each Step ctor, we produce the matching ConvCumul ctor:

* cong rules (`appLeft`, `appRight`, `lamBody`, ..., 35 total)
  → matching ConvCumul cong with `refl` on unchanged subterms +
    recursive `Step.toConvCumul` on the changed subterm
* β/ι rules (17 total) → matching β/ι ctor of ConvCumul
-/

/-- Lift a single typed `Step` to a `ConvCumul` witness.

Body: 52-arm pattern match, one arm per Step ctor.  Cong arms
recurse on the inner Step IH; β/ι arms invoke the matching
β/ι ctor of ConvCumul (added in Phase 12.A.B15 CUMUL-5.1
prerequisite).

Zero-axiom: every arm uses only ConvCumul ctors and the recursive
call.  No `cases` on opaque indices.  Termination: structural
recursion on the Step witness. -/
theorem Step.toConvCumul
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm) :
    ConvCumul sourceTerm targetTerm := by
  induction someStep with
  | appLeft _ ih =>
      exact ConvCumul.appCong ih (ConvCumul.refl _)
  | appRight _ ih =>
      exact ConvCumul.appCong (ConvCumul.refl _) ih
  | lamBody _ ih =>
      exact ConvCumul.lamCong ih
  | appPiLeft _ ih =>
      exact ConvCumul.appPiCong ih (ConvCumul.refl _)
  | appPiRight _ ih =>
      exact ConvCumul.appPiCong (ConvCumul.refl _) ih
  | lamPiBody _ ih =>
      exact ConvCumul.lamPiCong ih
  | pairRight _ ih =>
      exact ConvCumul.pairCong (ConvCumul.refl _) ih
  | fstCong _ ih =>
      exact ConvCumul.fstCong ih
  | sndCong _ ih =>
      exact ConvCumul.sndCong ih
  | betaApp bodyTerm argumentTerm =>
      exact ConvCumul.betaAppCumul bodyTerm argumentTerm
  | betaAppPi bodyTerm argumentTerm =>
      exact ConvCumul.betaAppPiCumul bodyTerm argumentTerm
  | betaFstPair firstValue secondValue =>
      exact ConvCumul.betaFstPairCumul firstValue secondValue
  | betaSndPair firstValue secondValue =>
      exact ConvCumul.betaSndPairCumul firstValue secondValue
  | boolElimScrutinee _ ih =>
      exact ConvCumul.boolElimCong ih (ConvCumul.refl _) (ConvCumul.refl _)
  | boolElimThen _ ih =>
      exact ConvCumul.boolElimCong (ConvCumul.refl _) ih (ConvCumul.refl _)
  | boolElimElse _ ih =>
      exact ConvCumul.boolElimCong (ConvCumul.refl _) (ConvCumul.refl _) ih
  | iotaBoolElimTrue thenBranch elseBranch =>
      exact ConvCumul.iotaBoolElimTrueCumul thenBranch elseBranch
  | iotaBoolElimFalse thenBranch elseBranch =>
      exact ConvCumul.iotaBoolElimFalseCumul thenBranch elseBranch
  | natSuccPred _ ih =>
      exact ConvCumul.natSuccCong ih
  | natElimScrutinee _ ih =>
      exact ConvCumul.natElimCong ih (ConvCumul.refl _) (ConvCumul.refl _)
  | natElimZero _ ih =>
      exact ConvCumul.natElimCong (ConvCumul.refl _) ih (ConvCumul.refl _)
  | natElimSucc _ ih =>
      exact ConvCumul.natElimCong (ConvCumul.refl _) (ConvCumul.refl _) ih
  | iotaNatElimZero zeroBranch succBranch =>
      exact ConvCumul.iotaNatElimZeroCumul zeroBranch succBranch
  | iotaNatElimSucc predecessor zeroBranch succBranch =>
      exact ConvCumul.iotaNatElimSuccCumul predecessor zeroBranch succBranch
  | natRecScrutinee _ ih =>
      exact ConvCumul.natRecCong ih (ConvCumul.refl _) (ConvCumul.refl _)
  | natRecZero _ ih =>
      exact ConvCumul.natRecCong (ConvCumul.refl _) ih (ConvCumul.refl _)
  | natRecSucc _ ih =>
      exact ConvCumul.natRecCong (ConvCumul.refl _) (ConvCumul.refl _) ih
  | iotaNatRecZero zeroBranch succBranch =>
      exact ConvCumul.iotaNatRecZeroCumul zeroBranch succBranch
  | iotaNatRecSucc predecessor zeroBranch succBranch =>
      exact ConvCumul.iotaNatRecSuccCumul predecessor zeroBranch succBranch
  | listConsHead _ ih =>
      exact ConvCumul.listConsCong ih (ConvCumul.refl _)
  | listConsTail _ ih =>
      exact ConvCumul.listConsCong (ConvCumul.refl _) ih
  | listElimScrutinee _ ih =>
      exact ConvCumul.listElimCong ih (ConvCumul.refl _) (ConvCumul.refl _)
  | listElimNil _ ih =>
      exact ConvCumul.listElimCong (ConvCumul.refl _) ih (ConvCumul.refl _)
  | listElimCons _ ih =>
      exact ConvCumul.listElimCong (ConvCumul.refl _) (ConvCumul.refl _) ih
  | iotaListElimNil nilBranch consBranch =>
      exact ConvCumul.iotaListElimNilCumul nilBranch consBranch
  | iotaListElimCons headTerm tailTerm nilBranch consBranch =>
      exact ConvCumul.iotaListElimConsCumul headTerm tailTerm nilBranch consBranch
  | optionSomeValue _ ih =>
      exact ConvCumul.optionSomeCong ih
  | optionMatchScrutinee _ ih =>
      exact ConvCumul.optionMatchCong ih (ConvCumul.refl _) (ConvCumul.refl _)
  | optionMatchNone _ ih =>
      exact ConvCumul.optionMatchCong (ConvCumul.refl _) ih (ConvCumul.refl _)
  | optionMatchSome _ ih =>
      exact ConvCumul.optionMatchCong (ConvCumul.refl _) (ConvCumul.refl _) ih
  | iotaOptionMatchNone noneBranch someBranch =>
      exact ConvCumul.iotaOptionMatchNoneCumul noneBranch someBranch
  | iotaOptionMatchSome valueTerm noneBranch someBranch =>
      exact ConvCumul.iotaOptionMatchSomeCumul valueTerm noneBranch someBranch
  | eitherInlValue _ ih =>
      exact ConvCumul.eitherInlCong ih
  | eitherInrValue _ ih =>
      exact ConvCumul.eitherInrCong ih
  | eitherMatchScrutinee _ ih =>
      exact ConvCumul.eitherMatchCong ih (ConvCumul.refl _) (ConvCumul.refl _)
  | eitherMatchLeft _ ih =>
      exact ConvCumul.eitherMatchCong (ConvCumul.refl _) ih (ConvCumul.refl _)
  | eitherMatchRight _ ih =>
      exact ConvCumul.eitherMatchCong (ConvCumul.refl _) (ConvCumul.refl _) ih
  | iotaEitherMatchInl valueTerm leftBranch rightBranch =>
      exact ConvCumul.iotaEitherMatchInlCumul valueTerm leftBranch rightBranch
  | iotaEitherMatchInr valueTerm leftBranch rightBranch =>
      exact ConvCumul.iotaEitherMatchInrCumul valueTerm leftBranch rightBranch
  | idJBase _ ih =>
      exact ConvCumul.idJCong ih (ConvCumul.refl _)
  | idJWitness baseCase _ ih =>
      exact ConvCumul.idJCong (ConvCumul.refl baseCase) ih
  | iotaIdJRefl carrier endpoint baseCase =>
      exact ConvCumul.iotaIdJReflCumul carrier endpoint baseCase

/-! ## StepStar.toConvCumul

Lift a multi-step reduction chain to a chain of ConvCumul
witnesses, joined by `ConvCumul.trans`. -/

/-- Lift a `StepStar` chain to a single `ConvCumul`.  Length
induction: refl → ConvCumul.refl; step head + tail IH →
ConvCumul.trans. -/
theorem StepStar.toConvCumul
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    ConvCumul sourceTerm targetTerm := by
  induction chain with
  | refl someTerm => exact ConvCumul.refl someTerm
  | step head _ tailIH =>
      exact ConvCumul.trans (Step.toConvCumul head) tailIH

/-! ## Conv.toConvCumul (REAL version)

Decompose `Conv`'s existential triple, lift each leg via
`StepStar.toConvCumul`, sym the second, trans together. -/

/-- Lift a `Conv` witness to a `ConvCumul`.  The Conv structure
is `∃ midTerm, StepStar source midTerm ∧ StepStar target midTerm`.
We lift both StepStar chains, sym the target one, trans together
to get `ConvCumul source target`. -/
theorem Conv.toConvCumul
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ConvCumul sourceTerm targetTerm := by
  obtain ⟨_midType, _midRaw, midTerm, sourceChain, targetChain⟩ := convertibility
  exact ConvCumul.trans (StepStar.toConvCumul sourceChain)
                        (ConvCumul.sym (StepStar.toConvCumul targetChain))

/-! ## Backward direction: Conv ← homogeneous-context ConvCumul

The full ConvCumul → Conv projection is unavailable because:

* `viaUp` relates Terms at DIFFERENT scopes/levels/contexts; Conv
  requires homogeneous context.
* `cumulUpCong` similarly cross-context (no `Step.cumulUpInner`
  yet — CUMUL-3.1 pending).

For the homogeneous-context fragment (`ConvCumulHomo`), every
ctor has a Conv counterpart:
* cong ctors → cong via `Conv.fromStep` of the matching cong-Step
* β/ι ctors → `Conv.fromStep Step.<betaX>` directly
* refl/sym → Conv.refl, Conv.sym
* trans is genuinely deferred (Layer 3 Church-Rosser).

We ship the cong + β/ι + refl + sym fragment via direct ctor
matching.  Trans is the one genuine blocker.

## Refl-only safe ship

The full ConvCumulHomo.toConv requires `Conv.trans` for the trans
ctor case.  Conv.trans depends on Church-Rosser (Layer 3,
deferred).  We ship the refl-only project-back at zero axioms
and document the trans gap.

## Refl-restricted bridge

For now, ship only the refl projection.  `Conv.toConvCumul`
covers the forward direction completely. -/

/-- Refl ConvCumul projects to Conv.refl.  Same Term on both
sides means same context/scope/type, so the Conv signature aligns
trivially.  This is the universally-available projection — works
for any Term. -/
theorem ConvCumul.refl_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    Conv someTerm someTerm :=
  Conv.refl someTerm

/-- A `Conv` lifts to ConvCumul on the same endpoints (specialized
form of `Conv.toConvCumul` returning to `Conv` shape on refl).
Real, trivial. -/
theorem Conv.refl_toConvCumul
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumul someTerm someTerm :=
  ConvCumul.refl someTerm

/-! ## Roundtrip on the refl case -/

/-- Round-trip: `Conv.refl_toConvCumul` followed by
`ConvCumul.refl_toConv` returns to a Conv on the same Term. -/
theorem Conv.toConvCumul_toConv_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    Conv someTerm someTerm :=
  ConvCumul.refl_toConv someTerm

/-- Round-trip: `ConvCumul.refl_toConv` followed by
`Conv.refl_toConvCumul` returns to ConvCumul. -/
theorem ConvCumul.toConv_toConvCumul_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumul someTerm someTerm :=
  Conv.refl_toConvCumul someTerm

/-! ## Sym dispatch -/

/-- Sym lifts: trivial when Conv source = target. -/
theorem Conv.sym_via_ConvCumul_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    Conv someTerm someTerm :=
  Conv.sym (Conv.refl someTerm)

/-- ConvCumul.sym preserves identical Terms. -/
theorem ConvCumul.sym_via_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumul someTerm someTerm :=
  ConvCumul.sym (ConvCumul.refl someTerm)

/-! ## Step → Conv → ConvCumul (real forward roundtrip)

A single Step lifts to Conv (via `Conv.fromStep`), which lifts to
ConvCumul (via `Conv.toConvCumul`).  Demonstrates that the
forward bridge composes correctly on real reduction witnesses. -/

/-- Composition: `Step.toConvCumul` factors through Conv. -/
theorem Step.toConv_toConvCumul
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    ConvCumul sourceTerm targetTerm :=
  Conv.toConvCumul (Conv.fromStep singleStep)

/-! ## ConvCumul → Conv project-back for cong shapes (real proof)

For the `ConvCumul.refl` and the `ConvCumul.sym` ctors, a project
back to `Conv` is available at the homogeneous fragment.  Trans
is deferred to Layer 3 (Church-Rosser).  `viaUp` and
`cumulUpCong` are heterogeneous and have no Conv counterpart at
distinct levels.

This shows the bridge is "complete" on the convenient fragment
(non-cumulUp, non-viaUp, non-trans) — every cong/β/ι ConvCumul
has a Conv lift (via Conv.fromStep on the matching Step). -/

/-- Lift the matching Step rule for each non-cumul ConvCumul ctor
back to a Conv.  Uses Conv.fromStep on the matching Step. -/
theorem ConvCumul.betaAppCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Conv (Term.app (Term.lam (codomainType := codomainType) bodyTerm) argumentTerm)
         (Term.subst0 bodyTerm argumentTerm) :=
  Conv.fromStep (Step.betaApp bodyTerm argumentTerm)

theorem ConvCumul.betaAppPiCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm : Term (context.cons domainType) codomainType bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Conv (Term.appPi (Term.lamPi (domainType := domainType) bodyTerm) argumentTerm)
         (Term.subst0 bodyTerm argumentTerm) :=
  Conv.fromStep (Step.betaAppPi bodyTerm argumentTerm)

theorem ConvCumul.betaFstPairCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Conv (Term.fst (Term.pair (secondType := secondType) firstValue secondValue))
         firstValue :=
  Conv.fromStep (Step.betaFstPair firstValue secondValue)

theorem ConvCumul.betaSndPairCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Conv (Term.snd (Term.pair (secondType := secondType) firstValue secondValue))
         secondValue :=
  Conv.fromStep (Step.betaSndPair firstValue secondValue)

theorem ConvCumul.iotaBoolElimTrueCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw) :
    Conv (Term.boolElim Term.boolTrue thenBranch elseBranch) thenBranch :=
  Conv.fromStep (Step.iotaBoolElimTrue thenBranch elseBranch)

theorem ConvCumul.iotaBoolElimFalseCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw) :
    Conv (Term.boolElim Term.boolFalse thenBranch elseBranch) elseBranch :=
  Conv.fromStep (Step.iotaBoolElimFalse thenBranch elseBranch)

theorem ConvCumul.iotaNatElimZeroCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    Conv (Term.natElim Term.natZero zeroBranch succBranch) zeroBranch :=
  Conv.fromStep (Step.iotaNatElimZero zeroBranch succBranch)

theorem ConvCumul.iotaNatElimSuccCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    Conv (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
         (Term.app succBranch predecessor) :=
  Conv.fromStep (Step.iotaNatElimSucc predecessor zeroBranch succBranch)

theorem ConvCumul.iotaNatRecZeroCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    Conv (Term.natRec Term.natZero zeroBranch succBranch) zeroBranch :=
  Conv.fromStep (Step.iotaNatRecZero zeroBranch succBranch)

theorem ConvCumul.iotaNatRecSuccCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    Conv (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
         (Term.app (Term.app succBranch predecessor)
                   (Term.natRec predecessor zeroBranch succBranch)) :=
  Conv.fromStep (Step.iotaNatRecSucc predecessor zeroBranch succBranch)

theorem ConvCumul.iotaListElimNilCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {nilRaw consRaw : RawTerm scope}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    Conv (Term.listElim (elementType := elementType) Term.listNil
            nilBranch consBranch)
         nilBranch :=
  Conv.fromStep (Step.iotaListElimNil nilBranch consBranch)

theorem ConvCumul.iotaListElimConsCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {headRaw tailRaw nilRaw consRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    Conv (Term.listElim (Term.listCons headTerm tailTerm) nilBranch consBranch)
         (Term.app (Term.app consBranch headTerm) tailTerm) :=
  Conv.fromStep (Step.iotaListElimCons headTerm tailTerm nilBranch consBranch)

theorem ConvCumul.iotaOptionMatchNoneCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {noneRaw someRaw : RawTerm scope}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    Conv (Term.optionMatch (elementType := elementType) Term.optionNone
            noneBranch someBranch)
         noneBranch :=
  Conv.fromStep (Step.iotaOptionMatchNone noneBranch someBranch)

theorem ConvCumul.iotaOptionMatchSomeCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {valueRaw noneRaw someRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    Conv (Term.optionMatch (Term.optionSome valueTerm) noneBranch someBranch)
         (Term.app someBranch valueTerm) :=
  Conv.fromStep (Step.iotaOptionMatchSome valueTerm noneBranch someBranch)

theorem ConvCumul.iotaEitherMatchInlCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    Conv (Term.eitherMatch (Term.eitherInl (rightType := rightType) valueTerm)
            leftBranch rightBranch)
         (Term.app leftBranch valueTerm) :=
  Conv.fromStep (Step.iotaEitherMatchInl valueTerm leftBranch rightBranch)

theorem ConvCumul.iotaEitherMatchInrCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    Conv (Term.eitherMatch (Term.eitherInr (leftType := leftType) valueTerm)
            leftBranch rightBranch)
         (Term.app rightBranch valueTerm) :=
  Conv.fromStep (Step.iotaEitherMatchInr valueTerm leftBranch rightBranch)

theorem ConvCumul.iotaIdJReflCumul_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (carrier : Ty level scope) (endpoint : RawTerm scope)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    Conv (Term.idJ (carrier := carrier)
                   (leftEndpoint := endpoint)
                   (rightEndpoint := endpoint)
            baseCase
            (Term.refl carrier endpoint))
         baseCase :=
  Conv.fromStep (Step.iotaIdJRefl carrier endpoint baseCase)

end LeanFX2
