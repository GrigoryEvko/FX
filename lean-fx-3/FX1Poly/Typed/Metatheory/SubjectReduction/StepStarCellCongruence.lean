import FX1Poly.Core.Rewriting.Reduction.Step.StepStar
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst0ArgumentStar
import FX1Poly.Core.Rewriting.Reduction.Step.StepRename
import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair
import FX1Poly.Axis.Term.Rename.RenameDefs
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeForwardClosure
import FX1Poly.Typed.Cell.CellConstructors

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/StepStarCellCongruence
    — DIRECTED (`StepStar`) congruence helpers for SR-DSL-2's `templateStepStarUnderChildStep`

The SR-DSL-2 type-SR keystone reduces "the drifted branch classifier is still a well-formed type" to
"the classifier reduces (`StepStar`) when one child steps" + `UnionClassifierIsType.preservedUnderStepStar`
(universe rigidity).  The directed multi-step interpretation congruence `templateStepStarUnderChildStep`
(the mirror of SR-DSL-1's `templateConvUnderChildStep`, but `Conv` ↝ `StepStar`) assembles, per `interpret?`
arm, exactly these congruences — the DIRECTED twins of `Conv.subst0` / `Conv.substPair` / `Conv.piTyCode_cong`
and the depth-graded weakening lifters.  This file ships those reusable directed congruences on top of the
existing `StepStar.{subst,weaken,rename,subst0Body,subst0Argument,ofChildrenStar}` + `StepChildrenStar.{here,
there,trans_compose}` + `RawTerm.subst_pointwise_stepStar` substrate.

Every helper is the literal directed analog of the `Conv.*` helper SR-DSL-1 used: `Conv := StepStar.Join` joins
two `StepStar` legs, so a `Conv` congruence is just the same construction applied to BOTH legs — here we keep the
ONE directed leg.

## Zero-axiom

Compositions of the shipped zero-axiom `StepStar.*` / `StepChildrenStar.*` congruences over structural `Nat`
recursion.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-decl
audit-gated. -/

namespace FX1Poly.Core

open FX1Poly.Core FX1Poly.Axis.Syntax

/-- `StepStar` through `subst0` in BOTH the body and the argument: step the body (argument fixed at the start),
then step the argument (body fixed at the target), composed.  The directed twin of `Conv.subst0`. -/
theorem StepStar.subst0Both {scope : Nat} {bodyStart bodyTarget : RawTerm (scope + 1)}
    {argStart argTarget : RawTerm scope}
    (bodyChain : StepStar bodyStart bodyTarget) (argChain : StepStar argStart argTarget) :
    StepStar (RawTerm.subst0 bodyStart argStart) (RawTerm.subst0 bodyTarget argTarget) :=
  StepStar.trans_compose
    (StepStar.subst0Body argStart bodyChain)
    (StepStar.subst0Argument bodyTarget argChain)

/-- `StepStar` through `substPair` in the body and BOTH pair arguments: step the body across the (start) pair
substitution, then step the two pair components with the body fixed at the target.  The directed twin of
`Conv.substPair` — same construction, one leg.  Uses `RawTerm.subst_pointwise_stepStar` over
`RawTermSubst.pair_pointwise_stepStar`. -/
theorem StepStar.substPairAll {scope : Nat} {bodyStart bodyTarget : RawTerm (scope + 2)}
    {innerStart innerTarget outerStart outerTarget : RawTerm scope}
    (bodyChain : StepStar bodyStart bodyTarget)
    (innerChain : StepStar innerStart innerTarget)
    (outerChain : StepStar outerStart outerTarget) :
    StepStar (RawTerm.substPair bodyStart innerStart outerStart)
             (RawTerm.substPair bodyTarget innerTarget outerTarget) :=
  StepStar.trans_compose
    (StepStar.subst (RawTermSubst.pair innerStart outerStart) bodyChain)
    (RawTerm.subst_pointwise_stepStar
      (RawTermSubst.pair_pointwise_stepStar innerChain outerChain) bodyTarget)

/-- `RawTerm.weakenBy depth` preserves `StepStar` — iterated `StepStar.weaken` over the depth.  The directed twin
of `Conv.weakenByConv` (used by the `childAt` / `universeCode` / `listConsBranchType`-macro arms). -/
theorem StepStar.weakenByStar {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (chain : StepStar leftTerm rightTerm) :
    (depth : Nat) → StepStar (RawTerm.weakenBy depth leftTerm) (RawTerm.weakenBy depth rightTerm)
  | 0 => chain
  | depth + 1 => StepStar.weaken (StepStar.weakenByStar chain depth)

/-- `RawTerm.weakenBodyUnderOneBinderBy depth` preserves `StepStar` — iterated `StepStar.rename (lift weaken)`.
The directed twin of `Conv.weakenBodyUnderOneBinderByConv` (the `childBodyAt` / `+1`-macro arms). -/
theorem StepStar.weakenBodyUnderOneBinderByStar {scope : Nat} {leftBody rightBody : RawTerm (scope + 1)}
    (chain : StepStar leftBody rightBody) :
    (depth : Nat) →
    StepStar (RawTerm.weakenBodyUnderOneBinderBy depth leftBody)
             (RawTerm.weakenBodyUnderOneBinderBy depth rightBody)
  | 0 => chain
  | depth + 1 =>
      StepStar.rename (RawRenaming.lift RawRenaming.weaken)
        (StepStar.weakenBodyUnderOneBinderByStar chain depth)

/-- `RawTerm.weakenBodyUnderTwoBindersBy depth` preserves `StepStar` — iterated `StepStar.rename (lift (lift
weaken))`.  The directed twin of `Conv.weakenBodyUnderTwoBindersByConv` (the `substPairInto` / `natSucc`-macro
arms). -/
theorem StepStar.weakenBodyUnderTwoBindersByStar {scope : Nat} {leftBody rightBody : RawTerm (scope + 2)}
    (chain : StepStar leftBody rightBody) :
    (depth : Nat) →
    StepStar (RawTerm.weakenBodyUnderTwoBindersBy depth leftBody)
             (RawTerm.weakenBodyUnderTwoBindersBy depth rightBody)
  | 0 => chain
  | depth + 1 =>
      StepStar.rename (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (StepStar.weakenBodyUnderTwoBindersByStar chain depth)

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Axis.Syntax

/-- Replay a `StepStar` chain in the DOMAIN code of a `piTyCodeCell` (codomain fixed).  Induction on the chain,
each head step lifted by `Step.cong gen_piTyCode` at the head child position (`StepChildren.here`); the concrete
`piTyCodeCell` head pins the child shift. -/
theorem StepStar.piTyCodeDomainStar {scope : Nat} {domainStart domainTarget : RawTerm scope}
    (codomain : RawTerm (scope + 1)) (chain : StepStar domainStart domainTarget) :
    StepStar (piTyCodeCell domainStart codomain) (piTyCodeCell domainTarget codomain) := by
  induction chain with
  | refl _ => exact StepStar.refl _
  | trans headStep _ tailReduces =>
      exact StepStar.trans (Step.cong .gen_piTyCode () (.here _ headStep)) tailReduces

/-- Replay a `StepStar` chain in the CODOMAIN code of a `piTyCodeCell` (domain fixed).  As above, at the second
child position (`StepChildren.there … (.here …)`). -/
theorem StepStar.piTyCodeCodomainStar {scope : Nat} (domain : RawTerm scope)
    {codomainStart codomainTarget : RawTerm (scope + 1)}
    (chain : StepStar codomainStart codomainTarget) :
    StepStar (piTyCodeCell domain codomainStart) (piTyCodeCell domain codomainTarget) := by
  induction chain with
  | refl _ => exact StepStar.refl _
  | trans headStep _ tailReduces =>
      exact StepStar.trans (Step.cong .gen_piTyCode () (.there _ (.here _ headStep))) tailReduces

/-- `piTyCodeCell` is `StepStar`-congruent in BOTH the domain and codomain codes — the directed twin of
`Conv.piTyCode_cong`.  Step the domain (codomain fixed), then the codomain (domain fixed at target), composed. -/
theorem StepStar.piTyCode_cong {scope : Nat} {domainStart domainTarget : RawTerm scope}
    {codomainStart codomainTarget : RawTerm (scope + 1)}
    (domainChain : StepStar domainStart domainTarget)
    (codomainChain : StepStar codomainStart codomainTarget) :
    StepStar (piTyCodeCell domainStart codomainStart) (piTyCodeCell domainTarget codomainTarget) :=
  StepStar.trans_compose
    (StepStar.piTyCodeDomainStar codomainStart domainChain)
    (StepStar.piTyCodeCodomainStar domainTarget codomainChain)

end FX1Poly.Typed
