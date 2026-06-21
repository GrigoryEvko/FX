import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluence

/-! # ElimOutputTypeCongruence — the eliminator output-type congruence ingredient of the eliminator-SR

The native eliminator subject-reduction (the residual `UnionElimCongruenceClosesToEmptyType` gate of the
TYTAB-2-FT consistency route, #1697) decomposes into TWO ingredients when a child of an eliminator cell steps:

  1. **child subject reduction** — the stepped child re-types (the recursion, supplied by the `ihPremises`
     of a `induction typed` single-step SR; the genuine FT-lane residual);
  2. **output-type Conv-stability** — the eliminator's OUTPUT type stays `Conv`-equal under the child step, so
     the re-formed cell still classifies at a convertible type.

This file ships ingredient (2) for the one row whose output type genuinely DEPENDS on a child: `app`, whose
output is `subst0 codomainCode argument` (the dependent application type).  Every OTHER core-fragment
eliminator (`fst`/`snd`/`boolElim`/`natElim`/`natRec`/`listElim`/`optionMatch`/`eitherMatch`/`idJ`) reads its
output type off the type-index PARAMS, not the stepping children, so its output-type Conv-stability is
`Conv.refl` — there is nothing to prove.  So `app` is the ENTIRE non-trivial content of ingredient (2), and it
is discharged here, unconditionally and zero-axiom, by the substitution-argument replay
`Step.subst0Argument` (a `StepStar` because the body may duplicate variable 0) composed with the
`StepStar → Conv` forward injection `Conv.fromStepStar`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The substitution body is `Conv`-stable when its substituted argument steps.**  `subst0 body argument`
replays the single `argument`-step at each of `body`'s var-0 occurrences — a `StepStar` (the body may use
var 0 zero or many times), hence a `Conv` via the forward injection.  This is the substitution-congruence
crux of the `app` eliminator's output-type stability. -/
theorem subst0_isConvStableUnderArgumentStep {scope : Nat} (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope} (argumentStep : Step argument updatedArgument) :
    Conv (RawTerm.subst0 body argument) (RawTerm.subst0 body updatedArgument) :=
  Conv.fromStepStar (Step.subst0Argument body argumentStep)

/-- **★ The `app` eliminator's output type is `Conv`-stable when its argument child steps.**  `app`'s output
type is the dependent application type `subst0 codomainCode argument`; when the `argument` child steps, the
output stays `Conv`-equal (ingredient (2) of the `app` eliminator subject reduction).  The `function` child
does NOT occur in the output type, so a function step leaves the output literally unchanged (`Conv.refl`) —
this argument case is the sole non-trivial half.  Reads the output type directly off the `appElimRule` row, so
it is exactly the table-native ingredient the native eliminator-SR consumes. -/
theorem appElimRuleOutputType_isConvStableUnderArgumentStep {scope : Nat}
    (function domainCode : RawTerm scope) {argument updatedArgument : RawTerm scope}
    (codomainCode : RawTerm (scope + 1))
    (argumentStep : Step argument updatedArgument) :
    Conv
      (appElimRule.outputType scope
        (.childCons function (.childCons argument .childNil))
        (.childCons domainCode (.childCons codomainCode .childNil)))
      (appElimRule.outputType scope
        (.childCons function (.childCons updatedArgument .childNil))
        (.childCons domainCode (.childCons codomainCode .childNil))) :=
  subst0_isConvStableUnderArgumentStep codomainCode argumentStep

end FX1Poly.Typed
