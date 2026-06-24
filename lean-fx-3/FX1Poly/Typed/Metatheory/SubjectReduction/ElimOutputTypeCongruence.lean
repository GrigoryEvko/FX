import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluence
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair

/-! # ElimOutputTypeCongruence — the eliminator output-type congruence ingredient of the eliminator-SR

The native eliminator subject-reduction (the residual `UnionElimCongruenceClosesToEmptyType` gate of the
TYTAB-2-FT consistency route, #1697) decomposes into TWO ingredients when a child of an eliminator cell steps:

  1. **child subject reduction** — the stepped child re-types (the recursion, supplied by the `ihPremises`
     of a `induction typed` single-step SR; the genuine FT-lane residual);
  2. **output-type Conv-stability** — the eliminator's OUTPUT type stays `Conv`-equal under the child step, so
     the re-formed cell still classifies at a convertible type.

This file ships ingredient (2).  After the DEP-* dependent-motive migration (#1713-#1731) the eleven
`ElimRule` output types split into THREE classes by what the output reads off:

  * **pure-param** (`fst` -> `firstType`, `snd` -> `secondType`, `pathApp` -> `carrierCode`): the output
    reads only the existential type-index PARAMS, never the stepping children, so a child step leaves the
    output literally unchanged — `Conv.refl`, nothing to prove.
  * **mixed** (`app` -> `subst0 codomainCode argument`): the codomain is a param but the `argument` is a
    child, so an argument step drifts the output; discharged by
    `appElimRuleOutputType_isConvStableUnderArgumentStep` via `subst0` argument-congruence (a `StepStar`
    because the body may duplicate variable 0).  A function step leaves the output unchanged.
  * **dependent** (`natElim`/`natRec`/`boolElim`/`optionMatch`/`eitherMatch`/`listElim` -> `subst0 motive
    scrutinee`; `idJ` -> `idJMotiveAt motive rightEndpoint witness`): the motive AND scrutinee (resp.
    witness) are CHILDREN, so a motive-step OR a scrutinee-step drifts the output — NOT `Conv.refl`.  This
    is the genuine content the dependent-motive migration introduced; the earlier revision of this note,
    which claimed every non-`app` row was `Conv.refl`, is STALE and is superseded here.

The six `subst0 motive scrutinee` rows are covered by the two `subst0`-congruence halves: the motive-step
(body) half `subst0_isConvStableUnderBodyStep` and the scrutinee-step (argument) half
`subst0_isConvStableUnderArgumentStep`, both built on the shipped two-sided `Conv.subst0`.  The branch
children never occur in the output, so a branch step is `Conv.refl`.  (`idJ`'s `idJMotiveAt` output is a
separate shape — a follow-up, not covered here.)  All unconditional and zero-axiom: `Conv.subst0` /
`Conv.fromStep` / `Conv.refl` / `Conv.fromStepStar`, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`. -/

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

/-- **The substitution result is `Conv`-stable when its BODY steps.**  The body-side dual of
`subst0_isConvStableUnderArgumentStep`: `subst0 body argument` stays `Conv`-equal when `body` (the term
under the var-0 binder) steps and the argument is fixed.  Built on the two-sided `Conv.subst0` with a
`Conv.refl` on the argument leg.  This is the substitution-congruence crux of the DEPENDENT eliminators'
output-type stability when their MOTIVE child steps (the motive is the body of `subst0 motive scrutinee`). -/
theorem subst0_isConvStableUnderBodyStep {scope : Nat} (argument : RawTerm scope)
    {body updatedBody : RawTerm (scope + 1)} (bodyStep : Step body updatedBody) :
    Conv (RawTerm.subst0 body argument) (RawTerm.subst0 updatedBody argument) :=
  Conv.subst0 (Conv.fromStep bodyStep) (Conv.refl argument)

/-- **★ A dependent eliminator's output type is `Conv`-stable when its MOTIVE child steps.**  The six
dependent eliminators (`natElim` / `natRec` / `boolElim` / `optionMatch` / `eitherMatch` / `listElim`)
share the output type `subst0 motive scrutinee`, reading the motive (binding one constructor variable) and
the scrutinee directly off the cell's children.  When the `motive` child steps, the output stays
`Conv`-equal via `subst0` body-congruence — the motive-step half of ingredient (2).  Stated over the
shared `subst0 motive scrutinee` shape, so it applies by defeq to every one of the six rows'
`ElimRule.outputType`. -/
theorem dependentEliminatorOutputType_isConvStableUnderMotiveStep {scope : Nat}
    (scrutinee : RawTerm scope) {motive updatedMotive : RawTerm (scope + 1)}
    (motiveStep : Step motive updatedMotive) :
    Conv (RawTerm.subst0 motive scrutinee) (RawTerm.subst0 updatedMotive scrutinee) :=
  subst0_isConvStableUnderBodyStep scrutinee motiveStep

/-- **★ A dependent eliminator's output type is `Conv`-stable when its SCRUTINEE child steps.**  Companion
to the motive-step lemma: when the `scrutinee` child of a dependent eliminator steps, the output
`subst0 motive scrutinee` stays `Conv`-equal via `subst0` argument-congruence (the scrutinee-step half).
Together the two halves discharge output-type `Conv`-stability for every `subst0 motive scrutinee` row
under any single child step — the branch children never occur in the output, so a branch step is
`Conv.refl`. -/
theorem dependentEliminatorOutputType_isConvStableUnderScrutineeStep {scope : Nat}
    (motive : RawTerm (scope + 1)) {scrutinee updatedScrutinee : RawTerm scope}
    (scrutineeStep : Step scrutinee updatedScrutinee) :
    Conv (RawTerm.subst0 motive scrutinee) (RawTerm.subst0 motive updatedScrutinee) :=
  subst0_isConvStableUnderArgumentStep motive scrutineeStep

/-- **★ `idJ`'s output type is `Conv`-stable when its MOTIVE child steps.**  Genuine path-induction's output
is `idJMotiveAt motive rightEndpoint witness = substPair motive witness rightEndpoint` — reading the
two-binder motive (binderShift 2) and the witness child off the cell.  When the `motive` child steps the
output stays `Conv`-equal via the body leg of `Conv.substPair`.  Stated over the shared `idJMotiveAt motive
point path` shape (`point := rightEndpoint`, `path := witness` for `idJElimRule.outputType`), so it applies
by defeq to the table row. -/
theorem idJOutputType_isConvStableUnderMotiveStep {scope : Nat}
    (point path : RawTerm scope) {motive updatedMotive : RawTerm (scope + 2)}
    (motiveStep : Step motive updatedMotive) :
    Conv (idJMotiveAt motive point path) (idJMotiveAt updatedMotive point path) :=
  Conv.substPair (Conv.fromStep motiveStep) (Conv.refl path) (Conv.refl point)

/-- **★ `idJ`'s output type is `Conv`-stable when its WITNESS child steps.**  Companion to the motive-step
lemma: in `idJMotiveAt motive point path = substPair motive path point` the `witness` child is the `path`
substituent (`var 0` of the motive's inner binder), so a witness step keeps the output `Conv`-equal via the
inner-substituent leg of `Conv.substPair`.  The base-case child does not occur in the output (a base-case
step is `Conv.refl`); the endpoints are type-index params, which never step under a child `StepChildren`. -/
theorem idJOutputType_isConvStableUnderWitnessStep {scope : Nat}
    (motive : RawTerm (scope + 2)) (point : RawTerm scope)
    {path updatedPath : RawTerm scope} (witnessStep : Step path updatedPath) :
    Conv (idJMotiveAt motive point path) (idJMotiveAt motive point updatedPath) :=
  Conv.substPair (Conv.refl motive) (Conv.fromStep witnessStep) (Conv.refl point)

end FX1Poly.Typed
