import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiContextStepConversion

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionUnconditional
    — the grown-engine master subject reduction ⋈ grown telescope SR, now UNCONDITIONAL

`HasTypeDescPiSubjectReductionMutual.lean` shipped the grown master SR ⋈ grown telescope SR as a mutual pair
CONDITIONAL on the single `piElim` context-conversion arm (`convContextOfPiElimArm`'s residual): the believed
logical-relation crux.  This file discharges that residual UNCONDITIONALLY and re-derives the same pair at the
canonical names `HasTypeDescPi.subjectReduction ⋈ DescTelescopePi.subjectReduction`.

## Why the residual was never actually needed

The conditional pair threads the arbitrary-`Conv` `piElim` arm everywhere, but USES it in exactly one place: the
telescope `here` arm, where a premise child's binding head steps (`head ⤳ headAfter`) and the tail telescope —
typed under `cons head` — must be re-typed under `cons headAfter`.  That is a context conversion across a SINGLE
stepped binder with the PREFIX UNCHANGED — the DIRECTED case.  The arbitrary-`Conv` arm is far stronger than this
directed instance needs.

`DescTelescopePi.contextConversionTelescopeExact` (the EXACT directed context conversion under the enriched
condition `ConvContextWithOldValid`) performs exactly that re-typing UNCONDITIONALLY: for a head step the prefix
is identical, so every prefix entry stays valid in the target by plain weakening (`ConvContextWithOldValid.
ofHeadStep`), and the enriched validity lets the var arm conv back to the EXACT old classifier — so the `piElim`
arm reforms via the native `HasTypeDescPi.piElim` with NO residual.  Swapping the lone `convTelescopeOfPiElimArm
piElimArm` call for `contextConversionTelescopeExact … (ofHeadStep …)` drops the hypothesis entirely.

## What ships

  * **`HasTypeDescPi.subjectReduction`** — the master dispatcher (unconditional).  `ofFormation` vacuous
    (`subjectAdmitsNoStep`); `conv` recurses; `piIntro` / `piElim` use the shipped function-space arms
    (`subjectReductionPiIntroArm` / `subjectReductionPiElimArmDescPi`) with the children's SR obtained recursively
    (extending the EXTENDABLE `WfContextDescPi` under the λ binder); `genFormationPi` decomposes via
    `former_step_inv` and re-types its premise telescope via the mutual telescope SR.
  * **`DescTelescopePi.subjectReduction`** — the telescope companion.  `here` (head steps): re-type the head via
    the mutual dispatcher, then re-type the tail under the stepped head via `contextConversionTelescopeExact` +
    `ofHeadStep`; `there` (a tail child steps): recurse under the extended `WfContextDescPi`.
  * **`HasTypeDescPi.subjectReductionStar`** — iterated SR along a whole `StepStar` chain (structural recursion
    on the chain, re-typing each single step via the master SR).  This is the preservation form consumed as a
    hypothesis by the grown closed / open type-safety theorems; it is now dischargeable unconditionally.

Argument order `(telescope) (wellFormed)` (telescope BEFORE well-formedness) is required for Lean's
mutual-recursion implicit inference — the telescope pins all the `levels`/`flag`/`children` implicits.

## Zero-axiom verification

Mutual structural recursion on the derivation / telescope + the shipped per-arm SR lemmas + `subjectAdmitsNoStep`
+ `former_step_inv` + the EXACT directed context conversion (`contextConversionTelescopeExact` /
`ConvContextWithOldValid.ofHeadStep`) + `WfContextDescPi.cons`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- **The grown-engine master subject reduction, UNCONDITIONAL.**  A grown-typed subject is preserved under a
`Step`, at the SAME classifier.  Threads the EXTENDABLE `WfContextDescPi`; `ofFormation` is vacuous, `conv`
recurses, `piIntro` / `piElim` use the shipped function-space arms with the children's SR obtained recursively,
`genFormationPi` re-types its premise telescope via the mutual `DescTelescopePi.subjectReduction`.  The lone
context-conversion need (the telescope head-step tail re-typing) is met by the EXACT directed context conversion,
so no `piElim` residual remains. -/
theorem HasTypeDescPi.subjectReduction {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescPi profile context reduct classifier :=
  match derivation with
  | .ofFormation formationTyped => fun reduct step =>
      absurd step (formationTyped.subjectAdmitsNoStep reduct)
  | .conv levelExpr flag typed converts reclassifierTyped => fun reduct step =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.subjectReduction typed wellFormed reduct step)
        converts reclassifierTyped
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
        (fun {bodyReduct} bodyStep =>
          HasTypeDescPi.subjectReduction bodyTyped
            (WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩) bodyReduct bodyStep)
  | .piElim functionTyped argumentTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiElimArmDescPi functionTyped argumentTyped step
        (fun {functionReduct} functionStep =>
          HasTypeDescPi.subjectReduction functionTyped wellFormed functionReduct functionStep)
        (fun {argumentReduct} argumentStep =>
          HasTypeDescPi.subjectReduction argumentTyped wellFormed argumentReduct argumentStep)
        wellFormed
  | .genFormationPi formerContext generator payload children levels flag rule isFormation premises =>
      fun reduct step => by
      obtain ⟨children', reductEq, stepChildren⟩ := former_step_inv isFormation step
      subst reductEq
      exact HasTypeDescPi.genFormationPi formerContext generator payload children' levels flag rule
        isFormation
        (DescTelescopePi.subjectReduction premises wellFormed children' stepChildren)

/-- **The grown premise-telescope subject reduction** (the mutual companion, UNCONDITIONAL).  A grown premise
telescope is preserved under a child `Step`.  `here` (the binding head steps): re-type the head via the mutual
dispatcher, then re-type the tail under the stepped binding via the EXACT directed context conversion
`DescTelescopePi.contextConversionTelescopeExact` (fed the head-step enriched condition
`ConvContextWithOldValid.ofHeadStep`); `there` (a tail child steps): recurse under the extended
`WfContextDescPi`. -/
theorem DescTelescopePi.subjectReduction {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children)
    (wellFormed : WfContextDescPi context) :
    ∀ (children' : RawTermChildren binderShifts baseScope),
      StepChildren children children' → DescTelescopePi profile context levels flag children' :=
  match telescope with
  | .nil _context _flag => fun _children' stepChildren =>
      (StepChildren.no_step_at_empty_spine stepChildren).elim
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      fun _children' stepChildren => by
        cases stepChildren with
        | here _rest headStep =>
            rename_i headAfter
            refine DescTelescopePi.cons context headAfter headLevel restLevels flag rest
              (HasTypeDescPi.subjectReduction headTyped wellFormed headAfter headStep) ?_
            exact DescTelescopePi.contextConversionTelescopeExact restTyped
              (context.cons headAfter)
              (ConvContextWithOldValid.ofHeadStep
                (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩) headStep)
        | there _head restStep =>
            rename_i restAfter
            exact DescTelescopePi.cons context head headLevel restLevels flag restAfter headTyped
              (DescTelescopePi.subjectReduction restTyped
                (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩) restAfter restStep)

end

/-- **Iterated (multi-step) subject reduction, UNCONDITIONAL.**  A grown-typed subject is preserved along an
entire `StepStar` reduction chain, at the SAME classifier.  Structural recursion on the chain: `refl` returns the
typing unchanged; `trans firstStep rest` re-types the single-step reduct via the master `HasTypeDescPi.
subjectReduction`, then recurses on `rest` under the SAME `wellFormed` (context and classifier are invariant
under reduction).  This is the preservation form consumed as a hypothesis by the grown closed / open type-safety
theorems. -/
theorem HasTypeDescPi.subjectReductionStar {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : StepStar subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  match chain with
  | .refl _ => typed
  | .trans firstStep rest =>
      HasTypeDescPi.subjectReductionStar wellFormed
        (HasTypeDescPi.subjectReduction typed wellFormed _ firstStep) rest

/-- **Grown type validity survives reduction — for the FULL grown engine, under `WfContextDescPi`.**  If
`subjectType` is a grown type code (`IsTypeDescPi`) in a well-formed context and it reduces to `reductType`, then
`reductType` is a grown type code, at the SAME universe classifier.  A direct corollary of `subjectReductionStar`
(the universe classifier is preserved at every step).  This is the FULL-engine, well-formed-context form of the
flexible context-conversion residual `TypeCodeValidityRespectsReduction` (type validity survives reduction): it
subsumes the formation-fragment `validityRespectsReductionOfFormation` and the head-β `validityRespectsBetaRedex`
over the ENTIRE grown type-code fragment — INCLUDING type-level-computing applications — at the cost of carrying the
well-formed-context presupposition.  That presupposition is irreducible (`HasTypeDescPi → WfContextDesc` is refuted),
but BENIGN: it is exactly the premise the flexible grown context-conversion bundle already carries (its `var` arm
reads the target binding's validity off `WfContextDescPi.lookupIsType`).  So the residual that was believed to "route
through the logical relation" is not logical-relation-hard once master subject reduction is unconditional — only
well-formed-context-gated. -/
theorem HasTypeDescPi.typeValiditySurvivesReductionUnderWf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subjectType reductType : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (isType : IsTypeDescPi profile context subjectType)
    (reduces : StepStar subjectType reductType) :
    IsTypeDescPi profile context reductType := by
  obtain ⟨levelExpr, flag, subjectTyped⟩ := isType
  exact ⟨levelExpr, flag, HasTypeDescPi.subjectReductionStar wellFormed subjectTyped reduces⟩

end FX1Poly.Typed
