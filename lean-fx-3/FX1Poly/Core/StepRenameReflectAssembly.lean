import FX1Poly.Core.StepRenameReflectEliminatorIota
import FX1Poly.Core.RawTermFoldNonVarCommute

/-! # FX1Poly/Core/StepRenameReflectAssembly
    — the full arbitrary-renaming `Step` reflection-with-image

This file assembles the COMPLETE arbitrary-renaming `Step` reflection-with-image

  `Step (rename rho t) u → ∃ t', Step t t' ∧ rename rho t' = u`

(the Kripke-arrow-CR3 ingredient the open-context logical relation `GrownCtxConv-5` needs) out of the
per-redex leaf arms shipped in `StepRenameReflect.lean` / `StepRenameReflectEliminatorIota.lean`
plus the recursive `cong` / children-`here` / children-`there` cases.

## The structure: `Step.subst` run backward

The shipped FORWARD closure `Step.rename` (`StepRename.lean`) factored through `Step.subst` — a
renaming is a substitution composed with identity, so the forward map reuses the more-general
substitution lemma and never re-does the mutual recursion.  The BACKWARD (reflection) direction
CANNOT factor that way: substitution creates redexes (e.g. substituting a `λ` into a variable
position manufactures a β-redex), so reflection-through-substitution is FALSE in general.  Renaming
only relabels variables — it preserves the term skeleton exactly — so every redex in `rename rho t`
sits at a position that is already a redex in `t`.  That is why reflection is true for an ARBITRARY
`rho` (no injectivity, no left inverse) and why it is proved STRUCTURALLY, by the same
`Step.rec` / `StepChildren.rec` mutual recursion that `Step.subst` uses, only run backward.

The motive generalizes the renamed subject: `motiveStep s u _ := ∀ origin originRho, rename originRho
origin = s → ∃ originReduct, Step origin originReduct ∧ rename originRho originReduct = u`.  The
recursor's 18 `Step` cases + 2 `StepChildren` cases then split exactly:

  * **18 redex-leaf cases** (β + 16 ι) are one-liners delegating to the shipped `Step.reflect*` arms —
    each arm's `rename rho term = <redex shape>` hypothesis is precisely the per-case motive premise.
  * **`cong`** recovers the source cell head (`rename_eq_mkGen`), distributes `rename` over the
    non-var cell (`rename_mkGen_of_ne_var`, payload preserved by a scope-invariance transport),
    reflects the children spine via the inline `motiveChildren` IH, and rebuilds with `Step.cong`.
    The `gen_var` sub-case is vacuous — `cong`'s `StepChildren` premise on a variable's empty child
    spine has no constructor (`cases childStep`).
  * **`here` / `there`** decompose the renamed child spine (`childCons` rename distributes by `rfl`,
    threading `iterateLiftRaw rho headShift` onto the head child — the LIFTED renaming, the reason
    arbitrary-`rho` reflection is required), reflect the stepping child via the appropriate mutual IH
    (`motiveStep` for `here`, `motiveChildren` for `there`), and rebuild with `StepChildren.here` /
    `StepChildren.there`.

With this, the full reflection assembles → Kripke-arrow CR3 → the open-context (Kripke) logical
relation that discharges `GrownCtxConv-5` (#842), the grown context-conversion `piElim` crux.

## Zero-axiom verification

The leaf arms are propext-free by construction (their shipped gates); the `Step.rec` assembly adds
only `rename_eq_mkGen` head-recovery, the `rename_mkGen_of_ne_var` / `childCons`-rfl distributions,
`injection`, and the matching reduction constructors — no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per-declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **The full arbitrary-renaming `Step` reflection-with-image.**  If a renamed term `rename rho
sourceTerm` `Step`-reduces to `targetReduct`, then `sourceTerm` itself `Step`-reduces to some
`sourceReduct` whose renaming under the SAME `rho` is exactly `targetReduct`.  Reflection holds for
ANY renaming `rho` (no injectivity / left-inverse needed) because renaming preserves the term
skeleton, so every reduct of the renamed term is the image of a reduct of the source.  Proved by the
`Step.rec` mutual recursion (the `Step.subst` template run backward): 18 redex-leaf cases delegate to
the shipped `Step.reflect*` arms, and the recursive `cong` / `here` / `there` cases thread the lifted
renaming through the children spine.  The Kripke-arrow-CR3 ingredient for the open-context logical
relation (`GrownCtxConv-5`, #842). -/
theorem Step.reflectRename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {sourceTerm : RawTerm sourceScope}
    {targetReduct : RawTerm targetScope}
    (renamedStep : Step (RawTerm.rename rho sourceTerm) targetReduct) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step sourceTerm sourceReduct ∧ RawTerm.rename rho sourceReduct = targetReduct := by
  let motiveStep :
      {scope : Nat} → (first second : RawTerm scope) → Step first second → Prop :=
    fun {scope} first second _ =>
      ∀ {sourceScope : Nat} (originTerm : RawTerm sourceScope)
        (originRenaming : RawRenaming sourceScope scope),
        RawTerm.rename originRenaming originTerm = first →
        ∃ originReduct : RawTerm sourceScope,
          Step originTerm originReduct ∧ RawTerm.rename originRenaming originReduct = second
  let motiveChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
        (first second : RawTermChildren binderShifts parentScope) →
        StepChildren first second → Prop :=
    fun {parentScope} {binderShifts} first second _ =>
      ∀ {sourceScope : Nat} (originChildren : RawTermChildren binderShifts sourceScope)
        (originRenaming : RawRenaming sourceScope parentScope),
        RawTermChildren.rename originRenaming originChildren = first →
        ∃ originReduct : RawTermChildren binderShifts sourceScope,
          StepChildren originChildren originReduct ∧
            RawTermChildren.rename originRenaming originReduct = second
  exact
    (Step.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      -- beta
      (fun {scope} {domainAnn} {body} {arg} {srcScope} originTerm originRho req =>
        Step.reflectBeta originRho req)
      -- cong
      (fun {scope} generator payload {children} {children'} childStep childStepIH
          {srcScope} originTerm originRho req => by
        by_cases hVar : generator = .gen_var
        · subst hVar
          cases childStep
        · obtain ⟨sourcePayload, sourceChildren, sourceTermEq⟩ :=
            RawTerm.rename_eq_mkGen originRho req
          subst sourceTermEq
          rw [RawTerm.rename_mkGen_of_ne_var originRho hVar sourcePayload sourceChildren] at req
          injection req with _scopeEq _genEq payloadEq childrenRenameEq
          obtain ⟨sourceChildren', childrenStep, childrenImageEq⟩ :=
            childStepIH sourceChildren originRho childrenRenameEq
          refine ⟨.mkGen generator sourcePayload sourceChildren',
            Step.cong generator sourcePayload childrenStep, ?_⟩
          rw [RawTerm.rename_mkGen_of_ne_var originRho hVar sourcePayload sourceChildren',
            childrenImageEq, payloadEq])
      -- iotaBoolTrue (Phase-Z: motive binder added at scope + 1, scrutinee last)
      (fun {scope} {motive} {thenBranch} {elseBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaBoolTrue originRho req)
      -- iotaBoolFalse (Phase-Z: motive binder added at scope + 1, scrutinee last)
      (fun {scope} {motive} {thenBranch} {elseBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaBoolFalse originRho req)
      -- iotaFstPair
      (fun {scope} {firstValue} {secondValue} {srcScope} originTerm originRho req =>
        Step.reflectIotaFstPair originRho req)
      -- iotaSndPair
      (fun {scope} {firstValue} {secondValue} {srcScope} originTerm originRho req =>
        Step.reflectIotaSndPair originRho req)
      -- iotaNatElimZero (Phase-Z: motive binder at scope + 1, succ at scope + 2, scrutinee last)
      (fun {scope} {motive} {zeroBranch} {succBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaNatElimZero originRho req)
      -- iotaNatRecZero (Phase-Z: motive binder at scope + 1, succ at scope + 2, scrutinee last)
      (fun {scope} {motive} {zeroBranch} {succBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaNatRecZero originRho req)
      -- iotaListElimNil (Phase-Z: motive binder added at scope + 1, scrutinee last)
      (fun {scope} {motive} {nilBranch} {consBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaListElimNil originRho req)
      -- iotaOptionMatchNone
      (fun {scope} {noneBranch} {someBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaOptionMatchNone originRho req)
      -- iotaOptionMatchSome
      (fun {scope} {value} {noneBranch} {someBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaOptionMatchSome originRho req)
      -- iotaEitherMatchInl
      (fun {scope} {value} {leftBranch} {rightBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaEitherMatchInl originRho req)
      -- iotaEitherMatchInr
      (fun {scope} {value} {leftBranch} {rightBranch} {srcScope} originTerm originRho req =>
        Step.reflectIotaEitherMatchInr originRho req)
      -- iotaNatElimSucc (Phase-Z: motive binder at scope + 1, succ at scope + 2, scrutinee last)
      (fun {scope} {motive} {predecessor} {zeroBranch} {succBranch} {srcScope}
          originTerm originRho req =>
        Step.reflectIotaNatElimSucc originRho req)
      -- iotaNatRecSucc (Phase-Z: motive binder at scope + 1, succ at scope + 2, scrutinee last)
      (fun {scope} {motive} {predecessor} {zeroBranch} {succBranch} {srcScope}
          originTerm originRho req =>
        Step.reflectIotaNatRecSucc originRho req)
      -- iotaListElimCons (Phase-Z: motive binder added at scope + 1, scrutinee last)
      (fun {scope} {motive} {headVal} {tailVal} {nilBranch} {consBranch} {srcScope}
          originTerm originRho req =>
        Step.reflectIotaListElimCons originRho req)
      -- iotaIdJRefl
      (fun {scope} {baseCase} {rawWitness} {srcScope} originTerm originRho req =>
        Step.reflectIotaIdJRefl originRho req)
      -- iotaIdStrictRecRefl
      (fun {scope} {baseCase} {rawWitness} {srcScope} originTerm originRho req =>
        Step.reflectIotaIdStrictRecRefl originRho req)
      -- here: the stepping head child reflects via the term-level mutual IH at the lifted renaming
      (fun {parentScope} {headShift} {restShifts} {head} {head'} rest childStep childStepIH
          {srcScope} originChildren originRho req => by
        cases originChildren with
        | childCons sourceHead sourceRest =>
            rw [show RawTermChildren.rename originRho
                  (.childCons sourceHead sourceRest) =
                  (.childCons (RawTerm.rename (iterateLiftRaw originRho headShift) sourceHead)
                    (RawTermChildren.rename originRho sourceRest)
                    : RawTermChildren (headShift :: restShifts) parentScope) from rfl] at req
            injection req with _scopeEq _shiftEq _restEq headRenameEq restRenameEq
            obtain ⟨sourceHead', headStep, headImageEq⟩ :=
              childStepIH sourceHead (iterateLiftRaw originRho headShift) headRenameEq
            refine ⟨.childCons sourceHead' sourceRest,
              StepChildren.here sourceRest headStep, ?_⟩
            rw [show RawTermChildren.rename originRho
                  (.childCons sourceHead' sourceRest) =
                  (.childCons (RawTerm.rename (iterateLiftRaw originRho headShift) sourceHead')
                    (RawTermChildren.rename originRho sourceRest)
                    : RawTermChildren (headShift :: restShifts) parentScope) from rfl,
              headImageEq, restRenameEq])
      -- there: the stepping tail spine reflects via the children-level mutual IH
      (fun {parentScope} {headShift} {restShifts} head {rest} {rest'} restStep restStepIH
          {srcScope} originChildren originRho req => by
        cases originChildren with
        | childCons sourceHead sourceRest =>
            rw [show RawTermChildren.rename originRho
                  (.childCons sourceHead sourceRest) =
                  (.childCons (RawTerm.rename (iterateLiftRaw originRho headShift) sourceHead)
                    (RawTermChildren.rename originRho sourceRest)
                    : RawTermChildren (headShift :: restShifts) parentScope) from rfl] at req
            injection req with _scopeEq _shiftEq _restEq headRenameEq restRenameEq
            obtain ⟨sourceRest', restStepReflected, restImageEq⟩ :=
              restStepIH sourceRest originRho restRenameEq
            refine ⟨.childCons sourceHead sourceRest',
              StepChildren.there sourceHead restStepReflected, ?_⟩
            rw [show RawTermChildren.rename originRho
                  (.childCons sourceHead sourceRest') =
                  (.childCons (RawTerm.rename (iterateLiftRaw originRho headShift) sourceHead)
                    (RawTermChildren.rename originRho sourceRest')
                    : RawTermChildren (headShift :: restShifts) parentScope) from rfl,
              headRenameEq, restImageEq])
      renamedStep)
      sourceTerm rho rfl

end FX1Poly.Core
