import FX1Poly.Core.ConvRenameReflection
import FX1Poly.Core.SubstPreservationProbes
import FX1Poly.Core.RawTermFoldNonVarCommute

/-! # FX1Poly/Core/RawTermRenameInjective — term-level rename injectivity from Fin-injectivity

`Conv.reflectRename` demands TERM-level injectivity of the renaming (`rename ρ l = rename ρ r →
l = r`), and so far only the `weaken` instance was discharged (`RawTerm.weaken_injective`, via the
`strengthen` partial left inverse).  The pinned reflection's binder arms (route H, STR-8) work at
`lift ρ`, where no strengthen-style inverse exists — the general statement is needed: **a
Fin-injective renaming is term-injective**.

  * `RawTerm.rename_injective` / `RawTermChildren.rename_injective` — the mutual structural
    induction.  Var heads reduce to the Fin payload (`rename_var_reduces`) and Fin-injectivity
    finishes; mixed heads die on the generator equation; non-var heads drill
    `rename_mkGen_of_ne_var`, strip the scope-invariance payload cast (`eqRecTypeCast_injective`),
    and recurse — the head child at `iterateLiftRaw ρ headShift`, whose injectivity is
    `RawRenaming.iterateLiftRaw_injective` (layered `RawRenaming.lift_injective`).
  * `Conv.reflectRenameOfFinInjective` — `Conv` reflects ANY Fin-injective renaming
    (`Conv.reflectRename` with the term-level hypothesis discharged).
  * `Conv.reflectLiftRename` — the binder instance the pinned reflection's piIntro arm consumes:
    `Conv` reflects `lift ρ` whenever `ρ` is Fin-injective.

## Zero-axiom verification

The mutual induction is the `subst_rename_commute` template (tactic `match` + structural
recursion); the payload cast strips by eliminating the type equality (`cases typesEqual`, plain
`Eq.rec`); `mkGen`/`childCons` injections emit plain `Eq` components here (the indices coincide
syntactically).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

universe u

/-- A cast along a type equality is injective: strip the cast by eliminating the equality. -/
theorem eqRecTypeCast_injective {firstType secondType : Sort u}
    (typesEqual : firstType = secondType)
    {leftValue rightValue : firstType}
    (castsAgree : typesEqual ▸ leftValue = typesEqual ▸ rightValue) :
    leftValue = rightValue := by
  cases typesEqual
  exact castsAgree

/-- Iterated lifting preserves injectivity: each layer is `RawRenaming.lift_injective`. -/
theorem RawRenaming.iterateLiftRaw_injective {sourceScope targetScope : Nat}
    {rho : RawRenaming sourceScope targetScope}
    (rhoInjective : Function.Injective rho) :
    ∀ binderDepth : Nat, Function.Injective (iterateLiftRaw rho binderDepth)
  | 0 => rhoInjective
  | priorDepth + 1 =>
      RawRenaming.lift_injective
        (RawRenaming.iterateLiftRaw_injective rhoInjective priorDepth)

mutual

/-- **Term-level rename injectivity from Fin-injectivity**: renaming by an injective positional
renaming is injective on terms. -/
theorem RawTerm.rename_injective {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (rhoInjective : Function.Injective rho)
    (leftTerm rightTerm : RawTerm sourceScope)
    (renamesAgree : RawTerm.rename rho leftTerm = RawTerm.rename rho rightTerm) :
    leftTerm = rightTerm := by
  match leftTerm, rightTerm with
  | .mkGen leftGenerator leftPayload leftChildren,
    .mkGen rightGenerator rightPayload rightChildren =>
    by_cases hVarLeft : leftGenerator = .gen_var
    · subst hVarLeft
      cases leftChildren with
      | childNil =>
        by_cases hVarRight : rightGenerator = .gen_var
        · subst hVarRight
          cases rightChildren with
          | childNil =>
            rw [RawTerm.rename_var_reduces, RawTerm.rename_var_reduces] at renamesAgree
            injection renamesAgree with hScope hGenerator hPayload hChildren
            have payloadImagesEqual : rho leftPayload = rho rightPayload := hPayload
            exact congrArg
              (fun varIndex => RawTerm.mkGen Generator.gen_var varIndex RawTermChildren.childNil)
              (rhoInjective payloadImagesEqual)
        · rw [RawTerm.rename_var_reduces,
              RawTerm.rename_mkGen_of_ne_var rho hVarRight] at renamesAgree
          injection renamesAgree with hScope hGenerator hPayload hChildren
          exact absurd hGenerator.symm hVarRight
    · by_cases hVarRight : rightGenerator = .gen_var
      · subst hVarRight
        cases rightChildren with
        | childNil =>
          rw [RawTerm.rename_mkGen_of_ne_var rho hVarLeft,
              RawTerm.rename_var_reduces] at renamesAgree
          injection renamesAgree with hScope hGenerator hPayload hChildren
          exact absurd hGenerator hVarLeft
      · rw [RawTerm.rename_mkGen_of_ne_var rho hVarLeft,
            RawTerm.rename_mkGen_of_ne_var rho hVarRight] at renamesAgree
        injection renamesAgree with hScope hGenerator hPayload hChildren
        subst hGenerator
        have payloadCastsAgree := eq_of_heq hPayload
        have payloadsEqual : leftPayload = rightPayload :=
          eqRecTypeCast_injective
            (Generator.payload_scope_invariant_of_not_var hVarLeft sourceScope targetScope)
            payloadCastsAgree
        have childrenImagesEqual := eq_of_heq hChildren
        have childrenEqual : leftChildren = rightChildren :=
          RawTermChildren.rename_injective rho rhoInjective
            leftChildren rightChildren childrenImagesEqual
        rw [payloadsEqual, childrenEqual]

/-- Spine half of the mutual: rename injectivity on children spines (head recurses at the lifted
renaming via `iterateLiftRaw_injective`). -/
theorem RawTermChildren.rename_injective {parentSourceScope parentTargetScope : Nat}
    (rho : RawRenaming parentSourceScope parentTargetScope)
    (rhoInjective : Function.Injective rho)
    {binderShifts : List Nat}
    (leftChildren rightChildren : RawTermChildren binderShifts parentSourceScope)
    (renamesAgree :
      RawTermChildren.rename rho leftChildren = RawTermChildren.rename rho rightChildren) :
    leftChildren = rightChildren := by
  match binderShifts, leftChildren, rightChildren with
  | [], .childNil, .childNil => rfl
  | headShift :: restShifts,
    .childCons leftHead leftTail, .childCons rightHead rightTail =>
    have reducedAgree :
        RawTermChildren.childCons
            (RawTerm.rename (iterateLiftRaw rho headShift) leftHead)
            (RawTermChildren.rename rho leftTail) =
          RawTermChildren.childCons
            (RawTerm.rename (iterateLiftRaw rho headShift) rightHead)
            (RawTermChildren.rename rho rightTail) := renamesAgree
    injection reducedAgree with hScope hShift hRestShifts hHead hTail
    have headsEqual : leftHead = rightHead :=
      RawTerm.rename_injective (iterateLiftRaw rho headShift)
        (RawRenaming.iterateLiftRaw_injective rhoInjective headShift)
        leftHead rightHead hHead
    have tailsEqual : leftTail = rightTail :=
      RawTermChildren.rename_injective rho rhoInjective
        leftTail rightTail hTail
    rw [headsEqual, tailsEqual]

end -- mutual

/-- **`Conv` reflects any Fin-injective renaming** — `Conv.reflectRename` with the term-level
injectivity discharged by `RawTerm.rename_injective`.  The pinned reflection consumes this at
`RawRenaming.lift rho` (with `RawRenaming.lift_injective`) in its binder arms. -/
theorem Conv.reflectRenameOfFinInjective {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (rhoInjective : Function.Injective rho)
    {leftTerm rightTerm : RawTerm sourceScope}
    (convertibility : Conv (RawTerm.rename rho leftTerm) (RawTerm.rename rho rightTerm)) :
    Conv leftTerm rightTerm :=
  Conv.reflectRename rho
    (fun imagesAgree => RawTerm.rename_injective rho rhoInjective _ _ imagesAgree)
    convertibility

/-- The binder instance the pinned reflection's piIntro arm consumes: `Conv` reflects `lift rho`
whenever `rho` is Fin-injective. -/
theorem Conv.reflectLiftRename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (rhoInjective : Function.Injective rho)
    {leftTerm rightTerm : RawTerm (sourceScope + 1)}
    (convertibility : Conv (RawTerm.rename (RawRenaming.lift rho) leftTerm)
      (RawTerm.rename (RawRenaming.lift rho) rightTerm)) :
    Conv leftTerm rightTerm :=
  Conv.reflectRenameOfFinInjective (RawRenaming.lift rho)
    (RawRenaming.lift_injective rhoInjective) convertibility

end FX1Poly.Core
