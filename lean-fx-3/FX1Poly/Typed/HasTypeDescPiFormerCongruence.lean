import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiValidity

/-! # FX1Poly/Typed/HasTypeDescPiFormerCongruence — grown-engine FORMER codomain-congruence arms
    (the type-former `Step.cong` cases of subject reduction, modulo the codomain's SR; toward #458/SN-055)

The λ/app congruence arms (`HasTypeDescPiCongruence`) cover `Step.cong` into a `lamCell` body or an
`appCell` function/argument.  The SR master dispatcher (#458) additionally needs the `Step.cong`-into-a-
type-FORMER cases — a step inside the domain or codomain of `Π`/`Σ`.  This file ships the CODOMAIN
side for both formers (the binder-side child), which — exactly like `congLamBody` — re-types the
codomain under the SAME `cons domain` context, so it needs NO context-conversion.

## Why codomain-cong is free, domain-cong is not

The genFormationPi premise types `[domain, codomain]` as a dependent telescope: `domain` at
`domainLevel` under `context`, and `codomain` at `codomainLevel` under `context.cons domain`.

  * **Codomain steps** (`codomain ⤳ codomain'`): the context `cons domain` is UNCHANGED, so
    `childPreserves` re-types `codomain'` at the same `codomainLevel` under `cons domain`, and the
    former re-fires at the same output level (`lmax domainLevel codomainLevel`) — free.  THIS FILE.
  * **Domain steps** (`domain ⤳ domain'`): the codomain was typed under `cons domain`; the re-fired
    former needs it under `cons domain'`.  Since `domain ⤳ domain'` gives `Conv domain domain'`, that
    transfer is exactly CONTEXT-CONVERSION (typing stable under a Conv-replaced context entry) — a
    separate, heavier brick deferred to its own fire.  (Domain steps only occur for GROWN domains —
    formation domains are normal — so this gap bites only on nested-redex domains.)

## What this file ships

  * `HasTypeDescPi.piFormationViaGenArm` / `sigmaFormationViaGenArm` — the grown-engine Π/Σ formation
    INTRODUCTIONS through the generic `genFormationPi` arm (grown analogues of
    `hasTypeDesc_piFormation_viaGenArm`): from grown domain + codomain type-derivations, the former
    inhabits `Type@(lmax domainLevel codomainLevel)`.  Reusable (the dispatcher's domain-cong will reuse
    them too); one `typingRuleDescOf` row, ZERO new arms (P13).
  * `HasTypeDescPi.congPiCodomain` / `congSigmaCodomain` — the SR `cong`-into-codomain arms: invert the
    former (`invertPiTyCode` / `invertSigmaTyCode`), re-type the codomain via `childPreserves`, re-fire
    the former, and `conv` back to the original classifier.  The exact `congLamBody` recipe, one
    dimension over (former instead of λ).

`childPreserves` is binder-context-general (`∀ {D S}, … (cons D) codomain S → … (cons D) codomain' S`),
precisely the shape `Step.subjectReduction`'s "preserves ANY classifier" provides.

## Zero-axiom verification

The reconstructions are direct `genFormationPi` applications (output reduces through `universeFormerOutput`
+ `lmaxAll` to `universeCodeCell (lmax …) flag` definitionally).  The cong arms compose shipped zero-axiom
results (`invertPiTyCode`/`invertSigmaTyCode`, `classifierIsTypeDesc`, the `conv` rule).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Grown-engine Π formation via the generic arm.**  From grown type-derivations of the `domain`
(at `domainLevel`) and the `codomain` (at `codomainLevel` under the domain binder), `piTyCodeCell
domainCode codomainCode` inhabits `Type@(lmax domainLevel codomainLevel)` — through the SAME generic
`genFormationPi` arm (one `typingRuleDescOf` row, no new arm).  The grown analogue of
`hasTypeDesc_piFormation_viaGenArm`; its output `universeFormerOutput scope [domainLevel, codomainLevel]
flag` reduces to `universeCodeCell (lmax domainLevel codomainLevel) flag` definitionally. -/
theorem HasTypeDescPi.piFormationViaGenArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  refine HasTypeDescPi.genFormationPi context .gen_piTyCode ()
    (RawTermChildren.binderShape domainCode codomainCode) [domainLevel, codomainLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_piTyCode ?_
  refine DescTelescopePi.cons (currentDepth := 0) context domainCode domainLevel
    [codomainLevel] flag (.childCons codomainCode .childNil) domainTyped ?_
  exact DescTelescopePi.cons (currentDepth := 1) (context.cons domainCode) codomainCode
    codomainLevel [] flag .childNil codomainTyped
    (DescTelescopePi.nil (currentDepth := 2) (context.cons domainCode |>.cons codomainCode) flag)

/-- **Grown-engine Σ formation via the generic arm.**  The dual of `piFormationViaGenArm` over
`gen_sigmaTyCode` — identical recipe, one `typingRuleDescOf` row. -/
theorem HasTypeDescPi.sigmaFormationViaGenArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  refine HasTypeDescPi.genFormationPi context .gen_sigmaTyCode ()
    (RawTermChildren.binderShape domainCode codomainCode) [domainLevel, codomainLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_sigmaTyCode ?_
  refine DescTelescopePi.cons (currentDepth := 0) context domainCode domainLevel
    [codomainLevel] flag (.childCons codomainCode .childNil) domainTyped ?_
  exact DescTelescopePi.cons (currentDepth := 1) (context.cons domainCode) codomainCode
    codomainLevel [] flag .childNil codomainTyped
    (DescTelescopePi.nil (currentDepth := 2) (context.cons domainCode |>.cons codomainCode) flag)

/-- **Π-codomain congruence (at typing).**  A `piTyCodeCell domainCode codomainCode` typed at
`classifier`, with a same-typed replacement `codomainCode'` (preserved at any codomain classifier under
any domain binder), gives `piTyCodeCell domainCode codomainCode'` typed at the SAME `classifier`.  The
`Step.cong`-into-a-Π-codomain case of subject reduction, modulo the codomain's SR (`childPreserves`).
`invertPiTyCode` exposes the domain/codomain typings + `Conv classifier (Type@(lmax …))`;
`piFormationViaGenArm` rebuilds at `Type@(lmax …)`; `classifierIsTypeDesc` + `conv` returns to
`classifier`.  No context-conversion (the `cons domainCode` context is unchanged). -/
theorem HasTypeDescPi.congPiCodomain {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode codomainCode' : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) classifier)
    (childPreserves : ∀ {bindingType : RawTerm scope} {codomainClassifier : RawTerm (scope + 1)},
      HasTypeDescPi profile (context.cons bindingType) codomainCode codomainClassifier →
        HasTypeDescPi profile (context.cons bindingType) codomainCode' codomainClassifier)
    (wellFormed : WfContext context) :
    HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode') classifier := by
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, convClassifierToCode⟩ :=
    typed.invertPiTyCode wellFormed
  have rebuilt :
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode')
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
    HasTypeDescPi.piFormationViaGenArm context domainCode codomainCode' domainLevel codomainLevel
      flag domainTyped (childPreserves codomainTyped)
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ := typed.classifierIsTypeDesc wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag rebuilt convClassifierToCode.sym
    classifierTyped

/-- **Σ-codomain congruence (at typing).**  The dual of `congPiCodomain` over `sigmaTyCodeCell` — the
`Step.cong`-into-a-Σ-codomain case of subject reduction, modulo the codomain's SR. -/
theorem HasTypeDescPi.congSigmaCodomain {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode codomainCode' : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode) classifier)
    (childPreserves : ∀ {bindingType : RawTerm scope} {codomainClassifier : RawTerm (scope + 1)},
      HasTypeDescPi profile (context.cons bindingType) codomainCode codomainClassifier →
        HasTypeDescPi profile (context.cons bindingType) codomainCode' codomainClassifier)
    (wellFormed : WfContext context) :
    HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode') classifier := by
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, convClassifierToCode⟩ :=
    typed.invertSigmaTyCode wellFormed
  have rebuilt :
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode')
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
    HasTypeDescPi.sigmaFormationViaGenArm context domainCode codomainCode' domainLevel codomainLevel
      flag domainTyped (childPreserves codomainTyped)
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ := typed.classifierIsTypeDesc wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag rebuilt convClassifierToCode.sym
    classifierTyped

end FX1Poly.Typed
