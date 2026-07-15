import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Cell.RawTermMorphismCell

/-! # FX1Poly/Typed/Engine/Union/RawTermMorphismFormationObligations — the formation-obligation push, ONCE

The formation-obligation push family used to exist twice: once for renaming, once for
substitution, byte-identical modulo the action.  This file states it ONCE, generically
over any raw-term morphism (`LiftsRaw` + `ActsOnRawTermVar`, i.e. exactly `fold`'s two
constraints — see `RawTermMorphismCell.lean`), and the renaming / substitution twins in
`HasTypeUnionFormationObligations.lean` become instantiations at their Container with
their EXACT names and EXACT types preserved.

## Why this abstraction is sound here (and where it stops)

Nothing in the obligation-list push inspects the action.  The push is a structural
recursion over the `RawTermChildren` spine that (a) transports children through the
action and (b) rewrites the CLOSED universe-code classifier, which every morphism
fixes (`applyMorphism_universeCodeCell`).  The one place rename and subst genuinely
differ — the variable action — is never reached, because a formation obligation's
classifier is a closed universe code, never a variable.  That is precisely why the
twin collapses here and does NOT collapse at `rename_variableCell` /
`subst_variableCell`.

## Zero-axiom verification

Structural recursion over the spine + `cases` on `List.Mem` constructors (NOT the
`mem_map` / `mem_append` iff lemmas, which leak `propext`) + the generic closed-cell
`applyMorphism_universeCodeCell`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`, `WellFounded.fix`.  Per-declaration audit-gated
in `FX1PolyAudit/Typed/Engine/Union/RawTermMorphismFormationObligations.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- ★ **The flat-family obligation push, generic in the morphism.**  The single content
behind `flatFormationObligations_pushSubst` / `flatFormationObligations_pushRename`:
per source flat child the hypothesis delivers the union typing of its transported form
at the closed universe code; the conclusion is every target obligation over the
transported children, union-typed.  Generic over the spine (induct on the shape
`binderShifts`, `cases` the mutual `RawTermChildren`) AND over the action. -/
theorem flatFormationObligations_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ flatFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile targetContext (RawTerm.applyMorphism morphism subject)
          (RawTerm.applyMorphism morphism classifier)) →
      ∀ targetObligation ∈ flatFormationObligations profile targetContext flag
          (RawTermChildren.applyMorphism morphism children) levels,
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro children levels _sourceTypings targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children levels sourceTypings targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases levels with
              | nil =>
                  -- LEVELS EXHAUSTED: the obligation list FORCES the remaining children at `lzero`.
                  cases targetMember with
                  | head =>
                      have headTyped := sourceTypings childHead (universeCodeCell LevelExpr.lzero flag)
                        (List.Mem.head _)
                      rwa [applyMorphism_universeCodeCell] at headTyped
                  | tail _ tailMember =>
                      exact ih childTail []
                        (fun subject classifier member =>
                          sourceTypings subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
              | cons headLevel restLevels =>
                  cases targetMember with
                  | head =>
                      have headTyped := sourceTypings childHead (universeCodeCell headLevel flag)
                        (List.Mem.head _)
                      rwa [applyMorphism_universeCodeCell] at headTyped
                  | tail _ tailMember =>
                      exact ih childTail restLevels
                        (fun subject classifier member =>
                          sourceTypings subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
          | succ _ => cases targetMember

/-- ★ **The term-indexed endpoint obligation push, generic in the morphism.**  Every
endpoint is typed at the FIXED `carrier` classifier; under the action the target
endpoints are typed at the transported carrier, which is exactly what the source-endpoint
typings supply — no closed-cell rewrite needed.  Same spine recursion as the flat push. -/
theorem termIndexedEndpointObligations_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope) (carrier : RawTerm sourceScope) :
    ∀ {shifts : List Nat} (children : RawTermChildren shifts sourceScope),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ termIndexedEndpointObligations profile sourceContext carrier children →
        HasTypeUnion profile targetContext (RawTerm.applyMorphism morphism subject)
          (RawTerm.applyMorphism morphism classifier)) →
      ∀ targetObligation ∈ termIndexedEndpointObligations profile targetContext
          (RawTerm.applyMorphism morphism carrier)
          (RawTermChildren.applyMorphism morphism children),
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro shifts
  induction shifts with
  | nil =>
      intro children _sourceTypings targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children sourceTypings targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases targetMember with
              | head =>
                  exact sourceTypings childHead carrier (List.Mem.head _)
              | tail _ tailMember =>
                  exact ih childTail
                    (fun subject classifier member =>
                      sourceTypings subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ => cases targetMember

/-- ★ **The cumulative-family obligation push, generic in the morphism.**  Dispatches on
the children spine (the binder-shape Pi/Sigma spine vs the element-shape List/Option
spine).  Condition-AGNOSTIC: two plain typing functions, no substituent condition baked
in.  `baseTypings` discharges the base (ambient-scope) obligations — domain / element —
via the generic closed-cell rewrite; `crossingTypings` discharges the Pi/Sigma
BINDER-CROSSING codomain obligation at `sourceScope + 1`, supplied under the LIFTED
morphism (`iterateLiftRaw morphism 1`) and the transported domain-extended context. -/
theorem cumulativeFormationObligations_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile targetContext (RawTerm.applyMorphism morphism subject)
          (RawTerm.applyMorphism morphism classifier)) →
      (∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
        ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile (targetContext.cons (RawTerm.applyMorphism morphism domain))
          (RawTerm.applyMorphism (iterateLiftRaw morphism 1) subject)
          (RawTerm.applyMorphism (iterateLiftRaw morphism 1) classifier)) →
      ∀ targetObligation ∈ cumulativeFormationObligations profile targetContext flag
          (RawTermChildren.applyMorphism morphism children) levels,
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro binderShifts children levels baseTypings crossingTypings targetObligation targetMember
  -- Mirror `cumulativeFormationObligations`'s spine dispatch so the transported list reduces.
  match binderShifts, children, levels with
  | _, .childNil, _ => cases targetMember
  -- Element spine, levels exhausted: the FORCED `headChild : Type@0` obligation.
  | _, .childCons (shift := 0) headChild .childNil, [] =>
      cases targetMember with
      | head =>
          have elementTyped := baseTypings headChild (universeCodeCell LevelExpr.lzero flag)
            (List.Mem.head _)
          rwa [applyMorphism_universeCodeCell] at elementTyped
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) headChild .childNil, elementLevel :: _ =>
      cases targetMember with
      | head =>
          have elementTyped := baseTypings headChild (universeCodeCell elementLevel flag)
            (List.Mem.head _)
          rwa [applyMorphism_universeCodeCell] at elementTyped
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil),
      domainLevel :: codomainLevel :: _ =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell domainLevel flag)
            (List.Mem.head _)
          rwa [applyMorphism_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              -- The binder-crossing codomain: supplied at the lifted morphism + extended context.
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell codomainLevel flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [applyMorphism_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  -- Pi / Sigma spine, levels exhausted / too short: the FORCED domain + codomain at `Type@0`.
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [] =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell LevelExpr.lzero flag)
            (List.Mem.head _)
          rwa [applyMorphism_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell LevelExpr.lzero flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [applyMorphism_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [_] =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell LevelExpr.lzero flag)
            (List.Mem.head _)
          rwa [applyMorphism_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell LevelExpr.lzero flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [applyMorphism_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 1) _ (.childCons _ _)), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 0) _ _), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := _ + 2) _ _), _ => cases targetMember
  | _, .childCons (shift := _ + 1) _ _, _ => cases targetMember

/-- ★ **The unified formation-obligation push, generic in the morphism** — the single
content behind `FormationRule.obligations_pushSubst` / `FormationRule.obligations_pushRename`,
dispatched by family.  Condition-AGNOSTIC: `baseTypings` supplies each base (ambient-scope)
source obligation's typing under the action, `crossingTypings` the cumulative Pi/Sigma
codomain at `sourceScope + 1` under the LIFTED action.  Base types demand nothing; flat
formers route through `flatFormationObligations_pushMorphism`; term-indexed formers
discharge the carrier at the universe code and the endpoints through
`termIndexedEndpointObligations_pushMorphism`; cumulative formers route through
`cumulativeFormationObligations_pushMorphism`.  No telescope, no host reflection — covers
every present and future formation former, at every present and future action, by the
generic spine recursion. -/
theorem FormationRule.obligations_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat} (rule : FormationRule)
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope)
    {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
    (levels : List LevelExpr) (carrier : RawTerm sourceScope) (level : LevelExpr)
    (flag : UniverseFlag)
    (baseTypings : ∀ (subject classifier : RawTerm sourceScope),
      ({ scope := sourceScope, context := sourceContext, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      HasTypeUnion profile targetContext (RawTerm.applyMorphism morphism subject)
        (RawTerm.applyMorphism morphism classifier))
    (crossingTypings : ∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
      ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      HasTypeUnion profile (targetContext.cons (RawTerm.applyMorphism morphism domain))
        (RawTerm.applyMorphism (iterateLiftRaw morphism 1) subject)
        (RawTerm.applyMorphism (iterateLiftRaw morphism 1) classifier)) :
    ∀ targetObligation ∈ rule.obligations profile targetContext
        (RawTermChildren.applyMorphism morphism children) levels
        (RawTerm.applyMorphism morphism carrier) level flag,
      HasTypeUnion profile targetObligation.context targetObligation.subject
        targetObligation.classifier := by
  cases rule with
  | baseType baseRule =>
      intro targetObligation targetMember
      cases targetMember
  | flat flatRule =>
      exact flatFormationObligations_pushMorphism targetContext morphism flag children levels
        baseTypings
  | cumulative cumulativeRule =>
      exact cumulativeFormationObligations_pushMorphism targetContext morphism flag
        children levels baseTypings crossingTypings
  | termIndexed termRule =>
      cases children with
      | childNil =>
          intro targetObligation targetMember
          cases targetMember
      | childCons carrierHead rest =>
          rename_i carrierShift _restShifts
          cases carrierShift with
          | zero =>
              intro targetObligation targetMember
              cases targetMember with
              | head =>
                  have carrierTyped := baseTypings carrierHead (universeCodeCell level flag)
                    (List.Mem.head _)
                  rwa [applyMorphism_universeCodeCell] at carrierTyped
              | tail _ tailMember =>
                  exact termIndexedEndpointObligations_pushMorphism targetContext morphism carrier rest
                    (fun subject classifier member =>
                      baseTypings subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ =>
              intro targetObligation targetMember
              cases targetMember

end FX1Poly.Typed
