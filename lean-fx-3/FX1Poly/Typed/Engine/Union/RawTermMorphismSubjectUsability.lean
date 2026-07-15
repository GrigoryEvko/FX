import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility
import FX1Poly.Typed.Cell.RawTermMorphismCell

/-! # FX1Poly/Typed/Engine/Union/RawTermMorphismSubjectUsability — the use-site usability transport, ONCE

The use-site conjunct's transport (`isSubjectUsableAtModality` survives the action) and the
formation-obligation USABILITY push family used to exist twice: once for renaming
(`HasTypeUnionWeakening`), once for substitution (`HasTypeUnionSubstitution`), identical modulo
the action.  This file states each ONCE, generically over any raw-term morphism (`LiftsRaw` +
`ActsOnRawTermVar`, i.e. exactly `fold`'s two constraints — see `RawTermMorphismCell.lean`), and
the renaming / substitution twins become instantiations at their Container with their EXACT names
and EXACT types preserved.

This is the usability-arm sibling of `RawTermMorphismFormationObligations.lean`, which states the
same family's TYPING push once.

## Why the asymmetry does NOT block this abstraction — and where it reappears

`rename` and `subject` diverge at exactly one datum: `ActsOnRawTermVar.varToRawTerm` re-wraps a
variable for `RawRenaming` but returns an ARBITRARY term for `RawTermSubst`.  The rename twin can
therefore phrase its side condition on the image INDEX (`isAccessibleAtModality (rho index)`,
a `Fin`); the subst twin cannot, and must phrase it on the image TERM
(`isSubjectUsableAtModality (sigma index)`).  Those are different propositions about different
types, which is why the two twins' hypotheses are NOT each other's transport.

The generic resolves this WITHOUT asserting anything about the image's shape: it takes the
SUBJECT-level condition (`variableImagesUsable`: every accessible source variable's image is a
usable SUBJECT) as a hypothesis, phrased at the OPAQUE class datum `varToRawTerm`.  Substitution
satisfies it definitionally (its `varToRawTerm` IS the substituent lookup).  Renaming DISCHARGES
it from its accessibility condition, because a renamed variable is still a variable and
`isSubjectUsableAtModality_var` reduces a variable subject's usability to its index's
accessibility.  Nothing here claims "a morphism maps a variable to a variable" — that claim is
TRUE for rename and FALSE for subst (any substituent sending a variable to a non-variable term
refutes it), so it is never stated; the generic proofs quantify over `Container` opaquely, so it
could not be stated even by accident.

`LiftsRaw` is LAW-FREE (`LiftsRaw.lean`: one field, `liftForRaw`, no equations), so NOTHING about
the LIFTED action's behaviour on variables is derivable generically.  Every binder-crossing step
is therefore taken as a hypothesis (`crossingTransport`), exactly as
`cumulativeFormationObligations_pushMorphism` takes `crossingTypings` — the caller, which knows
its Container, supplies it.

## Zero-axiom verification

Structural recursion over the children spine + `cases` on `List.Mem` constructors (NOT the
`mem_map` / `mem_append` iff lemmas, which leak `propext`) + the generic non-variable cell brick
`RawTerm.applyMorphism_mkGen_of_ne_var`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`, `WellFounded.fix`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Engine/Union/RawTermMorphismSubjectUsability.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- ★ **Subject usability transports along EVERY raw-term morphism whose variable images are
usable.**  The single content behind `subjectUsabilityPreservedUnderRename` /
`subjectUsabilityPreservedUnderSubst`.

A subject is either a variable cell or a non-variable cell.  A non-variable head is preserved by
every morphism (`RawTerm.applyMorphism_mkGen_of_ne_var`), so it stays unconditionally usable via
the modality-independent `else true` branch (`isSubjectUsableAtModality_ofNonVarHead`) — this half
never touches the action.  A variable subject's image is `varToRawTerm morphism index` by
definitional unfolding of the canonical fold's variable case, which `variableImagesUsable`
discharges directly.

The hypothesis is stated at the OPAQUE `varToRawTerm` — it constrains the image's USABILITY, never
its SHAPE, which is precisely why both Containers can satisfy it. -/
theorem subjectUsabilityPreservedUnderMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (morphism : Container sourceScope targetScope) (modality : ObligationModality)
    (variableImagesUsable : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isSubjectUsableAtModality
          (ActsOnRawTermVar.varToRawTerm morphism index) modality = true)
    (subject : RawTerm sourceScope)
    (usable : sourceContext.isSubjectUsableAtModality subject modality = true) :
    targetContext.isSubjectUsableAtModality
      (RawTerm.applyMorphism morphism subject) modality = true := by
  cases subject with
  | mkGen generator payload children =>
      by_cases generatorIsVar : generator = Generator.gen_var
      · subst generatorIsVar
        cases children
        rw [isSubjectUsableAtModality_var] at usable
        exact variableImagesUsable payload usable
      · rw [RawTerm.applyMorphism_mkGen_of_ne_var morphism generatorIsVar]
        exact isSubjectUsableAtModality_ofNonVarHead targetContext generator _ _ modality
          generatorIsVar

/-- ★ **The flat-family obligation-usability push, generic in the morphism.**  The single content
behind `flatFormationObligations_usable_pushRename` / `flatFormationObligations_usable_pushSubst`.
Every flat formation obligation is FIBRANT and lives at the ambient scope, so each transports by
`subjectUsabilityPreservedUnderMorphism` — no binder is crossed, hence no crossing hypothesis.
Generic over the spine (induct on the shape `binderShifts`, `cases` the mutual
`RawTermChildren`) AND over the action. -/
theorem flatFormationObligations_usable_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope) (flag : UniverseFlag)
    (variableImagesUsable : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isSubjectUsableAtModality
          (ActsOnRawTermVar.varToRawTerm morphism index) .fibrant = true) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ flatFormationObligations profile sourceContext flag children levels →
        sourceContext.isSubjectUsableAtModality subject .fibrant = true) →
      ∀ targetObligation ∈ flatFormationObligations profile targetContext flag
          (RawTermChildren.applyMorphism morphism children) levels,
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro children levels _sourceUsable targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children levels sourceUsable targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases levels with
              | nil =>
                  cases targetMember with
                  | head =>
                      exact subjectUsabilityPreservedUnderMorphism morphism .fibrant
                        variableImagesUsable childHead
                        (sourceUsable childHead (universeCodeCell LevelExpr.lzero flag)
                          (List.Mem.head _))
                  | tail _ tailMember =>
                      exact ih childTail []
                        (fun subject classifier member =>
                          sourceUsable subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
              | cons headLevel restLevels =>
                  cases targetMember with
                  | head =>
                      exact subjectUsabilityPreservedUnderMorphism morphism .fibrant
                        variableImagesUsable childHead
                        (sourceUsable childHead (universeCodeCell headLevel flag)
                          (List.Mem.head _))
                  | tail _ tailMember =>
                      exact ih childTail restLevels
                        (fun subject classifier member =>
                          sourceUsable subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
          | succ _ => cases targetMember

/-- ★ **The term-indexed endpoint obligation-usability push, generic in the morphism.**  The single
content behind `termIndexedEndpointObligations_usable_pushRename` /
`termIndexedEndpointObligations_usable_pushSubst`.  Every endpoint is an ambient-context term at
the FIXED `carrier` classifier, hence fibrant and binder-free.  Same spine recursion as the flat
push. -/
theorem termIndexedEndpointObligations_usable_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope) (carrier : RawTerm sourceScope)
    (variableImagesUsable : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isSubjectUsableAtModality
          (ActsOnRawTermVar.varToRawTerm morphism index) .fibrant = true) :
    ∀ {shifts : List Nat} (children : RawTermChildren shifts sourceScope),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ termIndexedEndpointObligations profile sourceContext carrier children →
        sourceContext.isSubjectUsableAtModality subject .fibrant = true) →
      ∀ targetObligation ∈ termIndexedEndpointObligations profile targetContext
          (RawTerm.applyMorphism morphism carrier)
          (RawTermChildren.applyMorphism morphism children),
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro shifts
  induction shifts with
  | nil =>
      intro children _sourceUsable targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children sourceUsable targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases targetMember with
              | head =>
                  exact subjectUsabilityPreservedUnderMorphism morphism .fibrant
                    variableImagesUsable childHead
                    (sourceUsable childHead carrier (List.Mem.head _))
              | tail _ tailMember =>
                  exact ih childTail
                    (fun subject classifier member =>
                      sourceUsable subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ => cases targetMember

/-- ★ **The cumulative-family obligation-usability push, generic in the morphism.**  The single
content behind `cumulativeFormationObligations_usable_pushRename` /
`cumulativeFormationObligations_usable_pushSubst`.  Dispatches on the children spine (the
binder-shape Pi/Sigma spine vs the element-shape List/Option spine).

`baseUsable` discharges the base (ambient-scope) obligations — domain / element — through
`subjectUsabilityPreservedUnderMorphism`; the Pi/Sigma BINDER-CROSSING codomain obligation (at
`sourceContext.cons domain`) is transported by `crossingTransport`, which is a HYPOTHESIS because
`LiftsRaw` carries no laws — nothing about the lifted action's variable behaviour is derivable at
an abstract Container.  Each caller supplies it from its own Container's lifted transport. -/
theorem cumulativeFormationObligations_usable_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope) (flag : UniverseFlag)
    (variableImagesUsable : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isSubjectUsableAtModality
          (ActsOnRawTermVar.varToRawTerm morphism index) .fibrant = true)
    (crossingTransport : ∀ (domain : RawTerm sourceScope) (subject : RawTerm (sourceScope + 1)),
        (sourceContext.cons domain).isSubjectUsableAtModality subject .fibrant = true →
        (targetContext.cons (RawTerm.applyMorphism morphism domain)).isSubjectUsableAtModality
          (RawTerm.applyMorphism (iterateLiftRaw morphism 1) subject) .fibrant = true) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        sourceContext.isSubjectUsableAtModality subject .fibrant = true) →
      (∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
        ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        (sourceContext.cons domain).isSubjectUsableAtModality subject .fibrant = true) →
      ∀ targetObligation ∈ cumulativeFormationObligations profile targetContext flag
          (RawTermChildren.applyMorphism morphism children) levels,
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro binderShifts children levels baseUsable crossingUsable targetObligation targetMember
  match binderShifts, children, levels with
  | _, .childNil, _ => cases targetMember
  | _, .childCons (shift := 0) headChild .childNil, [] =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderMorphism morphism .fibrant variableImagesUsable
            headChild (baseUsable headChild (universeCodeCell LevelExpr.lzero flag)
              (List.Mem.head _))
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) headChild .childNil, elementLevel :: _ =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderMorphism morphism .fibrant variableImagesUsable
            headChild (baseUsable headChild (universeCodeCell elementLevel flag)
              (List.Mem.head _))
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil),
      domainLevel :: codomainLevel :: _ =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderMorphism morphism .fibrant variableImagesUsable
            domain (baseUsable domain (universeCodeCell domainLevel flag) (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact crossingTransport domain codomain
                (crossingUsable domain codomain (universeCodeCell codomainLevel flag)
                  (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [] =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderMorphism morphism .fibrant variableImagesUsable
            domain (baseUsable domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact crossingTransport domain codomain
                (crossingUsable domain codomain (universeCodeCell LevelExpr.lzero flag)
                  (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [_] =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderMorphism morphism .fibrant variableImagesUsable
            domain (baseUsable domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact crossingTransport domain codomain
                (crossingUsable domain codomain (universeCodeCell LevelExpr.lzero flag)
                  (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 1) _ (.childCons _ _)), _ =>
      cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 0) _ _), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := _ + 2) _ _), _ => cases targetMember
  | _, .childCons (shift := _ + 1) _ _, _ => cases targetMember

/-- ★ **The unified formation-rule obligation-USABILITY push, generic in the morphism** — the
single content behind `FormationRule.obligationsUsable_pushRename` /
`FormationRule.obligationsUsable_pushSubst`, dispatched by family.  Base types demand nothing;
flat formers route through `flatFormationObligations_usable_pushMorphism`; term-indexed formers
discharge the carrier at the ambient scope and the endpoints through
`termIndexedEndpointObligations_usable_pushMorphism`; cumulative formers route through
`cumulativeFormationObligations_usable_pushMorphism`, supplying its binder crossing.  No
telescope, no host reflection — covers every present and future formation former, at every present
and future action, by the generic spine recursion. -/
theorem FormationRule.obligationsUsable_pushMorphism {profile : PolyProfile}
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat} (rule : FormationRule)
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (morphism : Container sourceScope targetScope)
    {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
    (levels : List LevelExpr) (carrier : RawTerm sourceScope) (level : LevelExpr)
    (flag : UniverseFlag)
    (variableImagesUsable : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isSubjectUsableAtModality
          (ActsOnRawTermVar.varToRawTerm morphism index) .fibrant = true)
    (crossingTransport : ∀ (domain : RawTerm sourceScope) (subject : RawTerm (sourceScope + 1)),
        (sourceContext.cons domain).isSubjectUsableAtModality subject .fibrant = true →
        (targetContext.cons (RawTerm.applyMorphism morphism domain)).isSubjectUsableAtModality
          (RawTerm.applyMorphism (iterateLiftRaw morphism 1) subject) .fibrant = true)
    (baseUsable : ∀ (subject classifier : RawTerm sourceScope),
      ({ scope := sourceScope, context := sourceContext, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      sourceContext.isSubjectUsableAtModality subject .fibrant = true)
    (crossingUsable : ∀ (domain : RawTerm sourceScope)
        (subject classifier : RawTerm (sourceScope + 1)),
      ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      (sourceContext.cons domain).isSubjectUsableAtModality subject .fibrant = true) :
    ∀ targetObligation ∈ rule.obligations profile targetContext
        (RawTermChildren.applyMorphism morphism children) levels
        (RawTerm.applyMorphism morphism carrier) level flag,
      targetObligation.context.isSubjectUsableAtModality targetObligation.subject
        targetObligation.modality = true := by
  cases rule with
  | baseType baseRule =>
      intro targetObligation targetMember
      cases targetMember
  | flat flatRule =>
      exact flatFormationObligations_usable_pushMorphism targetContext morphism flag
        variableImagesUsable children levels baseUsable
  | cumulative cumulativeRule =>
      exact cumulativeFormationObligations_usable_pushMorphism targetContext morphism flag
        variableImagesUsable crossingTransport children levels baseUsable crossingUsable
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
                  exact subjectUsabilityPreservedUnderMorphism morphism .fibrant
                    variableImagesUsable carrierHead
                    (baseUsable carrierHead (universeCodeCell level flag) (List.Mem.head _))
              | tail _ tailMember =>
                  exact termIndexedEndpointObligations_usable_pushMorphism targetContext morphism
                    carrier variableImagesUsable rest
                    (fun subject classifier member =>
                      baseUsable subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ =>
              intro targetObligation targetMember
              cases targetMember

end FX1Poly.Typed
