import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFlatFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric
import FX1Poly.Typed.Metatheory.ContextConversion.HasTypeUnionContextConversion

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionCumulativeFormationCongruence
    — the CUMULATIVE (Π/Σ/List/Option) formation obligation transform under a child congruence (gate-2, cumulative arm)

The `formationRule` arm of the generic congruence closer needs, per family, the obligation transform: the
formation obligations at `childrenBefore` all hold + each obligation subject enjoys single-step subject reduction
⟹ every obligation at `childrenAfter` holds.  `flatFormationPremisesHoldAfter` (flat) and
`termIndexedFormationPremisesHoldAfter` (Id/Bridge) ship the easy families; the BASE family is vacuous (no
children); this file ships the LAST, genuinely-hard family — the CUMULATIVE Π/Σ/List/Option formers.

The Π/Σ codes carry a BINDER-CROSSING codomain obligation (`codomain : Type@codomainLevel` over the
domain-EXTENDED context `context.cons domain`).  When the DOMAIN steps, that sibling obligation's CONTEXT drifts
`context.cons domain ⟶ context.cons domain'` — so re-typing the codomain there demands native CONTEXT CONVERSION
(`HasTypeUnion.convertHeadBinding`, the SR-DSL-2 motive-arm unblock).  This was the one formation family the empty
closer's (there vacuous) formationRule arm left for after context conversion shipped; it now closes.

  * **domain steps** — re-type the domain at its universe code (its SR + universe reclassification), and re-home
    the UNCHANGED codomain from `cons domain` to `cons domain'` through `convertHeadBinding` (the domain's
    universe typing is the well-formedness witness; `Conv.fromStep` the binding conversion);
  * **codomain steps** — re-type the codomain at its universe code IN the unchanged `cons domain`, domain
    untouched;
  * **List/Option element steps** — re-type the single element at its universe code (binder-free, like flat).

The cumulative OUTPUT (`Type@level`) is children-invariant, so — as for every formation family — there is no
output drift: the reformed cell keeps its classifier (`Conv.refl` at the gate).

## The recursion driver: `cases childrenAfter` on the SHARED `binderShifts`

A `StepChildren childrenBefore childrenAfter` keeps the spine length, so `childrenAfter` shares `childrenBefore`'s
`binderShifts`.  After `cases childrenBefore` fixes the shape, `cases childrenAfter` concretizes the reduct spine
to the SAME shape WITHOUT touching the obligation membership (kept un-introduced), dodging the dependent-elimination
failure a `cases childStep` over a still-abstract reduct would hit.  With both spines concrete, `cases childStep`
extracts which child stepped (its `here`/`there` unifying the unchanged sibling).

## Zero-axiom verification

`cases childrenAfter` (shared shifts) + the two binder helpers + `reclassifyToType` over `universeFormation`
(universe rigidity), `convertHeadBinding` (the domain-step context drift), `Conv.fromStep`, and
`noStepChildren_childNil` for the impossible steps.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The Π/Σ binder obligations under a DOMAIN step.**  When the domain of a cumulative binder former steps
`domain ⟶ domainAfter`, both obligations re-establish at `domainAfter`: the domain obligation through its subject
reduction + universe reclassification, and the binder-crossing codomain — UNCHANGED but now over the drifted
context `context.cons domainAfter` — through native context conversion (`convertHeadBinding`), with the domain's
own universe typing as the well-formedness witness and `Conv.fromStep` the binding conversion. -/
theorem cumulativeBinderObligationsHoldAfterDomainStep {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    {domain domainAfter : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr)
    (domainStep : Step domain domainAfter)
    (inlineChildSubjectReduction :
      ∀ obligation ∈ cumulativeBinderObligations profile context flag domain codomain
          domainLevel codomainLevel,
        ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
          ∃ pinned : RawTerm obligation.scope,
            HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier)
    (premisesHold : ∀ obligation ∈ cumulativeBinderObligations profile context flag domain codomain
        domainLevel codomainLevel,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ cumulativeBinderObligations profile context flag domainAfter codomain
        domainLevel codomainLevel,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  have domainTyped : HasTypeUnion profile context domain (universeCodeCell domainLevel flag) :=
    premisesHold _ (List.Mem.head _)
  have codomainTyped : HasTypeUnion profile (context.cons domain) codomain
      (universeCodeCell codomainLevel flag) :=
    premisesHold _ (List.Mem.tail _ (List.Mem.head _))
  intro obligation obligationMem
  cases obligationMem with
  | head =>
      obtain ⟨pinned, reductTyped, convPinned⟩ :=
        inlineChildSubjectReduction _ (List.Mem.head _) domainAfter domainStep
      exact HasTypeUnion.reclassifyToType reductTyped convPinned
        ⟨_, _, HasTypeUnion.universeFormation context domainLevel flag⟩
  | tail _ tailMem =>
      cases tailMem with
      | head =>
          exact HasTypeUnion.convertHeadBinding codomainTyped (Conv.fromStep domainStep)
            ⟨domainLevel, flag, domainTyped⟩
      | tail _ emptyMem => cases emptyMem

/-- **The Π/Σ binder obligations under a CODOMAIN step.**  When the codomain steps `codomain ⟶ codomainAfter` in
the domain-extended context, the codomain obligation re-types at its universe code (its SR + universe
reclassification over `context.cons domain`); the domain obligation is untouched. -/
theorem cumulativeBinderObligationsHoldAfterCodomainStep {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    {domain : RawTerm scope} {codomain codomainAfter : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr)
    (codomainStep : Step codomain codomainAfter)
    (inlineChildSubjectReduction :
      ∀ obligation ∈ cumulativeBinderObligations profile context flag domain codomain
          domainLevel codomainLevel,
        ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
          ∃ pinned : RawTerm obligation.scope,
            HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier)
    (premisesHold : ∀ obligation ∈ cumulativeBinderObligations profile context flag domain codomain
        domainLevel codomainLevel,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ cumulativeBinderObligations profile context flag domain codomainAfter
        domainLevel codomainLevel,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  have domainTyped : HasTypeUnion profile context domain (universeCodeCell domainLevel flag) :=
    premisesHold _ (List.Mem.head _)
  have codomainTyped : HasTypeUnion profile (context.cons domain) codomain
      (universeCodeCell codomainLevel flag) :=
    premisesHold _ (List.Mem.tail _ (List.Mem.head _))
  intro obligation obligationMem
  cases obligationMem with
  | head => exact domainTyped
  | tail _ tailMem =>
      cases tailMem with
      | head =>
          obtain ⟨pinned, reductTyped, convPinned⟩ :=
            inlineChildSubjectReduction _ (List.Mem.tail _ (List.Mem.head _)) codomainAfter codomainStep
          exact HasTypeUnion.reclassifyToType reductTyped convPinned
            ⟨_, _, HasTypeUnion.universeFormation (context.cons domain) codomainLevel flag⟩
      | tail _ emptyMem => cases emptyMem

/-- **★ The cumulative-family obligation transform under a child congruence.**  The Π/Σ/List/Option formation
obligations at `childrenBefore` all hold + each enjoys single-step subject reduction ⟹ every obligation at
`childrenAfter` holds.  `cases childrenAfter` (shared `binderShifts`) concretizes the reduct spine; the
List/Option element step re-types the single element (binder-free); the Π/Σ domain step routes through
`cumulativeBinderObligationsHoldAfterDomainStep` (with the codomain context conversion), the codomain step through
`cumulativeBinderObligationsHoldAfterCodomainStep`.  The cumulative sibling of `flatFormationPremisesHoldAfter`. -/
theorem cumulativeFormationPremisesHoldAfter {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    {binderShifts : List Nat} (childrenBefore childrenAfter : RawTermChildren binderShifts scope)
    (childStep : StepChildren childrenBefore childrenAfter) (levels : List LevelExpr)
    (premisesHold : ∀ obligation ∈ cumulativeFormationObligations profile context flag childrenBefore levels,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (inlineChildSubjectReduction :
      ∀ obligation ∈ cumulativeFormationObligations profile context flag childrenBefore levels,
        ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
          ∃ pinned : RawTerm obligation.scope,
            HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier) :
    ∀ obligation ∈ cumulativeFormationObligations profile context flag childrenAfter levels,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  cases childrenBefore with
  | childNil => exact fun _ _ => (StepStar.noStepChildren_childNil childStep).elim
  | childCons firstChild rest =>
    rename_i firstShift _restShifts
    cases childrenAfter with
    | childCons firstChildAfter restAfter =>
      cases firstShift with
      | succ _firstShiftPredecessor =>
          -- first-child shift `_+1`: `cumulativeFormationObligations` is `[]`.
          intro obligation obligationMem; cases obligationMem
      | zero =>
          cases rest with
          | childNil =>
              -- List / Option element-shape spine: `restAfter : RawTermChildren [] → childNil`.
              cases restAfter with
              | childNil =>
                  cases childStep with
                  | @here _ _ _ _ _ _ elementStep =>
                      cases levels with
                      | nil =>
                          intro obligation obligationMem
                          cases obligationMem with
                          | head =>
                              obtain ⟨pinned, reductTyped, convPinned⟩ :=
                                inlineChildSubjectReduction _ (List.Mem.head _) _ elementStep
                              exact HasTypeUnion.reclassifyToType reductTyped convPinned
                                ⟨_, _, HasTypeUnion.universeFormation context LevelExpr.lzero flag⟩
                          | tail _ emptyMem => cases emptyMem
                      | cons elementLevel _restLevels =>
                          intro obligation obligationMem
                          cases obligationMem with
                          | head =>
                              obtain ⟨pinned, reductTyped, convPinned⟩ :=
                                inlineChildSubjectReduction _ (List.Mem.head _) _ elementStep
                              exact HasTypeUnion.reclassifyToType reductTyped convPinned
                                ⟨_, _, HasTypeUnion.universeFormation context elementLevel flag⟩
                          | tail _ emptyMem => cases emptyMem
                  | @there _ _ _ _ _ _ restStep =>
                      exact fun _ _ => (StepStar.noStepChildren_childNil restStep).elim
          | childCons codomain tail =>
            rename_i secondShift _tailShifts
            cases restAfter with
            | childCons codomainAfter tailAfter =>
              cases secondShift with
              | zero =>
                  -- second-child shift `0`: `cumulativeFormationObligations` is `[]`.
                  intro obligation obligationMem; cases obligationMem
              | succ secondShiftPredecessor =>
                  cases secondShiftPredecessor with
                  | succ _ =>
                      -- second-child shift `_+2`: `cumulativeFormationObligations` is `[]`.
                      intro obligation obligationMem; cases obligationMem
                  | zero =>
                      cases tail with
                      | childCons _ _ =>
                          -- shift `1`, non-`childNil` tail: `cumulativeFormationObligations` is `[]`.
                          cases tailAfter with
                          | childCons _ _ => intro obligation obligationMem; cases obligationMem
                      | childNil =>
                          -- genuine Π / Σ binder spine: `[domain, codomain]` at shifts `[0, 1]`.
                          cases tailAfter with
                          | childNil =>
                              cases childStep with
                              | @here _ _ _ _ _ _ domainStep =>
                                  cases levels with
                                  | nil =>
                                      exact cumulativeBinderObligationsHoldAfterDomainStep context flag
                                        LevelExpr.lzero LevelExpr.lzero domainStep inlineChildSubjectReduction
                                        premisesHold
                                  | cons _domainLevel restLevels =>
                                      cases restLevels with
                                      | nil =>
                                          exact cumulativeBinderObligationsHoldAfterDomainStep context flag
                                            LevelExpr.lzero LevelExpr.lzero domainStep inlineChildSubjectReduction
                                            premisesHold
                                      | cons _codomainLevel _ =>
                                          exact cumulativeBinderObligationsHoldAfterDomainStep context flag
                                            _ _ domainStep inlineChildSubjectReduction premisesHold
                              | @there _ _ _ _ _ _ restStep =>
                                  cases restStep with
                                  | @here _ _ _ _ _ _ codomainStep =>
                                      cases levels with
                                      | nil =>
                                          exact cumulativeBinderObligationsHoldAfterCodomainStep context flag
                                            LevelExpr.lzero LevelExpr.lzero codomainStep inlineChildSubjectReduction
                                            premisesHold
                                      | cons _domainLevel restLevels =>
                                          cases restLevels with
                                          | nil =>
                                              exact cumulativeBinderObligationsHoldAfterCodomainStep context
                                                flag LevelExpr.lzero LevelExpr.lzero codomainStep
                                                inlineChildSubjectReduction premisesHold
                                          | cons _codomainLevel _ =>
                                              exact cumulativeBinderObligationsHoldAfterCodomainStep context
                                                flag _ _ codomainStep inlineChildSubjectReduction premisesHold
                                  | @there _ _ _ _ _ _ tailStep =>
                                      exact fun _ _ => (StepStar.noStepChildren_childNil tailStep).elim

end FX1Poly.Typed
