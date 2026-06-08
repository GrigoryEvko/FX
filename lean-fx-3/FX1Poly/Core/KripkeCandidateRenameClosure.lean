import FX1Poly.Core.StratifiedReducibleType
import FX1Poly.Core.StrongNormalizationApplication
import FX1Poly.Core.StrongNormalizationRename
import FX1Poly.Core.StepRename
import FX1Poly.Core.StepRenameReflectAssembly
import FX1Poly.Core.NeutralTermRename
import FX1Poly.Core.StepInversion
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # Foundation/PolyCell/Core/KripkeCandidateRenameClosure
    — Kripke-indexed reducibility candidates make arrow rename-closure DEFINITIONAL

## The obstruction this resolves

The stratified `ReducibleTypeStep.piType` arm's arrow candidate quantifies over SAME-scope arguments:

  `fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate argument (app functionTerm argument)`.

Renaming `ρ : scope → scope'` ENLARGES the scope, so rebuilding the arm at `scope'` demands the codomain
reducible under EVERY `scope'`-argument — including fresh-variable arguments outside `rename ρ`'s image,
which the inner induction hypothesis cannot supply.  This is the precise wall blocking reducibility
closed under renaming at the `piType` arm.  See `StratifiedReducibleTypeRename` for the obstruction
write-up.

CALIBRATION: the non-Kripke arrow candidate causes TWO distinct obstructions, and this
proof of concept addresses only the FIRST.  (1) The RENAME obstruction, resolved by Kripke-indexing over future
renamings — what this file builds.  (2) The FUEL-STABILITY obstruction (one-level reducibility → all-levels),
which is the actual gate on whole-relation strong normalization: it is exactly the premise
`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`
(`FundamentalWithTypeValueCandidates.lean`), and candidate rename-closure does NOT discharge it.  A FULL
Kripke refactor quantifies the arrow over future renamings AND future fuel (Abel/Adjedj); this
proof of concept does the renaming dimension only.  The env-based fundamental-theorem route
(`ReducibleEnvAtAllLevels`) sidesteps candidate rename-closure altogether — so renaming-closure is
OFF that critical path.  Net: finishing this proof of concept's CR bundle is a sound standalone construction
that does not by itself unblock whole-relation strong normalization.

## The Kripke resolution (validated here)

The standard fix (Abel/Adjedj NbE logical relations) Kripke-indexes the candidate: a candidate at
`sourceScope` becomes a renaming-indexed family `KripkeCand sourceScope`, and the arrow quantifies over a
FURTHER renaming before the argument.  Renaming a Kripke candidate is then PRECOMPOSITION on the index
(`KripkeCand.transport`), and the arrow's rename-closure becomes pure composition-associativity on that
index — which is DEFINITIONAL here because `RawRenaming = Fin → Fin` (a plain function), so renaming
composition is function composition and its associativity holds by `rfl`.

This file is the standalone, zero-axiom PROOF OF CONCEPT of that resolution: the renaming-indexed candidate
family, its transport, the presheaf functoriality law `transport_transport_pointwise`, the non-dependent
Kripke arrow `kripkeArrow`, and the headline `kripkeArrow_transport_pointwise` — the arrow rename-closure
that the non-Kripke `piType` arm CANNOT prove, here closing by `Iff.rfl`.

## Scope (honest boundary)

This is the NON-DEPENDENT arrow proof of concept, NOT wired into `ReducibleTypeStep`.  The
(large, foundational) refactor to actually unblock whole-relation strong normalization is: (1) the dependent
Kripke arrow (codomain indexed by the argument), (2) the reducibility-candidate bundle (CR1/CR2/CR3) for the
Kripke arrow, (3) re-indexing `ReducibleTypeStep` / `ReducibleTypeAt` over Kripke candidates, (4) re-threading the
fundamental theorem.  This seed proves the KEY enabling fact — that Kripke-indexing trivializes
rename-closure — so step (3)'s `piType` rename arm discharges definitionally rather than hitting the wall.

## Scope: the non-dependent arrow CR bundle COMPLETE (CR1/CR2/CR3)

Shipped + gated, all zero-axiom: rename-closure (`Iff.rfl`), presheaf functoriality, the dependent Kripke
arrow, CR1 (`kripkeArrow_stronglyNormalizing` / `kripkeArrowDep_stronglyNormalizing`), CR2
(`kripkeArrow_forwardStep` / `kripkeArrowDep_forwardStep`), and now CR3 — the neutral backward closure
(Girard's hard arrow case) — for the non-dependent arrow, `kripkeArrow_neutralBackwardClosure` below.  CR3
was the PAUSED brick: it needs the full-`Step` rename-reflection-with-image
`Step (rename ρ f) h → ∃ f', Step f f' ∧ rename ρ f' = h` for the neutral-head case, which is now shipped as
`Step.reflectRename` (`StepRenameReflectAssembly.lean`).  With it, the non-dependent Kripke arrow's
reducibility-candidate bundle is complete.  The DEPENDENT-arrow CR3 (`kripkeArrowDep`) is deferred — its
argument-dependent codomain family needs an extra family-coherence hypothesis across argument steps.

Per the CALIBRATION above, completing CR3 unblocks nothing downstream (whole-relation strong normalization
is gated on the SEPARATE fuel-stability premise, and the env-based fundamental-theorem route sidesteps it).
This file is a self-contained construction of standalone candidate rename-closure; the dependent/fuel-indexed
Kripke refactor is a separate, deliberately-scoped development.

## Zero-axiom verification

Both laws close by `Iff.rfl` (definitional composition-associativity on `RawRenaming = Fin → Fin`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (verified by
`#print axioms` in scratch before landing).  Gated per declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **A Kripke-indexed reducibility candidate at `sourceScope`.**  Unlike a plain `RawTerm sourceScope →
Prop`, a Kripke candidate is a renaming-indexed family: at each renaming `ρ : sourceScope → targetScope`
it gives a predicate on `RawTerm targetScope`.  The renaming index is precisely what the non-Kripke
`ReducibleTypeStep.piType` arrow candidate lacks. -/
def KripkeCand (sourceScope : Nat) :=
  ∀ {targetScope : Nat}, RawRenaming sourceScope targetScope → RawTerm targetScope → Prop

/-- **Renaming transport of a Kripke candidate, by precomposition on the index.**  Transporting along
`forwardRenaming : sourceScope → renamedScope` precomposes it onto the candidate's own index renaming —
the presheaf restriction map.  This is what makes rename-closure of derived candidates (the arrow below)
reduce to composition-associativity. -/
def KripkeCand.transport {sourceScope renamedScope : Nat}
    (forwardRenaming : RawRenaming sourceScope renamedScope) (candidate : KripkeCand sourceScope) :
    KripkeCand renamedScope :=
  fun {_targetScope} indexRenaming term =>
    candidate (RawRenaming.compose forwardRenaming indexRenaming) term

/-- **Transport is functorial (presheaf law), pointwise.**  Transporting along `firstRenaming` then
`secondRenaming` equals transporting along their composite — because the index becomes
`firstRenaming ; (secondRenaming ; indexRenaming)` versus `(firstRenaming ; secondRenaming) ; indexRenaming`,
equal by definitional composition-associativity (`RawRenaming = Fin → Fin`). -/
theorem transport_transport_pointwise {sourceScope middleScope renamedScope : Nat}
    (firstRenaming : RawRenaming sourceScope middleScope)
    (secondRenaming : RawRenaming middleScope renamedScope)
    (candidate : KripkeCand sourceScope)
    {targetScope : Nat} (indexRenaming : RawRenaming renamedScope targetScope)
    (term : RawTerm targetScope) :
    KripkeCand.transport secondRenaming (KripkeCand.transport firstRenaming candidate)
        indexRenaming term ↔
      KripkeCand.transport (RawRenaming.compose firstRenaming secondRenaming) candidate
        indexRenaming term :=
  Iff.rfl

/-- **The non-dependent Kripke arrow candidate.**  A function term lies in the arrow at index renaming
`indexRenaming` when, for every FURTHER renaming `furtherRenaming` and argument in the domain candidate at
the composite index, the renamed application lands in the codomain candidate at the composite index.  The
"further renaming" quantifier is the Kripke move that makes the arrow rename-stable. -/
def kripkeArrow {sourceScope : Nat} (domainCandidate codomainCandidate : KripkeCand sourceScope) :
    KripkeCand sourceScope :=
  fun {_targetScope} indexRenaming functionTerm =>
    ∀ {argScope : Nat} (furtherRenaming : RawRenaming _targetScope argScope) (argument : RawTerm argScope),
      domainCandidate (RawRenaming.compose indexRenaming furtherRenaming) argument →
      codomainCandidate (RawRenaming.compose indexRenaming furtherRenaming)
        (.mkGen .gen_app ()
          (.childCons (RawTerm.rename furtherRenaming functionTerm) (.childCons argument .childNil)))

/-- **The Kripke arrow is closed under renaming, DEFINITIONALLY (headline).**  Transporting the arrow along
`forwardRenaming` equals the arrow of the transported domain / codomain.  This is the property whose
non-Kripke analogue is the unprovable `piType` rename arm — here it closes by `Iff.rfl`, because the
renaming threads through purely as composition-associativity on the candidate index.  Concretely both sides
quantify `∀ furtherRenaming argument, domain (...) → codomain (...)` with index
`(forwardRenaming ; indexRenaming) ; furtherRenaming` on the left and
`forwardRenaming ; (indexRenaming ; furtherRenaming)` on the right — definitionally equal. -/
theorem kripkeArrow_transport_pointwise {sourceScope renamedScope : Nat}
    (forwardRenaming : RawRenaming sourceScope renamedScope)
    (domainCandidate codomainCandidate : KripkeCand sourceScope)
    {targetScope : Nat} (indexRenaming : RawRenaming renamedScope targetScope)
    (functionTerm : RawTerm targetScope) :
    KripkeCand.transport forwardRenaming (kripkeArrow domainCandidate codomainCandidate)
        indexRenaming functionTerm ↔
      kripkeArrow (KripkeCand.transport forwardRenaming domainCandidate)
        (KripkeCand.transport forwardRenaming codomainCandidate) indexRenaming functionTerm :=
  Iff.rfl

/-! ## The DEPENDENT Kripke arrow (the Pi case FX actually needs)

The `ReducibleTypeStep.piType` arm is DEPENDENT: the codomain candidate is evaluated at the argument
(`Πx:A. B x`).  The codomain is therefore a family indexed by renaming AND argument; the dependent arrow's
rename-closure is STILL definitional, the argument riding along the same composition-associativity. -/

/-- A codomain candidate FAMILY at `sourceScope`: indexed by renaming AND argument (the dependency of a
dependent-product codomain). -/
def KripkeCodFamily (sourceScope : Nat) :=
  ∀ {targetScope : Nat},
    RawRenaming sourceScope targetScope → RawTerm targetScope → RawTerm targetScope → Prop

/-- Renaming transport of a codomain family, by precomposition on the index (the argument rides along). -/
def KripkeCodFamily.transport {sourceScope renamedScope : Nat}
    (forwardRenaming : RawRenaming sourceScope renamedScope) (family : KripkeCodFamily sourceScope) :
    KripkeCodFamily renamedScope :=
  fun {_targetScope} indexRenaming argument term =>
    family (RawRenaming.compose forwardRenaming indexRenaming) argument term

/-- Codomain-family transport is functorial (presheaf law), pointwise — definitional composition
associativity, the argument inert. -/
theorem codFamily_transport_transport_pointwise {sourceScope middleScope renamedScope : Nat}
    (firstRenaming : RawRenaming sourceScope middleScope)
    (secondRenaming : RawRenaming middleScope renamedScope)
    (family : KripkeCodFamily sourceScope)
    {targetScope : Nat} (indexRenaming : RawRenaming renamedScope targetScope)
    (argument term : RawTerm targetScope) :
    KripkeCodFamily.transport secondRenaming (KripkeCodFamily.transport firstRenaming family)
        indexRenaming argument term ↔
      KripkeCodFamily.transport (RawRenaming.compose firstRenaming secondRenaming) family
        indexRenaming argument term :=
  Iff.rfl

/-- **The dependent Kripke arrow (dependent-product candidate).**  A function term lies in the dependent
arrow at index `indexRenaming` when, for every further renaming and argument in the domain candidate at the
composite index, the renamed application lands in the codomain FAMILY evaluated AT THAT ARGUMENT at the
composite index. -/
def kripkeArrowDep {sourceScope : Nat}
    (domainCandidate : KripkeCand sourceScope) (codomainFamily : KripkeCodFamily sourceScope) :
    KripkeCand sourceScope :=
  fun {_targetScope} indexRenaming functionTerm =>
    ∀ {argScope : Nat} (furtherRenaming : RawRenaming _targetScope argScope) (argument : RawTerm argScope),
      domainCandidate (RawRenaming.compose indexRenaming furtherRenaming) argument →
      codomainFamily (RawRenaming.compose indexRenaming furtherRenaming) argument
        (.mkGen .gen_app ()
          (.childCons (RawTerm.rename furtherRenaming functionTerm) (.childCons argument .childNil)))

/-- **The dependent Kripke arrow is closed under renaming, definitionally.**  The dependent-product
(`Pi`) generalization of `kripkeArrow_transport_pointwise` — the exact rename-closure the dependent
`ReducibleTypeStep.piType` arm requires, here again `Iff.rfl` by composition-associativity (the argument
and codomain dependency ride along inertly). -/
theorem kripkeArrowDep_transport_pointwise {sourceScope renamedScope : Nat}
    (forwardRenaming : RawRenaming sourceScope renamedScope)
    (domainCandidate : KripkeCand sourceScope) (codomainFamily : KripkeCodFamily sourceScope)
    {targetScope : Nat} (indexRenaming : RawRenaming renamedScope targetScope)
    (functionTerm : RawTerm targetScope) :
    KripkeCand.transport forwardRenaming (kripkeArrowDep domainCandidate codomainFamily)
        indexRenaming functionTerm ↔
      kripkeArrowDep (KripkeCand.transport forwardRenaming domainCandidate)
        (KripkeCodFamily.transport forwardRenaming codomainFamily) indexRenaming functionTerm :=
  Iff.rfl

/-! ## CR1 for the Kripke arrow — members are strongly normalizing

The first reducibility-candidate property (CR1) of the Kripke arrow, the SUBSTANTIVE payoff of the seed
(not a definitional `Iff.rfl`).  The classical Tait argument: a function `f` in the arrow at the identity
renaming, applied (via the weakening renaming) to the fresh variable `var 0` — which the domain candidate
contains by hypothesis — lands in the codomain candidate; codomain-CR1 makes that application strongly
normalizing; `isStronglyNormalizing_of_appFunction` descends SN to the renamed function `rename weaken f`;
and `isStronglyNormalizing_of_rename` (reverse rename-SN) descends it to `f`.  The renaming index threads
as `compose identity weaken = weaken` definitionally, so the hypotheses apply directly. -/

/-- **CR1 for the non-dependent Kripke arrow.**  A member of `kripkeArrow` at the identity renaming is
strongly normalizing, given the domain candidate contains the fresh variable (at the weakening renaming)
and the codomain candidate's members are strongly normalizing. -/
theorem kripkeArrow_stronglyNormalizing {scope : Nat}
    {domainCandidate codomainCandidate : KripkeCand scope} {functionTerm : RawTerm scope}
    (domainContainsFreshVariable :
      domainCandidate RawRenaming.weaken (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil))
    (codomainMembersStronglyNormalizing :
      ∀ {targetScope : Nat} (indexRenaming : RawRenaming scope targetScope) (term : RawTerm targetScope),
        codomainCandidate indexRenaming term → IsStronglyNormalizing term)
    (membership : kripkeArrow domainCandidate codomainCandidate RawRenaming.identity functionTerm) :
    IsStronglyNormalizing functionTerm :=
  isStronglyNormalizing_of_rename RawRenaming.weaken
    (isStronglyNormalizing_of_appFunction
      (codomainMembersStronglyNormalizing _ _
        (membership RawRenaming.weaken (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
          domainContainsFreshVariable)))

/-- **CR1 for the dependent Kripke arrow.**  The dependent-product (`Pi`) generalization: same Tait
argument, with the codomain family evaluated at the fresh variable.  This is the CR1 the dependent
`ReducibleTypeStep.piType` arm will require once the candidate layer is Kripke-indexed. -/
theorem kripkeArrowDep_stronglyNormalizing {scope : Nat}
    {domainCandidate : KripkeCand scope} {codomainFamily : KripkeCodFamily scope}
    {functionTerm : RawTerm scope}
    (domainContainsFreshVariable :
      domainCandidate RawRenaming.weaken (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil))
    (codomainMembersStronglyNormalizing :
      ∀ {targetScope : Nat} (indexRenaming : RawRenaming scope targetScope)
        (argument term : RawTerm targetScope),
        codomainFamily indexRenaming argument term → IsStronglyNormalizing term)
    (membership : kripkeArrowDep domainCandidate codomainFamily RawRenaming.identity functionTerm) :
    IsStronglyNormalizing functionTerm :=
  isStronglyNormalizing_of_rename RawRenaming.weaken
    (isStronglyNormalizing_of_appFunction
      (codomainMembersStronglyNormalizing _ _ _
        (membership RawRenaming.weaken (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
          domainContainsFreshVariable)))

/-! ## CR2 for the Kripke arrow — forward closure under `Step`

A member of the Kripke arrow that takes a `Step` is again a member.  For any further renaming and domain
argument, the original member lands in the codomain; the function-step renames (`Step.rename`) and lifts to
an application step (`appFunctionCongStep`); codomain-CR2 carries the codomain membership forward.  The
renaming index is unchanged throughout, so this is a direct composition (no associativity juggling). -/

/-- **CR2 for the non-dependent Kripke arrow.**  `Step functionTerm functionTerm'` carries arrow membership
forward, given the codomain candidate is closed under `Step`. -/
theorem kripkeArrow_forwardStep {scope : Nat}
    {domainCandidate codomainCandidate : KripkeCand scope}
    (codomainClosedUnderStep :
      ∀ {targetScope : Nat} (indexRenaming : RawRenaming scope targetScope)
        {term term' : RawTerm targetScope},
        codomainCandidate indexRenaming term → Step term term' → codomainCandidate indexRenaming term')
    {targetScope : Nat} {indexRenaming : RawRenaming scope targetScope}
    {functionTerm functionTerm' : RawTerm targetScope}
    (functionStep : Step functionTerm functionTerm')
    (membership : kripkeArrow domainCandidate codomainCandidate indexRenaming functionTerm) :
    kripkeArrow domainCandidate codomainCandidate indexRenaming functionTerm' := by
  intro _argScope furtherRenaming argument domainMember
  exact codomainClosedUnderStep _
    (membership furtherRenaming argument domainMember)
    (appFunctionCongStep (Step.rename furtherRenaming functionStep))

/-- **CR2 for the dependent Kripke arrow.**  The dependent-product generalization; codomain-CR2 holds at
each fixed argument. -/
theorem kripkeArrowDep_forwardStep {scope : Nat}
    {domainCandidate : KripkeCand scope} {codomainFamily : KripkeCodFamily scope}
    (codomainClosedUnderStep :
      ∀ {targetScope : Nat} (indexRenaming : RawRenaming scope targetScope)
        (argument : RawTerm targetScope) {term term' : RawTerm targetScope},
        codomainFamily indexRenaming argument term → Step term term' →
          codomainFamily indexRenaming argument term')
    {targetScope : Nat} {indexRenaming : RawRenaming scope targetScope}
    {functionTerm functionTerm' : RawTerm targetScope}
    (functionStep : Step functionTerm functionTerm')
    (membership : kripkeArrowDep domainCandidate codomainFamily indexRenaming functionTerm) :
    kripkeArrowDep domainCandidate codomainFamily indexRenaming functionTerm' := by
  intro _argScope furtherRenaming argument domainMember
  exact codomainClosedUnderStep _ argument
    (membership furtherRenaming argument domainMember)
    (appFunctionCongStep (Step.rename furtherRenaming functionStep))

/-! ## CR3 for the Kripke arrow — neutral backward closure (Girard's hard arrow case)

The third reducibility-candidate property: a NEUTRAL function term whose every one-step `Step`-reduct is
already in the arrow is itself in the arrow.  This was the PAUSED brick — it needs the full arbitrary-renaming
`Step` reflection-with-image `Step (rename ρ f) h → ∃ f', Step f f' ∧ rename ρ f' = h`
(`Step.reflectRename`, `StepRenameReflectAssembly.lean`) for the neutral-head case, now shipped.

The classical Tait/Girard argument, run under the Kripke index: to show `app (rename furtherRenaming
functionTerm) argument` lands in the codomain at the composite index, observe the application is NEUTRAL
(`IsNeutral.app` of the renamed neutral head, `IsNeutral.rename`), so codomain-CR3 reduces it to: every
`Step`-reduct of the application is in the codomain.  `Step.from_app` splits those reducts three ways — β
(impossible: a neutral head is never a λ, `IsNeutral.not_lam`), a HEAD step, or an ARGUMENT step:

  * **Head step** `app N argument ↝ app N' argument` with `Step N N'` (`N = rename furtherRenaming
    functionTerm`): `Step.reflectRename furtherRenaming` pulls the renamed-head step back to a source step
    `Step functionTerm sourceReduct` with `rename furtherRenaming sourceReduct = N'`; the all-reducts
    hypothesis puts `sourceReduct` in the arrow, whose membership applied at `furtherRenaming` / `argument`
    lands `app N' argument` in the codomain.  THIS is the use of the reflection.
  * **Argument step** `app N argument ↝ app N argument'` with `Step argument argument'`: an inner
    accessibility (Tait) induction on the argument's strong normalization — the argument is SN by domain-CR1,
    `argument'` stays in the domain by domain-CR2, and the inner IH lands `app N argument'` in the codomain.

This COMPLETES the non-dependent Kripke arrow's reducibility-candidate bundle (CR1 `kripkeArrow_stronglyNormalizing`,
CR2 `kripkeArrow_forwardStep`, CR3 here) — a self-contained construction.  Per the CALIBRATION at the top of
this file it does not by itself unblock whole-relation strong normalization (that is gated on the separate
fuel-stability premise, and the env-based fundamental-theorem route sidesteps candidate rename-closure); it is
a prerequisite ingredient for the open-context (Kripke) logical relation that the `GrownCtxConv-5` (#842)
context-conversion `piElim` residual requires.  The DEPENDENT-arrow CR3 (`kripkeArrowDep`) is deferred: its
argument-dependent codomain family needs an extra family-coherence hypothesis across argument steps.

The hypotheses are explicit (matching CR1/CR2's style) rather than packaged as a `KripkeCand`-is-a-candidate
bundle: domain members are strongly normalizing (CR1), the domain is `Step`-closed (CR2), the codomain has its
own neutral backward closure (CR3), all at the composite index, plus the all-reducts-in-arrow premise. -/

/-- **CR3 for the non-dependent Kripke arrow** — neutral backward closure.  A neutral `functionTerm` all of
whose `Step`-reducts are in the arrow at `indexRenaming` is itself in the arrow at `indexRenaming`, given the
domain's CR1 (members strongly normalizing) and CR2 (`Step`-closure) and the codomain's own CR3, all at the
composite index.  The head-step case consumes `Step.reflectRename`; the argument-step case runs the inner Tait
accessibility induction on the (domain-CR1) strongly-normalizing argument. -/
theorem kripkeArrow_neutralBackwardClosure {scope : Nat}
    {domainCandidate codomainCandidate : KripkeCand scope}
    {targetScope : Nat} {indexRenaming : RawRenaming scope targetScope}
    {functionTerm : RawTerm targetScope}
    (functionNeutral : IsNeutral functionTerm)
    (domainMembersStronglyNormalizing :
      ∀ {argScope : Nat} (furtherRenaming : RawRenaming targetScope argScope)
        (argument : RawTerm argScope),
        domainCandidate (RawRenaming.compose indexRenaming furtherRenaming) argument →
          IsStronglyNormalizing argument)
    (domainClosedUnderStep :
      ∀ {argScope : Nat} (furtherRenaming : RawRenaming targetScope argScope)
        {argument argument' : RawTerm argScope},
        domainCandidate (RawRenaming.compose indexRenaming furtherRenaming) argument →
          Step argument argument' →
            domainCandidate (RawRenaming.compose indexRenaming furtherRenaming) argument')
    (codomainNeutralBackwardClosure :
      ∀ {argScope : Nat} (furtherRenaming : RawRenaming targetScope argScope)
        (neutralTerm : RawTerm argScope),
        IsNeutral neutralTerm →
        (∀ reduct : RawTerm argScope, Step neutralTerm reduct →
            codomainCandidate (RawRenaming.compose indexRenaming furtherRenaming) reduct) →
          codomainCandidate (RawRenaming.compose indexRenaming furtherRenaming) neutralTerm)
    (reductsInArrow :
      ∀ functionReduct : RawTerm targetScope, Step functionTerm functionReduct →
        kripkeArrow domainCandidate codomainCandidate indexRenaming functionReduct) :
    kripkeArrow domainCandidate codomainCandidate indexRenaming functionTerm := by
  intro argScope furtherRenaming argument domainMember
  have renamedFunctionNeutral : IsNeutral (RawTerm.rename furtherRenaming functionTerm) :=
    IsNeutral.rename furtherRenaming functionNeutral
  suffices general :
      ∀ {currentArgument : RawTerm argScope}, Acc StepSuccessor currentArgument →
        domainCandidate (RawRenaming.compose indexRenaming furtherRenaming) currentArgument →
          codomainCandidate (RawRenaming.compose indexRenaming furtherRenaming)
            (.mkGen .gen_app ()
              (.childCons (RawTerm.rename furtherRenaming functionTerm)
                (.childCons currentArgument .childNil))) from
    general (domainMembersStronglyNormalizing furtherRenaming argument domainMember) domainMember
  intro currentArgument argumentAccessible
  induction argumentAccessible with
  | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
      intro argumentFocusMember
      refine codomainNeutralBackwardClosure furtherRenaming
        (.mkGen .gen_app ()
          (.childCons (RawTerm.rename furtherRenaming functionTerm)
            (.childCons argumentFocus .childNil)))
        (IsNeutral.app renamedFunctionNeutral) ?_
      intro reduct reductionStep
      rcases Step.from_app reductionStep with
        ⟨_body, functionEqualsLam, _targetEq⟩ |
        ⟨functionAfter, reductEquals, functionStep⟩ |
        ⟨argumentAfter, reductEquals, argumentStep⟩
      · exact (IsNeutral.not_lam (functionEqualsLam ▸ renamedFunctionNeutral)).elim
      · obtain ⟨sourceReduct, sourceStep, renameEquation⟩ :=
          Step.reflectRename furtherRenaming functionStep
        rw [reductEquals, ← renameEquation]
        exact reductsInArrow sourceReduct sourceStep furtherRenaming argumentFocus
          argumentFocusMember
      · rw [reductEquals]
        exact argumentInductiveHypothesis argumentAfter argumentStep
          (domainClosedUnderStep furtherRenaming argumentFocusMember argumentStep)

/-! ## The SN Kripke candidate — the Kripke-model interpretation of a NEUTRAL type code

`ReducibleTypeStep.neutral` interprets a weak-head-normal non-Π non-universe type code as the
strong-normalization candidate (`IsStronglyNormalizing`).  Lifting that to the Kripke-indexed setting gives
the index-IGNORING candidate `snKripkeCand`, the Kripke-model neutral-type interpretation.  Its defining
feature — and the reason context conversion is FREE on the semantic side of the open `GrownCtxConv-5` (#842)
type-validity residual — is that it does not consult its renaming index, so transporting it along ANY
renaming (a change of Kripke world = a context conversion) acts as the IDENTITY.  The type-level analogue of
the term-level Kripke-arrow transport laws above, and the Kripke-model home of the firing-15/16 finding that
semantic neutral-type validity is context-free (`neutralTypeCodeSemanticReducibilityIsContextFree`). -/

/-- **The strong-normalization Kripke candidate.**  The index-ignoring Kripke candidate whose members at
every renaming index are exactly the strongly-normalizing terms — the Kripke-model interpretation of a
neutral type code (the `ReducibleTypeStep.neutral` SN candidate, lifted to the renaming-indexed family). -/
def snKripkeCand {scope : Nat} : KripkeCand scope :=
  fun {_targetScope} _indexRenaming term => IsStronglyNormalizing term

/-- **The SN Kripke candidate is rename-INVARIANT (the neutral-type interpretation's context-uniformity).**
Transporting `snKripkeCand` along any `forwardRenaming` leaves it unchanged, pointwise — because it ignores
its index, so precomposing the index with `forwardRenaming` changes nothing.  This is the type-level analogue
of `kripkeArrow_transport_pointwise`: where the arrow's rename-closure threads through as composition-
associativity, the neutral interpretation's is the STRONGER statement that the renaming is invisible entirely
(`Iff.rfl`).  Context conversion (= a change of Kripke index) acts as the identity on the neutral-type
interpretation — the semantic side of the open type-validity residual, free. -/
theorem snKripkeCand_transport_pointwise {scope renamedScope : Nat}
    (forwardRenaming : RawRenaming scope renamedScope)
    {targetScope : Nat} (indexRenaming : RawRenaming renamedScope targetScope)
    (term : RawTerm targetScope) :
    KripkeCand.transport forwardRenaming (snKripkeCand) indexRenaming term ↔
      snKripkeCand indexRenaming term :=
  Iff.rfl

/-- **CR1 for the SN Kripke candidate: its members are strongly normalizing** — definitionally (a member IS
an `IsStronglyNormalizing` witness).  The neutral-type Kripke interpretation trivially satisfies the first
reducibility-candidate property, completing it as a genuine candidate; the Kripke-model analogue of
`ReducibleTypeStep.neutral`'s candidate being `IsStronglyNormalizing`. -/
theorem snKripkeCand_stronglyNormalizing {scope targetScope : Nat}
    (indexRenaming : RawRenaming scope targetScope) {term : RawTerm targetScope}
    (membership : snKripkeCand indexRenaming term) : IsStronglyNormalizing term :=
  membership

end FX1Poly.Core
