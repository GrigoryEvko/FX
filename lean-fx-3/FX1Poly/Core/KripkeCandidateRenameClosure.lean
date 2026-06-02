import FX1Poly.Core.StratifiedReducibleType

/-! # Foundation/PolyCell/Core/KripkeCandidateRenameClosure
    — Kripke-indexed reducibility candidates make arrow rename-closure DEFINITIONAL (SN-043 refactor seed)

## The obstruction this resolves

The stratified `ReducibleTypeStep.piType` arm's arrow candidate quantifies over SAME-scope arguments:

  `fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate argument (app functionTerm argument)`.

Renaming `ρ : scope → scope'` ENLARGES the scope, so rebuilding the arm at `scope'` demands the codomain
reducible under EVERY `scope'`-argument — including fresh-variable arguments outside `rename ρ`'s image,
which the inner induction hypothesis cannot supply.  This is the precise wall blocking SN-040 (reducibility
closed under renaming) at the `piType` arm, and — through the strengthened fundamental theorem's
fuel-stability requirement — the whole unconditional Milestone-A spine (SN-043 SN-for-well-typed, SN-046
typed Newman, SN-047..050 canonicity/consistency).  See `StratifiedReducibleTypeRename` for the obstruction
write-up.

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

This is the NON-DEPENDENT arrow proof of concept, NOT yet wired into `ReducibleTypeStep`.  The remaining
(large, foundational) refactor to actually unblock SN-043 is: (1) the dependent Kripke arrow (codomain
indexed by the argument), (2) the reducibility-candidate bundle (CR1/CR2/CR3) for the Kripke arrow,
(3) re-indexing `ReducibleTypeStep` / `ReducibleTypeAt` over Kripke candidates, (4) re-threading the
fundamental theorem.  This seed proves the KEY enabling fact — that Kripke-indexing trivializes
rename-closure — so step (3)'s `piType` rename arm will discharge definitionally rather than hit the wall.

## Zero-axiom verification

Both laws close by `Iff.rfl` (definitional composition-associativity on `RawRenaming = Fin → Fin`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (verified by
`#print axioms` in scratch before landing).  Gated per declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

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
non-Kripke analogue is the unprovable SN-040 `piType` rename arm — here it closes by `Iff.rfl`, because the
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

end FX1Poly.Core
