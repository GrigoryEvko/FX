import FX1Poly.Core.KripkeCandidateRenameClosure

/-! # FX1Poly/Core/KripkeReducibilityCandidate
    — SN-040, honest unconditional form: a reducibility candidate is closed under renaming

## What SN-040 actually is, honestly

SN-040 ("reducibility closed under renaming") has NO unconditional proof for the bare `ReducibleTypeStep`
relation — it is FALSE there, not merely hard.  The `ReducibleTypeStep.piType` arm's candidate is
`fun f => ∀ argument : RawTerm scope, domainCandidate argument → codomainCandidate argument (app f argument)`,
quantifying over SAME-scope arguments.  A renaming `ρ : scope → scope'` enlarges the scope, and a renamed
Π-type `Π A⟨ρ⟩ B⟨ρ.lift⟩` is reducible only if its codomain is reducible under EVERY `scope'`-argument,
including fresh-variable arguments outside `ρ`'s image — which a source derivation (image arguments only)
cannot supply.  Concretely, a Π-type whose codomain is reducible exactly on `ρ`'s image is reducible at the
source scope but its renaming is genuinely not reducible.  So the bare statement has a real counterexample.

The HONEST unconditional renaming-closure lives one layer up, at the KRIPKE-indexed candidate (Abel/Adjedj
NbE logical relations).  `KripkeCandidateRenameClosure.lean` ships the predicate-level half:
`kripkeArrowDep_transport_pointwise` — the dependent arrow's transport equals the arrow of the transported
domain/codomain, by `Iff.rfl` (the renaming threads as precomposition on the candidate index, definitional on
`RawRenaming = Fin → Fin`).  This file ships the CANDIDATE-level half: the reducibility-candidate PROPERTY
(CR1 members-SN + CR2 closed-under-Step) survives transport along ANY renaming with NO hypothesis.

## Honest boundary

The Kripke candidate is NOT wired into `ReducibleTypeStep` (that is the deliberately-deferred foundational
refactor), and per `KripkeCandidateRenameClosure.lean`'s calibration, candidate rename-closure is OFF the
SN-043 critical path — the gate on SN-043 is the SEPARATE fuel-stability premise
`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` (`FundamentalWithTypeValueCandidates.lean`),
which rename-closure does not discharge.  This file is the honest, unconditional, hypothesis-free statement of
SN-040 in the form in which it is TRUE — the bare-relation form being false.

## Zero-axiom verification

`IsKripkeReducibilityCandidate` is a two-field `Prop` structure; `transport` feeds the composed index renaming
to the original candidate's laws (the transport unfolds to precomposition definitionally).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **A Kripke candidate is a reducibility candidate** when, at every index renaming, its members are strongly
normalizing (CR1) and it is closed under `Step` (CR2).  CR3 (neutral backward closure) is intentionally not a
field here — it is the deferred Girard arrow case (`KripkeCandidateRenameClosure.lean`, PAUSED), and the
renaming-closure of this CR1+CR2 bundle is provable without it. -/
structure IsKripkeReducibilityCandidate {scope : Nat} (candidate : KripkeCand scope) : Prop where
  /-- CR1: members of the candidate (at any index renaming) are strongly normalizing. -/
  membersStronglyNormalizing : ∀ {targetScope : Nat} (indexRenaming : RawRenaming scope targetScope)
    (term : RawTerm targetScope), candidate indexRenaming term → IsStronglyNormalizing term
  /-- CR2: the candidate is closed under `Step` (at any index renaming). -/
  closedUnderStep : ∀ {targetScope : Nat} (indexRenaming : RawRenaming scope targetScope)
    {term term' : RawTerm targetScope}, candidate indexRenaming term → Step term term' →
    candidate indexRenaming term'

/-- **SN-040, honest Kripke form: a reducibility candidate is closed under renaming, UNCONDITIONALLY.**
Transporting a Kripke reducibility candidate along ANY renaming yields a Kripke reducibility candidate — with
NO hypothesis.  The transport precomposes the renaming onto the candidate's own index, so a member of the
transported candidate at index `indexRenaming` is definitionally a member of the original at the composed
index `forwardRenaming ; indexRenaming`; CR1 and CR2 then read off the original candidate's laws at that
composed index.  This is the renaming-closure the bare `ReducibleTypeStep.piType` arm cannot have (its
same-scope argument quantifier makes the bare statement false); the Kripke index makes it free. -/
theorem IsKripkeReducibilityCandidate.transport {sourceScope renamedScope : Nat}
    (forwardRenaming : RawRenaming sourceScope renamedScope)
    {candidate : KripkeCand sourceScope}
    (isCandidate : IsKripkeReducibilityCandidate candidate) :
    IsKripkeReducibilityCandidate (KripkeCand.transport forwardRenaming candidate) := by
  constructor
  · intro _targetScope indexRenaming term membership
    exact isCandidate.membersStronglyNormalizing _ term membership
  · intro _targetScope indexRenaming term term' membership step
    exact isCandidate.closedUnderStep _ membership step

end FX1Poly.Core
