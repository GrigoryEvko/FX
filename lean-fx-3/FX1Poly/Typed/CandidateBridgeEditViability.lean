import FX1Poly.Typed.ConsistencyTargetSignature

/-! # FX1Poly/Typed/CandidateBridgeEditViability
    — the GO certificate for the §5 candidate-bridge model edit (companion to the shipped obstruction)

`ConsistencyTargetSignature.lean` ships the OBSTRUCTION proof
(`emptyTypeCell_candidate_forcedStronglyNormalizing`): under the CURRENT `ReducibleTypeStepBounded`, the
`neutral` arm over-fires on `gen_emptyCode` and `deterministic` then FORCES emptyTypeCell's reducibility
candidate to the whole `IsStronglyNormalizing` set — so the canonicity/consistency `memberBridge` (CON-A3,
#810) is unconditionally FALSE in the model.  The shipped verdict: closing the candidate bridge needs a
STRUCTURAL §5 edit — gate `neutral` with `rootGenerator ≠ gen_emptyCode` and add a dedicated `dataEmpty`
arm pinning data-type codes to their Tait candidates.

The open question that decides whether that edit is VIABLE at all: **does `deterministic` survive the
edit?**  If gating `neutral` and adding `dataEmpty` broke functionality of the reducibility-as-type
relation, the whole approach would be dead (the FT's canonical-candidate reconciliation consumes
determinism).  The only genuinely-new interaction is the `neutral × dataEmpty` cross-case.

This file is the GO certificate: it replays the exact edit on a FAITHFUL MINIATURE of the relation, built
over the REAL `RawTerm` / `Generator` / `WeakHeadStep` / `RawTerm.rootGenerator` / `emptyTypeCell` (so the
rootGenerator facts — `gen_emptyCode ≠ gen_piTyCode`, etc. — are the actual ones and transfer directly),
and PROVES, zero-axiom, that the four load-bearing claims hold:

  * **`deterministic`** — the relation stays functional; the new `neutral × dataEmpty` cross-case is ruled
    out by `notEmpty` (neutral's new gate) contradicting `isEmpty` (dataEmpty's premise).
  * **`emptyCodeCandidateIsEmpty`** — emptyTypeCell now routes through `dataEmpty` to the EMPTY candidate
    (the exact reversal of the SN-forcing the obstruction proves).
  * **`consistencyCore`** — a fundamental-theorem-produced member of emptyTypeCell's candidate yields
    `False`, because that candidate IS the (member-free) empty candidate; the bridge the current model
    blocks becomes provable.
  * **`nonEmptyNeutralStillSN`** — the gating does NOT disturb non-empty neutral codes; every non-data type
    code keeps its SN candidate, so the existing metatheory is preserved.

## What this is and is NOT

This is a DESIGN-VALIDATION certificate for the edit's structure, NOT the model change itself.  It proves
the determinism-survival crux on a miniature; the actual change is the mechanical mirror of this structure
into the real 5-arm `ReducibleTypeStepBounded` + its `ReducibleTypeStepDenote` forget-twin and the ~12
arm-enumerating consumer files (verified census: 4 bounded + 8 denote enumerating files, ~37 case-split
sites, zero wildcard absorption — an all-or-nothing commit).  The intellectual content (does determinism
survive?) is settled here as a checked proof; the remaining work is mechanical.

## Zero-axiom verification

Each theorem is a two-level `cases` on the miniature derivations with the cross-case discharged by
`absurd` on the rootGenerator (in)equality.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Faithful miniature of the EDITED reducibility-as-type relation.**  The gated `neutral` (now carrying
`rootGenerator ≠ gen_emptyCode`) plus the new `dataEmpty` arm (a data-type code routes to the supplied
empty candidate).  Parameterized over the empty candidate so the validation is candidate-agnostic.  Built
over the REAL `RawTerm` / `Generator` / `WeakHeadStep` so the structure transfers directly to the model. -/
inductive ScratchReducibleTypeEdited {scope : Nat} (emptyCandidate : RawTerm scope → Prop) :
    RawTerm scope → (RawTerm scope → Prop) → Prop where
  | neutral {typeCode : RawTerm scope} :
      (∀ reduct, ¬ WeakHeadStep typeCode reduct) →
      typeCode.rootGenerator ≠ Generator.gen_piTyCode →
      typeCode.rootGenerator ≠ Generator.gen_universeCode →
      typeCode.rootGenerator ≠ Generator.gen_emptyCode →
      ScratchReducibleTypeEdited emptyCandidate typeCode StepStar.IsStronglyNormalizing
  | dataEmpty {typeCode : RawTerm scope} :
      typeCode.rootGenerator = Generator.gen_emptyCode →
      ScratchReducibleTypeEdited emptyCandidate typeCode emptyCandidate

/-- **★ Make-or-break: determinism SURVIVES the edit.**  The only new interaction is the
`neutral × dataEmpty` cross-case; it is ruled out by `notEmpty` (neutral's new gate) contradicting
`isEmpty` (dataEmpty's premise) — a direct `rootGenerator` (in)equality clash.  The same-arm cases give
the candidate reflexively.  This is the property the candidate-bridge edit's whole viability rests on. -/
theorem ScratchReducibleTypeEdited.deterministic {scope : Nat} {emptyCandidate : RawTerm scope → Prop}
    {typeCode : RawTerm scope} {candidate1 candidate2 : RawTerm scope → Prop}
    (reducible1 : ScratchReducibleTypeEdited emptyCandidate typeCode candidate1)
    (reducible2 : ScratchReducibleTypeEdited emptyCandidate typeCode candidate2) :
    PointwiseIff candidate1 candidate2 := by
  cases reducible1 with
  | neutral _ _ _ notEmpty1 =>
      cases reducible2 with
      | neutral _ _ _ _ => exact fun _ => Iff.rfl
      | dataEmpty isEmpty2 => exact absurd isEmpty2 notEmpty1
  | dataEmpty isEmpty1 =>
      cases reducible2 with
      | neutral _ _ _ notEmpty2 => exact absurd isEmpty1 notEmpty2
      | dataEmpty _ => exact fun _ => Iff.rfl

/-- **emptyTypeCell routes through `dataEmpty` to the EMPTY candidate.**  ANY candidate emptyTypeCell is
reducible-as-type to IS the empty candidate — the exact reversal of the SN-forcing
`emptyTypeCell_candidate_forcedStronglyNormalizing` proves for the current model. -/
theorem ScratchReducibleTypeEdited.emptyCodeCandidateIsEmpty {scope : Nat}
    {emptyCandidate : RawTerm scope → Prop} {candidate : RawTerm scope → Prop}
    (reducible : ScratchReducibleTypeEdited emptyCandidate (emptyTypeCell (scope := scope)) candidate) :
    PointwiseIff candidate emptyCandidate :=
  ScratchReducibleTypeEdited.deterministic reducible
    (ScratchReducibleTypeEdited.dataEmpty
      (by show Generator.gen_emptyCode = Generator.gen_emptyCode; rfl))

/-- **Consistency core: the canonicity/consistency bridge becomes provable under the edit.**  With
emptyTypeCell's candidate pinned to the (member-free) empty candidate, a fundamental-theorem-produced
member of that candidate yields `False`.  This is exactly the `memberBridge` (CON-A3) that the current
model blocks (`emptyConsistencyFromReducibleMemberBridge` leaves it as the residual); the edit discharges
it. -/
theorem ScratchReducibleTypeEdited.consistencyCore {scope : Nat}
    {emptyCandidate : RawTerm scope → Prop} (memberFree : ∀ term, ¬ emptyCandidate term)
    {candidate : RawTerm scope → Prop}
    (reducible : ScratchReducibleTypeEdited emptyCandidate (emptyTypeCell (scope := scope)) candidate)
    (closedTerm : RawTerm scope) (member : candidate closedTerm) :
    False :=
  memberFree closedTerm
    ((ScratchReducibleTypeEdited.emptyCodeCandidateIsEmpty reducible closedTerm).mp member)

/-- **The edit does NOT disturb non-empty neutral codes.**  A weak-head-normal non-Π non-universe
non-empty code still gets the `IsStronglyNormalizing` candidate via the gated `neutral` — the existing
behavior for every non-data type code is preserved (the gating only carves out `gen_emptyCode`). -/
theorem ScratchReducibleTypeEdited.nonEmptyNeutralStillSN {scope : Nat}
    {emptyCandidate : RawTerm scope → Prop} {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct, ¬ WeakHeadStep typeCode reduct)
    (notPi : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : typeCode.rootGenerator ≠ Generator.gen_emptyCode) :
    ScratchReducibleTypeEdited emptyCandidate typeCode StepStar.IsStronglyNormalizing :=
  ScratchReducibleTypeEdited.neutral noWeakHeadStep notPi notUniverse notEmpty

end FX1Poly.Typed
