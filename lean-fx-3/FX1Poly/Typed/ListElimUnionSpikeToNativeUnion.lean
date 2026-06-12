import FX1Poly.Typed.DataIntroNativeRowConversion
import FX1Poly.Typed.ListElimRecursiveRow

/-! # FX1Poly/Typed/ListElimUnionSpikeToNativeUnion — NATIVE-36 / NATIVE-33: the listElim spike
    transfers INTO the real union judgment (discharging the batch-1 union-residency pin)

The NATIVE-32(B) spike (`ListElimUnionSpike`, in `ListElimRecursiveRow`) locked the app-chain listElim
row shape, with the union-proper residency explicitly PINNED as NATIVE-33 follow-on work.  NATIVE-36
lands a native twin of that row IN `HasTypeNativeUnion` as the `listElim` arm (the table hoisted into
the pre-union `NativeUnionRuleTables` as `listElimNativeRule`).  This file proves the TRANSFER: every
spike derivation maps to a `HasTypeNativeUnion` typing at the same subject and classifier — discharging
the batch-1 pin "listElim union residency lands with NATIVE-33".  Mirrors
`RecursiveElimUnionSpike.toNativeUnion`.

## The transfer

`ListElimUnionSpike.toNativeUnion` — `induction` over the spike's three arms:

  * `ofUnion unionTyped` — identity.
  * `ofListIntro listTyped` — the union's own `ofListIntro` embedding arm.
  * `listElimRecursiveRow` — the spike's table hit (`listElimRecursiveRuleOf generator = some rule`) is
    inverted by the spike-table-inversion lemma here, pinning `gen_listElim` and the spike row; the spike
    row's cell builders are definitionally the native row's, so the union's `listElim` arm fires with the
    scrutinee / nil / cons premises carried verbatim (they are GROWN in the spike — no IH needed).

## Zero-axiom

The spike-table-inversion lemma is `by_cases` over the single-row table; the transfer is `induction`
over the spike's arms with that lemma feeding the union arm at definitionally-equal cells.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNativeWaveUnionResidency.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Spike-table inversion (the transfer ingredient; decidable, no derivation elimination) -/

/-- **A spike listElim table hit pins the listElim spike row.**  Decidable case analysis over the
spike's single-row `listElimRecursiveRuleOf` if-then-else table. -/
theorem listElimRecursiveRuleOf_spikeCases {generator : Generator} {rule : ListElimRule}
    (tableHit : listElimRecursiveRuleOf generator = some rule) :
    generator = .gen_listElim ∧ rule = listElimRecursiveRule := by
  unfold listElimRecursiveRuleOf at tableHit
  by_cases isListElim : generator = .gen_listElim
  · rw [if_pos isListElim] at tableHit
    exact ⟨isListElim, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isListElim] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-! ## ★ The spike→union transfer -/

/-- **★ Every NATIVE-32(B) `ListElimUnionSpike` derivation maps to a `HasTypeNativeUnion` typing at the
same subject and classifier.**  Induction over the spike's three arms; `ofUnion` is identity,
`ofListIntro` converts through the native intro rows (`toNativeRows`), and the `listElimRecursiveRow`
maps to the union's `listElim` arm via the spike-table-inversion lemma at definitionally-equal cells —
the spike's list-intro scrutinee premise converts through `toNativeRows` into the union arm's
NATIVE-42 union-recursive scrutinee premise; the nil/cons grown premises carry verbatim.  Discharges
the batch-1 union-residency pin. -/
theorem ListElimUnionSpike.toNativeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : ListElimUnionSpike profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  induction derivation with
  | ofUnion unionTyped => exact unionTyped
  | ofListIntro listTyped => exact listTyped.toNativeRows
  | listElimRecursiveRow generator rule motive scrutinee nilBranch consBranch elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      rcases listElimRecursiveRuleOf_spikeCases isListElim with ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.listElim _ .gen_listElim listElimNativeRule
        motive scrutinee nilBranch consBranch elementType resultType rfl
        scrutineeTyped.toNativeRows nilBranchTyped consBranchTyped

/-! ## The transfer gate -/

/-- **The NATIVE-36 listElim transfer evidence record.**  An inhabitant certifies the listElim spike
transfers wholesale into the real union — the batch-1 pin discharged. -/
structure ListElimUnionTransferEvidence (profile : PolyProfile) : Prop where
  /-- Every spike derivation transfers to the union. -/
  spikeTransfers : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    ListElimUnionSpike profile context subject classifier →
    HasTypeNativeUnion profile context subject classifier

/-- **★ The NATIVE-36 listElim transfer gate** — inhabited by the shipped witness. -/
theorem listElimUnionTransferWitness {profile : PolyProfile} :
    ListElimUnionTransferEvidence profile where
  spikeTransfers := fun derivation => derivation.toNativeUnion

end FX1Poly.Typed
