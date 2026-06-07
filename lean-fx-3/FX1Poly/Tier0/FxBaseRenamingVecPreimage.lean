import FX1Poly.Tier0.FxBaseRenamingVecTabulate

/-! # FX1Poly/Tier0/FxBaseRenamingVecPreimage
    — the preimage search over a `RenamingVec`: the search core of the finite-bijectivity iso-decider

Toward the `memberDecidable` of the iso-class `RepresentableMapCategory` (SN-085a, #914): a categorical iso of the
renaming base is a renaming whose lookup is a bijection, and the candidate inverse is `tabulate` of the PREIMAGE
function `Fin target → Fin source`.  This file supplies that preimage search and its two correctness facts.

`findPreimage vec targetIndex` walks the product structure of `vec : RenamingVec target source` and returns the
FIRST position whose stored image equals `targetIndex` (reconstructed as a `Fin source` across the recursion), or
`none` if no position maps there.  Soundness (`findPreimage_some`) says a found position really maps to the target
— this makes the assembled candidate inverse a right-inverse section; completeness (`findPreimage_none`) says a
`none` result means the target is genuinely unhit — this drives the decider's not-surjective `isFalse` branch (an
iso's inverse would supply a preimage, contradiction).

## What lands here (all zero-axiom)

  * `RenamingVec.findPreimage` — the first-preimage search (product recursion, head compared by `Nat` value).
  * `RenamingVec.findPreimage_succ_eq` — the successor reduction equation (definitional `rfl`), so proofs reason
    about the search without `unfold`.
  * `RenamingVec.findPreimage_some` — soundness: `findPreimage vec j = some i → vec.lookup i = j`.
  * `RenamingVec.findPreimage_none` — completeness: `findPreimage vec j = none → ∀ i, vec.lookup i ≠ j`.

## Zero-axiom verification

The search compares the head image by `Nat` value via a `Nat.decEq` match (not `if`/`by_cases`, which pull
`Classical`).  The correctness proofs case on that `Nat.decEq` (`cases hDec`), derive a computed reduction equation
through `findPreimage_succ_eq` + `rw [hDec]` (never `unfold`/`simp`), and discharge the impossible-`Option`
equalities by `nomatch` and the genuine ones by `Option.some.inj` + `Fin.eq_of_val_eq` — type-ascribing through the
`Option.map` reduction.  The `Fin source` index is split structurally (`⟨0,_⟩` / `⟨_+1,_⟩`), no `Fin.cases`.  No
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- Search a `RenamingVec` for the first position whose stored image is `targetIndex`, reconstructing that position
as a `Fin source` across the product recursion; `none` if no position maps there. -/
def RenamingVec.findPreimage {target : Nat} :
    {source : Nat} → RenamingVec target source → Fin target → Option (Fin source)
  | 0, _vec, _targetIndex => none
  | _source + 1, vec, targetIndex =>
      match Nat.decEq vec.1.val targetIndex.val with
      | isTrue _ => some ⟨0, Nat.succ_pos _⟩
      | isFalse _ =>
          (RenamingVec.findPreimage vec.2 targetIndex).map
            (fun restIndex => ⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩)

/-- The successor reduction equation (definitional), so the correctness proofs never need `unfold`. -/
theorem RenamingVec.findPreimage_succ_eq {target source : Nat}
    (vec : RenamingVec target (source + 1)) (targetIndex : Fin target) :
    RenamingVec.findPreimage vec targetIndex =
      match Nat.decEq vec.1.val targetIndex.val with
      | isTrue _ => some ⟨0, Nat.succ_pos _⟩
      | isFalse _ =>
          (RenamingVec.findPreimage vec.2 targetIndex).map
            (fun restIndex => ⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩) := rfl

/-- **Soundness**: a found position really maps to the target index — so the candidate inverse assembled from
`findPreimage` is a right-inverse section. -/
theorem RenamingVec.findPreimage_some {target : Nat} :
    {source : Nat} → (vec : RenamingVec target source) → (targetIndex : Fin target) →
      (foundIndex : Fin source) → RenamingVec.findPreimage vec targetIndex = some foundIndex →
        vec.lookup foundIndex = targetIndex
  | 0, _vec, _targetIndex, foundIndex, _foundEq => foundIndex.elim0
  | _source + 1, vec, targetIndex, foundIndex, foundEq => by
      cases hDec : Nat.decEq vec.1.val targetIndex.val with
      | isTrue headEqual =>
          have reduced : RenamingVec.findPreimage vec targetIndex = some ⟨0, Nat.succ_pos _source⟩ := by
            rw [RenamingVec.findPreimage_succ_eq, hDec]
          have foundIsZero : foundIndex = ⟨0, Nat.succ_pos _source⟩ :=
            Option.some.inj (foundEq.symm.trans reduced)
          rw [foundIsZero]
          show vec.1 = targetIndex
          exact Fin.eq_of_val_eq headEqual
      | isFalse headDiffers =>
          have reduced : RenamingVec.findPreimage vec targetIndex =
              (RenamingVec.findPreimage vec.2 targetIndex).map
                (fun restIndex => ⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩) := by
            rw [RenamingVec.findPreimage_succ_eq, hDec]
          cases hRest : RenamingVec.findPreimage vec.2 targetIndex with
          | none =>
              rw [hRest] at reduced
              nomatch (show some foundIndex = none from foundEq.symm.trans reduced)
          | some restIndex =>
              rw [hRest] at reduced
              have foundIsSucc : foundIndex = ⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩ :=
                Option.some.inj
                  (show some foundIndex = some ⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩
                    from foundEq.symm.trans reduced)
              rw [foundIsSucc]
              show vec.2.lookup restIndex = targetIndex
              exact RenamingVec.findPreimage_some vec.2 targetIndex restIndex hRest

/-- **Completeness**: a `none` result means NO position maps to the target — so a hypothetical iso (whose inverse
would supply a preimage) cannot exist, driving the decider's not-surjective `isFalse` branch. -/
theorem RenamingVec.findPreimage_none {target : Nat} :
    {source : Nat} → (vec : RenamingVec target source) → (targetIndex : Fin target) →
      RenamingVec.findPreimage vec targetIndex = none →
        ∀ (index : Fin source), vec.lookup index ≠ targetIndex
  | 0, _vec, _targetIndex, _noneEq => fun index => index.elim0
  | _source + 1, vec, targetIndex, noneEq => by
      cases hDec : Nat.decEq vec.1.val targetIndex.val with
      | isTrue headEqual =>
          have reduced : RenamingVec.findPreimage vec targetIndex = some ⟨0, Nat.succ_pos _source⟩ := by
            rw [RenamingVec.findPreimage_succ_eq, hDec]
          nomatch (show some (⟨0, Nat.succ_pos _source⟩ : Fin (_source + 1)) = none
            from reduced.symm.trans noneEq)
      | isFalse headDiffers =>
          have reduced : RenamingVec.findPreimage vec targetIndex =
              (RenamingVec.findPreimage vec.2 targetIndex).map
                (fun restIndex => ⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩) := by
            rw [RenamingVec.findPreimage_succ_eq, hDec]
          cases hRest : RenamingVec.findPreimage vec.2 targetIndex with
          | some restIndex =>
              rw [hRest] at reduced
              nomatch (show some (⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩ : Fin (_source + 1)) = none
                from reduced.symm.trans noneEq)
          | none =>
              have tailComplete := RenamingVec.findPreimage_none vec.2 targetIndex hRest
              exact fun index => match index with
                | ⟨0, _⟩ => fun headIsTarget => headDiffers (congrArg Fin.val headIsTarget)
                | ⟨position + 1, isLt⟩ => tailComplete ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

end FX1Poly.Tier0
