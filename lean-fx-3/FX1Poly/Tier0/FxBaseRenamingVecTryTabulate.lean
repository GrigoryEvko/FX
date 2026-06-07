import FX1Poly.Tier0.FxBaseRenamingVecTabulate

/-! # FX1Poly/Tier0/FxBaseRenamingVecTryTabulate
    — the Option-valued tabulate: build a `RenamingVec` from a PARTIAL image function

Toward the candidate-inverse builder of the finite-bijectivity iso-decider (SN-085a, #914): the inverse of an iso
renaming is `tabulate` of its preimage function, but the preimage is PARTIAL (a target index may be unhit).  So we
need the partial analogue of `tabulate`: `tryTabulate (imageOf : Fin length → Option (Fin target)) : Option
(RenamingVec target length)`, succeeding iff EVERY image is `some`.  Composed with `findPreimage`
(`FxBaseRenamingVecPreimage.lean`), it builds the candidate inverse — `some backward` exactly when the renaming is
surjective.

## What lands here (all zero-axiom)

  * `RenamingVec.tryTabulate` — recurse on `length`; at a successor, fail if the head image is `none`, else `map`
    the head onto the recursive result.
  * `RenamingVec.tryTabulate_succ_eq` — the successor reduction equation (definitional `rfl`).
  * `RenamingVec.tryTabulate_lookup` — soundness: `tryTabulate imageOf = some vec → ∀ index, imageOf index =
    some (vec.lookup index)`.  This makes the assembled candidate inverse a right-inverse SECTION (every image
    agrees with the built vector's lookup).
  * `RenamingVec.tryTabulate_none` — completeness: `tryTabulate imageOf = none → ∃ index, imageOf index = none`.
    Drives the decider's not-surjective `isFalse` branch.

## Zero-axiom verification

The lemmas reason about the `match`-defined `tryTabulate` propext-clean by: `rw [tryTabulate_succ_eq] at h` to
expose the head match, then `split at h` (which REDUCES the matcher — `rw` alone does not iota-reduce a match on a
freed scrutinee), naming the arm pattern variable + discriminant equation via `case h_1` / `case h_2`.  The inner
`Option.map` reduces by the `Option.map_none` / `Option.map_some` rfl-lemmas; impossible `Option` equalities by
`nomatch`; the success components by `Option.some.inj` + `subst`; the `Fin` index split structurally (`⟨0,_⟩` /
`⟨_+1,_⟩`).  No `funext`, no `Fin.cases`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- **Option-valued tabulate**: build a `RenamingVec` from a partial image function, succeeding iff every image is
`some`.  Recurse on `length`; at a successor, fail if the head image is `none`, else `map` the head onto the
recursive result. -/
def RenamingVec.tryTabulate {target : Nat} :
    {length : Nat} → (Fin length → Option (Fin target)) → Option (RenamingVec target length)
  | 0, _imageOf => some PUnit.unit
  | _length + 1, imageOf =>
      match imageOf ⟨0, Nat.succ_pos _⟩ with
      | none => none
      | some headImage =>
          (RenamingVec.tryTabulate
              (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩)).map
            (fun restVec => (headImage, restVec))

/-- The successor reduction equation (definitional), so the correctness proofs can expose the head match without
`unfold`. -/
theorem RenamingVec.tryTabulate_succ_eq {target length : Nat}
    (imageOf : Fin (length + 1) → Option (Fin target)) :
    RenamingVec.tryTabulate imageOf =
      match imageOf ⟨0, Nat.succ_pos _⟩ with
      | none => none
      | some headImage =>
          (RenamingVec.tryTabulate
              (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩)).map
            (fun restVec => (headImage, restVec)) := rfl

/-- **Soundness**: when `tryTabulate` succeeds, every image agrees with the built vector's lookup — so the
candidate inverse assembled from it is a right-inverse section. -/
theorem RenamingVec.tryTabulate_lookup {target : Nat} :
    {length : Nat} → (imageOf : Fin length → Option (Fin target)) → (vec : RenamingVec target length) →
      RenamingVec.tryTabulate imageOf = some vec →
        ∀ (index : Fin length), imageOf index = some (vec.lookup index)
  | 0, _imageOf, _vec, _someEq => fun index => index.elim0
  | _length + 1, imageOf, vec, someEq => by
      rw [RenamingVec.tryTabulate_succ_eq] at someEq
      split at someEq
      case h_1 => nomatch someEq
      case h_2 headImage hHead =>
        cases hRest : RenamingVec.tryTabulate
            (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩) with
        | none =>
            rw [hRest, Option.map_none] at someEq
            nomatch someEq
        | some restVec =>
            rw [hRest, Option.map_some] at someEq
            have vecEq : vec = (headImage, restVec) := (Option.some.inj someEq).symm
            have ih := RenamingVec.tryTabulate_lookup
              (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩) restVec hRest
            subst vecEq
            exact fun index => match index with
              | ⟨0, _⟩ => hHead
              | ⟨position + 1, isLt⟩ => ih ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- **Completeness**: when `tryTabulate` fails, some image was `none` — driving the decider's not-surjective
`isFalse` branch. -/
theorem RenamingVec.tryTabulate_none {target : Nat} :
    {length : Nat} → (imageOf : Fin length → Option (Fin target)) →
      RenamingVec.tryTabulate imageOf = none → ∃ (index : Fin length), imageOf index = none
  | 0, _imageOf, noneEq => nomatch (show some (PUnit.unit) = none from noneEq)
  | _length + 1, imageOf, noneEq => by
      rw [RenamingVec.tryTabulate_succ_eq] at noneEq
      split at noneEq
      case h_1 hHead => exact ⟨⟨0, Nat.succ_pos _length⟩, hHead⟩
      case h_2 headImage _hHead =>
        cases hRest : RenamingVec.tryTabulate
            (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩) with
        | none =>
            have ⟨restIndex, restNone⟩ := RenamingVec.tryTabulate_none
              (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩) hRest
            exact ⟨⟨restIndex.val + 1, Nat.succ_lt_succ restIndex.isLt⟩, restNone⟩
        | some restVec =>
            rw [hRest, Option.map_some] at noneEq
            nomatch noneEq

end FX1Poly.Tier0
