import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallFreeInversion — the LETTER-level wall-free inversion (the converse of
`embedRightLetter`) + injectivity + round-trip (WP-AMALG-2 r10, B1 — node (i) prerequisite)

The r10 recon's node (i) (the reconstruction-inversion / essential-surjectivity converse) needs, at its base, a
LETTER-level converse of the right coprojection `embedRightLetter`: given a pushout-alphabet letter that is
component-2 (`letterTag = false`, i.e. index `≥ comp1.len` — the "wall-free" / gap letters), recover the monad
letter it came from by subtracting the split offset.  This file ships that converse, its two round-trips, and the
letter-level injectivity of `embedRightLetter`, then TRUTH-PROBES it on the concrete `involution +_M monad` pushout
letters `s` (wall) and `t` (gap) FIRST — before any cell-level inversion is attempted.

## The letter converse (general over any two components)

`embedRightLetter comp1 comp2 sameModes` sends a component-2 index `i` to `⟨comp1.len + i, _⟩` (a Fin subtraction's
inverse).  Its converse `retractRightLetter` sends a combined letter `letter` with `comp1.len ≤ letter.val` back to
`⟨letter.val − comp1.len, _⟩` — TOTAL and injective on the wall-free (component-2) subset, because this pushout's
alphabet is EXACTLY `comp1-retag ++ comp2-retag` (the free-product disjointness).  The two round-trips
(`retract ∘ embed = id`, `embed ∘ retract = id`) and `embedRightLetter_injective` are clean Fin/Nat arithmetic
(`addSubCancelLeft` / `addSubCancel` / `Nat.add_left_cancel`, `Fin.ext`) — no `omega`, no propext.

## The truth-probe on the concrete pushout letters (FIRST)

`involutionMonadSplit = 1` (the involution contributes one generator).  The gap letter `t` (`tLetter`, index `1`)
is wall-free (`letterTag = false`), and `retractRightLetter … tLetter = ⟨0, _⟩` recovers the monad's `t`-generator
index — machine-checked by `decide`.  The wall letter `s` (`sLetter`, index `0`) is NOT wall-free
(`letterTag = true`), so the converse is (correctly) inapplicable — the boundary between the invertible gap letters
and the non-invertible wall letters is exactly the `letterTag` bit.

## What STAYS WALLED (no flip)

This is the LETTER-level (1-generator) converse — NOT the PATH-level `pathInvert` (a wall-free pushout 1-cell
reconstructs a monad 1-cell), and NOT the CELL-level `wallFreeCellInvert` (node i's essential-surjectivity converse
feeding `pushoutRightImageConvReflect`).  Those are the named downstream nodes (B1-path / B3).
`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`;
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL / Fin-`.ext` / `decide` on literals.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The `Nat.blt`-false bridge -/

/-- From `Nat.blt value bound = false` recover `bound ≤ value` — the converse of `bltFalseOfGe`, via the total
order (`Nat.lt_or_ge`): a `value < bound` would give `Nat.blt value bound = true` (`bltTrueOfLt`), contradicting the
hypothesis.  Propext-free (`Nat.lt_or_ge` + `Bool.noConfusion`). -/
theorem geOfBltFalse {value bound : Nat} (isFalse : Nat.blt value bound = false) : bound ≤ value :=
  match Nat.lt_or_ge value bound with
  | Or.inl isLt => Bool.noConfusion ((bltTrueOfLt isLt).symm.trans isFalse)
  | Or.inr isGe => isGe

/-! ## The letter-level converse of `embedRightLetter` -/

/-- ★ **The letter-level converse of `embedRightLetter`** — a combined pushout letter that is component-2
(`comp1.len ≤ letter.val`, i.e. wall-free / `letterTag = false`) retracts to the monad letter `⟨letter.val −
comp1.len, _⟩`.  The bound is `subLtOfLtAdd` on the combined-length equation (mirroring `copairOnGenerators`'s
component-2 branch).  TOTAL on the wall-free subset. -/
def retractRightLetter (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (letter : Fin (combinedModalityGenerators comp1 comp2 sameModes).length)
    (isRight : comp1.modalityGenerators.length ≤ letter.val) :
    Fin comp2.modalityGenerators.length :=
  ⟨letter.val - comp1.modalityGenerators.length, by
    have belowSum : letter.val < comp1.modalityGenerators.length + comp2.modalityGenerators.length := by
      rw [← combinedModalityGenerators_length]; exact letter.isLt
    exact subLtOfLtAdd isRight belowSum⟩

/-- The retract's underlying value is the offset subtraction (definitional). -/
theorem retractRightLetter_val (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (letter : Fin (combinedModalityGenerators comp1 comp2 sameModes).length)
    (isRight : comp1.modalityGenerators.length ≤ letter.val) :
    (retractRightLetter comp1 comp2 sameModes letter isRight).val
      = letter.val - comp1.modalityGenerators.length := rfl

/-- ★ **`retract ∘ embed = id`** — the right coprojection followed by its converse recovers the monad index
(`addSubCancelLeft`: `(len1 + i) − len1 = i`), `Fin.ext`. -/
theorem retractRightLetter_embedRightLetter (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) (index : Fin comp2.modalityGenerators.length)
    (isRight : comp1.modalityGenerators.length ≤ (embedRightLetter comp1 comp2 sameModes index).val) :
    retractRightLetter comp1 comp2 sameModes (embedRightLetter comp1 comp2 sameModes index) isRight = index :=
  Fin.ext (addSubCancelLeft comp1.modalityGenerators.length index.val)

/-- ★ **`embed ∘ retract = id`** — the converse followed by the right coprojection recovers the wall-free letter
(`addSubCancel`: `len1 + (v − len1) = v` given `len1 ≤ v`), `Fin.ext`. -/
theorem embedRightLetter_retractRightLetter (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (letter : Fin (combinedModalityGenerators comp1 comp2 sameModes).length)
    (isRight : comp1.modalityGenerators.length ≤ letter.val) :
    embedRightLetter comp1 comp2 sameModes (retractRightLetter comp1 comp2 sameModes letter isRight) = letter :=
  Fin.ext (addSubCancel isRight)

/-- ★ **`embedRightLetter` is injective** — two monad indices with equal right-coprojected letters are equal.
Cancelling the shared `comp1.len` offset via the propext-free subtraction round-trip `addSubCancelLeft`
(`(len + i) − len = i`): `indexA.val = (len + indexA.val) − len = (len + indexB.val) − len = indexB.val`, then
`Fin.ext`.  Avoids `Nat.add_left_cancel` (which pulls `propext`).  The free-product faithfulness at the 1-generator
level. -/
theorem embedRightLetter_injective (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) {indexA indexB : Fin comp2.modalityGenerators.length}
    (equalImages : embedRightLetter comp1 comp2 sameModes indexA = embedRightLetter comp1 comp2 sameModes indexB) :
    indexA = indexB :=
  Fin.ext
    ((addSubCancelLeft comp1.modalityGenerators.length indexA.val).symm.trans
      ((congrArg (· - comp1.modalityGenerators.length) (congrArg Fin.val equalImages)).trans
        (addSubCancelLeft comp1.modalityGenerators.length indexB.val)))

/-! ## The truth-probe on the concrete pushout letters (FIRST) -/

-- The gap letter `t` is component-2 (wall-free): expect `false`.
#eval letterTag involutionMonadSplit tLetter
-- The retract of the gap letter `t`: expect `0` (the monad's t-generator index).
#eval (retractRightLetter involutionComputad monadComputad involutionMonadSameModes tLetter
        (by decide)).val
-- The wall letter `s` is component-1 (NOT wall-free): expect `true`.
#eval letterTag involutionMonadSplit sLetter

/-- ★★ **The gap letter `t` is wall-free** — `letterTag involutionMonadSplit tLetter = false` (`decide`), so the
converse is applicable to it. -/
theorem tLetter_wallFree : letterTag involutionMonadSplit tLetter = false := by decide

/-- ★★ **The wall letter `s` is NOT wall-free** — `letterTag involutionMonadSplit sLetter = true` (`decide`), so
the converse is (correctly) inapplicable: the invertible/non-invertible boundary is exactly the `letterTag` bit. -/
theorem sLetter_notWallFree : letterTag involutionMonadSplit sLetter = true := by decide

/-- ★★★ **THE CONCRETE GEN-LETTER TRUTH-PROBE.**  On the shipped `involution +_M monad` pushout, the gap letter `t`
(`tLetter`, index `1`) retracts to the monad's `t`-generator index `⟨0, _⟩` — machine-checked by `decide` (a
genuine reduction on concrete data, not a vacuous instance).  This is the letter-level base of node (i)'s
reconstruction-inversion: a wall-free pushout letter reconstructs its monad pre-image. -/
theorem tLetter_retract :
    retractRightLetter involutionComputad monadComputad involutionMonadSameModes tLetter (by decide)
      = ⟨0, by decide⟩ := by decide

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the LETTER-level wall-free inversion SHIPS (WP-AMALG-2 r10, B1).**  `= true`:
`retractRightLetter` is the total converse of the right coprojection `embedRightLetter` on the wall-free
(component-2) letters, with both round-trips (`retractRightLetter_embedRightLetter`,
`embedRightLetter_retractRightLetter`), the letter-level injectivity `embedRightLetter_injective`, and the
`Nat.blt`-false bridge `geOfBltFalse`.  The concrete truth-probe (`tLetter_retract`, by `decide`) confirms the gap
letter `t` retracts to the monad's `t`-index on the shipped pushout, and `tLetter_wallFree` / `sLetter_notWallFree`
pin the invertible/non-invertible boundary at the `letterTag` bit.  This is node (i)'s LETTER base; the PATH-level
`pathInvert` (a wall-free 1-cell reconstructs a monad 1-cell) and the CELL-level `wallFreeCellInvert` are the named
downstream nodes.  No marker flips.  `= true`. -/
def fxAmalg_hasWallFreeLetterInversion : Bool := true

end FX1Poly.Polygraph.Amalgam
