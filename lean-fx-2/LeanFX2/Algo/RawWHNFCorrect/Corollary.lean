import LeanFX2.Algo.RawWHNFCorrect.Headline

/-! # Corollary — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # LeanFX2.Algo.RawWHNFCorrect.Corollary — WHNF agreement and convertibility

Two corollaries of `whnf_reaches`:

* `whnf_agreement_join` — equal WHNF outputs imply a shared
  parStar-reduct, the convertibility witness needed downstream.
* `checkConv` — a fuel-bounded structural-equality check on
  WHNFs, sound (positive answers witness a common reduct) but
  not complete (negatives may be fuel-starvation).

Combined with confluence (Phase 6.C), these underpin the
decidable conversion checker in `Algo/DecConv`.

## Root status

Layer 3 algorithm aggregator. -/

namespace LeanFX2

variable {scope : Nat}

/-! ## Corollary: WHNF agreement ⇒ common reduct

Two raw terms whose WHNF outputs are equal share a common reduct
(both reach the shared WHNF via parStar).  Combined with
confluence (Phase 6.C), this provides the foundation for a
fuel-bounded conversion check: if WHNFs agree, terms are
parStar-convertible. -/

/-- If two terms have the same WHNF (at the same fuel), they have
a common parStar-reduct. -/
theorem RawTerm.whnf_agreement_join
    {scope : Nat} (fuel : Nat) (leftTerm rightTerm : RawTerm scope)
    (whnfsEqual : RawTerm.whnf fuel leftTerm = RawTerm.whnf fuel rightTerm) :
    ∃ commonReduct,
      RawStep.parStar leftTerm commonReduct ∧
      RawStep.parStar rightTerm commonReduct :=
  ⟨RawTerm.whnf fuel leftTerm,
   RawTerm.whnf_reaches fuel leftTerm,
   whnfsEqual ▸ RawTerm.whnf_reaches fuel rightTerm⟩

/-! ## Fuel-bounded conversion checker

`RawTerm.checkConv fuel left right` returns `true` iff the WHNFs
of `left` and `right` (at the given fuel) are structurally equal.
Sound (positive answers witness a common parStar-reduct) but not
complete (negative answers may be due to insufficient fuel or
deeper redexes that WHNF doesn't reach). -/

/-- Fuel-bounded structural-equality conversion check on raw
terms.  Returns `true` iff `whnf fuel left` equals `whnf fuel
right` as raw terms.  Decidable via `RawTerm`'s `DecidableEq`. -/
def RawTerm.checkConv (fuel : Nat) {scope : Nat}
    (leftTerm rightTerm : RawTerm scope) : Bool :=
  decide (RawTerm.whnf fuel leftTerm = RawTerm.whnf fuel rightTerm)

/-- Soundness: a positive `checkConv` answer witnesses a common
parStar-reduct.  Composes `decide ... = true ↔ ...` with
`whnf_agreement_join`. -/
theorem RawTerm.checkConv_sound
    {scope : Nat} (fuel : Nat) (leftTerm rightTerm : RawTerm scope)
    (checkSucceeded : RawTerm.checkConv fuel leftTerm rightTerm = true) :
    ∃ commonReduct,
      RawStep.parStar leftTerm commonReduct ∧
      RawStep.parStar rightTerm commonReduct := by
  have whnfsEqual : RawTerm.whnf fuel leftTerm = RawTerm.whnf fuel rightTerm :=
    of_decide_eq_true checkSucceeded
  exact RawTerm.whnf_agreement_join fuel leftTerm rightTerm whnfsEqual

/-- Reflexivity: a term is convertible to itself at any fuel.
`checkConv` always succeeds when both sides are syntactically equal,
since `whnf fuel term = whnf fuel term` is `rfl`. -/
theorem RawTerm.checkConv_refl
    {scope : Nat} (fuel : Nat) (term : RawTerm scope) :
    RawTerm.checkConv fuel term term = true := by
  unfold RawTerm.checkConv
  exact decide_eq_true rfl


end LeanFX2

-/
