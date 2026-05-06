import LeanFX2.Algo.RawWHNFCorrect
import LeanFX2.Confluence.ConvBridge

/-! # Algo/DecConv — fuel-bounded definitional conversion

The goal of decidable conversion is a `Decidable (Conv t1 t2)`
instance.  Full decidability requires strong normalization (a
separate metatheoretic theorem); without SN we ship a sound
fuel-bounded checker.

## What lives here

* `Term.checkConv` — typed counterpart to `RawTerm.checkConv`,
  delegated to the raw projection (since `Term.toRaw t` is rfl
  in lean-fx-2's raw-aware Term encoding).
* `Term.checkConv_sound` — soundness against the raw kernel:
  positive answers witness a raw common reduct, which composes
  with `Conv.toRawJoin` (Phase 6.F) to relate to typed `Conv`.
* `Conv.toCheckConv` — typed `Conv` projects to a checkConv-style
  raw join via `Conv.toRawJoin`; the WHNFs of source and target
  raw projections may not literally agree (WHNF is fuel-bounded),
  but they are parStar-joinable.

## Bidirectional structure

The algorithm composes three pieces:

1. **WHNF reach**: every output of `RawTerm.whnf fuel term` is
   parStar-reachable from `term` (`whnf_reaches`, Phase 9.A.2).

2. **WHNF agreement ⇒ join** : if the WHNF outputs of two raw
   terms are structurally equal, the terms share a common
   parStar-reduct (`whnf_agreement_join`, Phase 9.A.3).

3. **Conv ⇒ raw join** : typed `Conv` projects to a raw join via
   `Conv.toRawJoin` (Phase 6.F).  This is the mathematical content;
   the algorithmic content is in (1)+(2).

## What's still missing

* **Full decidability**: requires strong normalization to bound
  fuel.  Without SN, `checkConv` may return false negatives.
* **Recursive structural compare under WHNF**: when WHNFs disagree
  at the head, the algorithm should NOT immediately fail — it
  should case on the head and recurse on sub-terms (handles
  reduction-stuck binders).  This is a future enhancement; the
  current `checkConv` catches only flat WHNF agreement.
* **Typed Conv from raw join**: requires Phase 7 (subject reduction).
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Typed-level fuel-bounded conversion checker.  Delegates to
`RawTerm.checkConv` on the raw projections — `Term.toRaw t` is
`rfl` in the raw-aware Term encoding, so this is just sugar. -/
def Term.checkConv (fuel : Nat)
    {leftType rightType : Ty level scope}
    {leftRaw rightRaw : RawTerm scope}
    (_leftTerm : Term context leftType leftRaw)
    (_rightTerm : Term context rightType rightRaw) : Bool :=
  RawTerm.checkConv fuel leftRaw rightRaw

/-- Soundness: a positive `Term.checkConv` answer witnesses a raw
common parStar-reduct between the two terms' raw projections.

Combined with `Conv.toRawJoin` (Phase 6.F) — which goes from
typed Conv to raw join — and the fact that raw join is symmetric
under `RawStep.parStar.append`, this gives the boundary at which
typed and raw reasoning meet. -/
theorem Term.checkConv_sound (fuel : Nat)
    {leftType rightType : Ty level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftTerm : Term context leftType leftRaw)
    (rightTerm : Term context rightType rightRaw)
    (checkSucceeded : Term.checkConv fuel leftTerm rightTerm = true) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw :=
  RawTerm.checkConv_sound fuel leftRaw rightRaw checkSucceeded

/-- Typed `Conv` projects to a raw join.  This is just a renaming
of `Conv.toRawJoin` (Phase 6.F) for convenience inside `Algo/`. -/
theorem Conv.toRawCheckConvWitness
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.toRawJoin convertibility

end LeanFX2
