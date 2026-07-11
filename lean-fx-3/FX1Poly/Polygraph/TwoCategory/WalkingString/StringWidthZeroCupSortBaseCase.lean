import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLastCupSharedTopPin

/-! # WalkingString — the width-0 pure-cup sort's SINGLETON BASE CASE, closed by the shared-top pin (FC-3 r13, B3
down-payment)

The full width-0 pure-cup sort inhabiting `StringWidthZeroPureCupDeterminacyShared` (`StringValleyDegenerateSplit`)
is the fueled partner-locate recursion N1/N3 (the r14/r15 content the recon budgets).  Its BASE CASE — a
length-1 cup list — is discharged NOW, machine-checked, at the exact verbatim hypotheses the Shared Prop hands over,
exercising the shipped shared-top last-cup pin `stringSpineAtom_eq_of_sharedCod_sameWindow` (`StringLastCupSharedTopPin`)
end-to-end.  This is the down-payment on B3: the recursion's floor, proved; the recursive step (bubble the located
partner to the front, drop it, recurse) is the standing residual.

  * ★ `stringWidthZeroPureCupShared_singleton` — for two SINGLETON pure-cup spines `[cupA]`, `[cupB]` over the width-0
    bottom boundary with a shared top word, the Shared Prop's conclusion `SpineTraceEquiv [cupA] [cupB]` holds.  The
    width-0 length chain FORCES each cup's window to `0` (`domBoundaryLength = leftContext.length + generatorDom.length
    + rightContext.length = 0`), so the two cups fire at the same window; their shared top word is their shared cod
    boundary word; the pin then concludes `cupA = cupB`, whence `SpineTraceEquiv.refl`.  The matching hypothesis is
    UNUSED at the base (the width-0 chain already pins the window) — it is the RECURSIVE step's locate input.

## Why this is a genuine fragment of the Shared Prop, not a restatement

The lemma's hypotheses are exactly the Shared Prop's, specialised to `cupFirst = [cupA]`, `cupSecond = [cupB]`: same
`AllCupArity`, same `SpineBoundaryChained 0`, same `SpineBoundaryWordChained bottomWord`, same `spineListTopWord`
equality, same `matchingOfSpineList 0` equality.  So the eventual fueled sort's length-≤1 base branch is discharged by
`exact stringWidthZeroPureCupShared_singleton …`; nothing is re-typed.  The full `∀`-quantified inhabitation stays
open — the recursion over longer lists needs the partner-locate (N1, blocked on the adjunction-keyed width-0 involution
`matchingOfSpineListZero_partner_isInvolution` being genericised) plus the matching-injective drop.

## What this does NOT do (the flag stays `false` — honestly)

The base case is not the sort.  `StringWidthZeroPureCupDeterminacyShared` is NOT inhabited; the recursive step is the
r14/r15 residual.  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false`.

Raw Lean 4 + Init; the window collapse is a two-fold `Nat`-sum-vanish on the width-0 chain, the atom pin is the shipped
drop-in.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- A left summand of a `Nat` sum that is zero is itself zero (structural on the right summand, propext-free). -/
private theorem stringNatSumLeftZero : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → leftSummand = 0
  | _, 0, sumZero => sumZero
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

/-- ★ **The width-0 pure-cup sort's SINGLETON base case.**  Two length-1 pure-cup spines over the width-0 bottom
boundary that share a top word are `SpineTraceEquiv`.  The width-0 length chain forces each cup's window
(`leftContext.length`) to `0`, so the two cups fire at the same window; the shared top word is the shared cod boundary
word; the shipped shared-top pin `stringSpineAtom_eq_of_sharedCod_sameWindow` concludes the two cups EQUAL, whence
`SpineTraceEquiv.refl`.  The hypotheses are the Shared Prop's, specialised to singletons — the fueled recursion's floor,
proved.  The matching hypothesis is unused here (the width-0 chain already pins the window); it is the recursive step's
locate input. -/
theorem stringWidthZeroPureCupShared_singleton
    {overallSource overallTarget : AdjointTripleMode}
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (cupA cupB : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (pureA : AllCupArity [cupA]) (pureB : AllCupArity [cupB])
    (chainedA : SpineBoundaryChained 0 [cupA]) (chainedB : SpineBoundaryChained 0 [cupB])
    (_wordChainedA : SpineBoundaryWordChained bottomWord [cupA])
    (_wordChainedB : SpineBoundaryWordChained bottomWord [cupB])
    (topWordEq : spineListTopWord bottomWord [cupA] = spineListTopWord bottomWord [cupB])
    (_matchingEq : matchingOfSpineList 0 [cupA] = matchingOfSpineList 0 [cupB]) :
    SpineTraceEquiv adjointTripleModeSignature [cupA] [cupB] := by
  cases pureA with
  | cons domA codA _restA =>
  cases pureB with
  | cons domB codB _restB =>
  obtain ⟨headFiresA, _tailA⟩ := spineBoundaryChained_tail chainedA
  obtain ⟨headFiresB, _tailB⟩ := spineBoundaryChained_tail chainedB
  have expandA :
      cupA.leftContext.length + cupA.generatorDom.length + cupA.rightContext.length = 0 := by
    dsimp only [SpineAtom.domBoundaryLength] at headFiresA; exact headFiresA
  have expandB :
      cupB.leftContext.length + cupB.generatorDom.length + cupB.rightContext.length = 0 := by
    dsimp only [SpineAtom.domBoundaryLength] at headFiresB; exact headFiresB
  have leftLenA : cupA.leftContext.length = 0 := stringNatSumLeftZero (stringNatSumLeftZero expandA)
  have leftLenB : cupB.leftContext.length = 0 := stringNatSumLeftZero (stringNatSumLeftZero expandB)
  have codWordEq :
      composePath cupA.leftContext (composePath cupA.generatorCod cupA.rightContext)
        = composePath cupB.leftContext (composePath cupB.generatorCod cupB.rightContext) := by
    dsimp only [spineListTopWord] at topWordEq; exact topWordEq
  have atomEq : cupA = cupB :=
    stringSpineAtom_eq_of_sharedCod_sameWindow cupA cupB codWordEq
      (leftLenA.trans leftLenB.symm) (codA.trans codB.symm) domA domB
  rw [atomEq]
  exact SpineTraceEquiv.refl [cupB]

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 pure-cup sort's SINGLETON BASE CASE is discharged by the shared-top pin (FC-3 r13,
B3 down-payment).**  `stringWidthZeroPureCupShared_singleton`: two length-1 pure-cup spines sharing a top word over the
width-0 bottom boundary are `SpineTraceEquiv` — the width-0 chain forces each window to `0`, the shared top word is the
shared cod boundary word, and the shipped drop-in `stringSpineAtom_eq_of_sharedCod_sameWindow`
(`StringLastCupSharedTopPin`) concludes the two cups equal.  The hypotheses are the Shared Prop's specialised to
singletons, so the fueled sort's length-≤1 base branch is discharged verbatim — the recursion's floor, proved,
exercising the shared-top pin end-to-end.

  What this marker does NOT close (no gate flag flips): the full `∀`-quantified
  `StringWidthZeroPureCupDeterminacyShared`.  The recursive step (bubble the located partner to the front via the
  word-swap kit, drop it by matching-injectivity, recurse on the shorter shared-top lists) is the r14/r15 residual —
  the partner-locate (N1) is blocked on the adjunction-keyed width-0 partner involution
  (`matchingOfSpineListZero_partner_isInvolution`) being genericised.  So `fxString_hasAdjointTripleCompleteness` stays
  `false`, honestly.  `= true`. -/
def fxString_hasWidthZeroCupSortBaseCase : Bool := true

end FX1Poly.Polygraph
