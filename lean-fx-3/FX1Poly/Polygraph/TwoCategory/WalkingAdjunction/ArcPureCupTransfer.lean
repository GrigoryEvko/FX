import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine

/-! # ArcPureCupTransfer — arc equality carries the pure-cup regime across both spines (cap-first base case)

The cap-first reconstruction route (#2168) peels caps preferentially until the spine has none left,
then finishes the pure-cup remainder by cup-interchange (Godement) alone.  Its base case fires on the
guard `capAtomCount firstList = 0` (no caps to peel).  At that point the caller also holds the
whole-spine arc equality `arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList
bottomCount secondList` with the OTHER spine.  This brick shows the guard PROPAGATES across that
equality: BOTH spines are pure cup.

The total `capCount` of an arc structure reflects the boundary-independent cap-ATOM count
(`capCountReflect`, re-derived locally to keep this off the gate file `ArcReconstruction`, whose
reconstruction marker would cycle if imported).  So arc-equal spines carry equal cap-atom counts, and
a zero count on one side forces zero on the other — whence `AllCupArity` on both
(`allCupArity_ofCapAtomCountZero`).

  * `capAtomCount_ofAllCupArity` — the converse of `allCupArity_ofCapAtomCountZero`: a pure-cup spine
    has zero cap tally.  Together they make `AllCupArity ↔ capAtomCount = 0` a clean characterization
    the interchange base case can phrase in either direction.
  * ★ `bothPureCup_ofCapCountZeroAndArcEqual` — the transfer: the base-case guard plus the whole-spine
    arc equality force `AllCupArity` on BOTH spines.

What this brick does NOT claim: the base case's own content (equal-arc pure-cup spines are
cup-interchange equivalent) nor the cap-first recursion itself.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The arc structure's total `capCount` reflects the boundary-independent cap-atom count — re-derived
locally (the gate file `ArcReconstruction` owns the shared copy; the transfer chain must not import it,
or flipping the reconstruction marker would cycle). -/
private theorem capCountReflect {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    (arcStructureOfSpineList bottomCount atoms).capCount = capAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).capEventNodes.length = capAtomCount atoms
  rw [processArcSpine_capEventNodes_length]
  exact Nat.zero_add _

/-- **The converse of `allCupArity_ofCapAtomCountZero`.**  A pure-cup spine has zero cap tally: every
atom has cup arity `(0, 2)`, so its domain length is `0`, not `2`, and the cap guard never fires.  By
induction on the `AllCupArity` witness. -/
theorem capAtomCount_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    AllCupArity atoms → capAtomCount atoms = 0 := by
  intro allCup
  induction allCup with
  | nil => rfl
  | cons hasCupDomArity hasCupCodArity restAllCup restCapZero =>
      rename_i headAtom rest
      dsimp only [capAtomCount]
      have guardFalse :
          ¬ (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
        rw [hasCupDomArity]
        exact Bool.noConfusion
      rw [if_neg guardFalse, Nat.zero_add]
      exact restCapZero

/-- ★ **The pure-cup regime transfers across arc equality.**  The cap-first base-case guard
`capAtomCount firstList = 0` plus the whole-spine arc equality between the two spines force
`AllCupArity` on BOTH: the arc structure's total `capCount` reflects the cap-atom count
(`capCountReflect`), so arc-equal spines carry equal cap tallies; a zero tally on the first side
forces zero on the second, and both discharge through `allCupArity_ofCapAtomCountZero`. -/
theorem bothPureCup_ofCapCountZeroAndArcEqual
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstCapZero : capAtomCount firstList = 0)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    AllCupArity firstList ∧ AllCupArity secondList := by
  have capCountsAgree : capAtomCount firstList = capAtomCount secondList := by
    have congrCapCount := congrArg FullArcStructure.capCount arcEqual
    rw [capCountReflect bottomCount firstList, capCountReflect bottomCount secondList] at congrCapCount
    exact congrCapCount
  have secondCapZero : capAtomCount secondList = 0 := capCountsAgree.symm.trans firstCapZero
  exact ⟨allCupArity_ofCapAtomCountZero firstList firstCapZero,
    allCupArity_ofCapAtomCountZero secondList secondCapZero⟩

/-! ## Honesty marker -/

/-- **Honesty marker — arc equality carries the pure-cup regime across both spines (cap-first base
case).**  `bothPureCup_ofCapCountZeroAndArcEqual`: the base-case guard `capAtomCount firstList = 0`
plus the whole-spine arc equality force `AllCupArity` on both spines; `capAtomCount_ofAllCupArity`
supplies the converse characterization.  What this marker does NOT claim: the base case's own
cup-interchange content nor the cap-first recursion.  `= true`. -/
def fxMode_hasArcPureCupTransfer : Bool := true

end FX1Poly.Polygraph
