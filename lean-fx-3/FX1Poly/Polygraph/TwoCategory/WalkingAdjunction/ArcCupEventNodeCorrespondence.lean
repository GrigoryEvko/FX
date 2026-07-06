import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence

/-! # ArcCupEventNodeCorrespondence — the cup-event-node ↔ cup-atom ordering correspondence (Strategy 2)

`processArcSpine` threads the arc fold head-first (`List.foldl stepArcAtom`).  Each CUP atom (arity
`0 ⇒ 2`) fires `stepCupArc`, which PREPENDS its event node `state.nextFresh + 2` onto
`state.cupEventNodes`; every other atom (`stepCapArc`, the generic box) leaves `cupEventNodes`
untouched.  So the fold only ever grows `cupEventNodes` at the FRONT — the starting state's cup
events stay a suffix, and the FIRST cup fired (the head cup) ends up as the LAST element.

This is the ordering half of the cup-event-node correspondence — the shipped
`processArcSpine_cupEventNodes_length` (`GodementIndependence.lean`) is the count half
(`cupEventNodes.length = cupAtomCount`).  Together: the final `cupEventNodes` is a length-`cupAtomCount`
list whose last element (for a cup head folded onto the fresh seed) is `bottomCount + 2` — the head
cup's event node, the atom whose window the boundary-index inversion must recover.

  ★ `IsConsSuffix` — a cons-based suffix relation (propext-free: a plain inductive `Prop`, no
    `List.append`, so `List.append_assoc` / `nil_append` never enter the proof term);
  ★ `stepArcAtom_cupEventNodes_consSuffix` — one arc step keeps `state.cupEventNodes` a cons-suffix
    (the cup prepends one node, cap / box leave it fixed);
  ★ `processArcSpine_cupEventNodes_consSuffix` — the whole fold keeps it a cons-suffix (fold induction
    + `IsConsSuffix.trans`);
  ★ `stepCupHead_cupEventNodes` — a cup-arity head fires `stepCupArc`, so its stepped `cupEventNodes`
    is exactly `(state.nextFresh + 2) :: state.cupEventNodes`;
  ★ `processArcSpine_headCup_consSuffix` / `arcSeedHeadCup_eventNode_isLast` — the head cup's event
    node `state.nextFresh + 2` is the LAST element of the final `cupEventNodes`; at the fresh seed
    (`nextFresh = bottomCount`, `cupEventNodes = []`) this reads `IsConsSuffix [bottomCount + 2] …`.

## What this does NOT close

The window recovery `windowPin` itself: this identifies WHICH event node (`bottomCount + 2`) belongs
to the head cup, but reading its window still needs the union-find inversion that maps that event
node's component back to the boundary port pair it turns back on (`internalCupCounts` scan +
short-chord adjacency).  This file supplies the "which cup atom owns event node `bottomCount + 2`"
half of that inversion.

Raw Lean 4 + Init; plain-inductive `IsConsSuffix` + structural fold induction, no `List.append`,
`omega`, `simp`-AC, or `WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A cons-based suffix relation (propext-free) -/

/-- `IsConsSuffix shorter longer` holds when `longer` is `shorter` with finitely many cons cells
prepended — a suffix reached by dropping heads.  A plain inductive `Prop` with no `List.append`, so
its proofs never route through the documented `List.append_assoc` / `nil_append` `propext` traps. -/
inductive IsConsSuffix {elem : Type} : List elem → List elem → Prop where
  /-- Every list is a cons-suffix of itself. -/
  | refl (whole : List elem) : IsConsSuffix whole whole
  /-- Prepending one cons cell keeps the suffix. -/
  | cons {shorter longer : List elem} (head : elem) :
      IsConsSuffix shorter longer → IsConsSuffix shorter (head :: longer)

/-- Cons-suffix is transitive: a suffix of a suffix is a suffix.  By induction on the outer witness. -/
theorem IsConsSuffix.trans {elem : Type} {first second third : List elem}
    (firstSuffix : IsConsSuffix first second) (secondSuffix : IsConsSuffix second third) :
    IsConsSuffix first third := by
  induction secondSuffix with
  | refl => exact firstSuffix
  | cons head _ inductionHypothesis => exact .cons head inductionHypothesis

/-! ## One arc step keeps `cupEventNodes` a cons-suffix -/

/-- ★ **One arc step keeps `state.cupEventNodes` a cons-suffix of the stepped state's.**  A CUP atom
(`0 ⇒ 2`) prepends its event node via `stepCupArc` (`.cons`); a CAP atom and the generic box leave
`cupEventNodes` untouched (`.refl`).  By cases on the generator's boundary lengths mirroring
`stepArcAtom`'s match (the exact skeleton of `stepArcAtom_cupEventNodes_length`). -/
theorem stepArcAtom_cupEventNodes_consSuffix {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    IsConsSuffix state.cupEventNodes (stepArcAtom state atom).cupEventNodes := by
  unfold stepArcAtom
  generalize atom.generatorDom.length = domLen
  generalize atom.generatorCod.length = codLen
  cases domLen with
  | zero =>
    cases codLen with
    | zero => exact .refl _
    | succ codLenPred =>
      cases codLenPred with
      | zero => exact .refl _
      | succ codLenPredPred =>
        cases codLenPredPred with
        | zero => exact .cons _ (.refl _)
        | succ _ => exact .refl _
  | succ domLenPred =>
    cases domLenPred with
    | zero =>
      cases codLen with
      | zero => exact .refl _
      | succ _ => exact .refl _
    | succ domLenPredPred =>
      cases domLenPredPred with
      | zero =>
        cases codLen with
        | zero => exact .refl _
        | succ _ => exact .refl _
      | succ _ => exact .refl _

/-! ## The whole fold keeps `cupEventNodes` a cons-suffix -/

/-- ★ **The arc fold keeps `state.cupEventNodes` a cons-suffix of the final state's.**  Since every arc
step only ever prepends to `cupEventNodes`, the starting state's list is a suffix of the result.  By
induction on the spine (the `foldl`), threading `IsConsSuffix.trans` through the per-step suffix. -/
theorem processArcSpine_cupEventNodes_consSuffix {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    IsConsSuffix state.cupEventNodes (processArcSpine state atoms).cupEventNodes
  | [], _ => .refl _
  | atom :: rest, state => by
      show IsConsSuffix state.cupEventNodes (processArcSpine (stepArcAtom state atom) rest).cupEventNodes
      exact (stepArcAtom_cupEventNodes_consSuffix state atom).trans
        (processArcSpine_cupEventNodes_consSuffix rest (stepArcAtom state atom))

/-! ## The head cup's event node is the LAST element -/

/-- A cup-arity head (`0 ⇒ 2`) fires `stepCupArc`, so its stepped `cupEventNodes` is exactly the head
cup's event node `state.nextFresh + 2` prepended onto `state.cupEventNodes`. -/
theorem stepCupHead_cupEventNodes {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (headAtom : SpineAtom signature sourceMode targetMode)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2) :
    (stepArcAtom state headAtom).cupEventNodes = (state.nextFresh + 2) :: state.cupEventNodes := by
  unfold stepArcAtom
  rw [hasCupDomArity, hasCupCodArity]
  rfl

/-- ★ **The head cup's event node `state.nextFresh + 2` is the LAST element of the final
`cupEventNodes`.**  For a cup-arity head, the head fires first and prepends `state.nextFresh + 2`;
every subsequent cup prepends in front of it, so `(state.nextFresh + 2) :: state.cupEventNodes` stays a
cons-suffix of the fully-folded `cupEventNodes`.  This is the ordering fact that pins the head cup's
event node at the tail of the reverse-ordered event list. -/
theorem processArcSpine_headCup_consSuffix {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (headAtom : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode))
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2) :
    IsConsSuffix ((state.nextFresh + 2) :: state.cupEventNodes)
      (processArcSpine state (headAtom :: rest)).cupEventNodes := by
  show IsConsSuffix ((state.nextFresh + 2) :: state.cupEventNodes)
    (processArcSpine (stepArcAtom state headAtom) rest).cupEventNodes
  rw [← stepCupHead_cupEventNodes state headAtom hasCupDomArity hasCupCodArity]
  exact processArcSpine_cupEventNodes_consSuffix rest (stepArcAtom state headAtom)

/-- ★ **The fresh-seed reading: a cup head's event node is `bottomCount + 2`, the LAST cup event.**
Specialising `processArcSpine_headCup_consSuffix` to the canonical seed
`ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []` (where `nextFresh = bottomCount` and
`cupEventNodes = []`): the final `cupEventNodes` list ends with `bottomCount + 2`, the head cup's event
node.  Combined with the shipped `processArcSpine_cupEventNodes_length` (its length is `cupAtomCount`),
this fixes which entry of the reverse-ordered event list the head cup owns. -/
theorem arcSeedHeadCup_eventNode_isLast {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (headAtom : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode))
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2) :
    IsConsSuffix [bottomCount + 2]
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        (headAtom :: rest)).cupEventNodes :=
  processArcSpine_headCup_consSuffix
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom rest
    hasCupDomArity hasCupCodArity

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-event-node ↔ cup-atom ordering correspondence is proved (Strategy 2).**
`processArcSpine_cupEventNodes_consSuffix` proves the arc fold only grows `cupEventNodes` at the front,
and `arcSeedHeadCup_eventNode_isLast` reads the head cup's event node as the LAST element
(`bottomCount + 2` at the fresh seed).  With the shipped count half
(`processArcSpine_cupEventNodes_length`) this identifies which reverse-ordered event entry the head cup
owns.  What this marker does NOT claim: the window recovery `windowPin` itself — mapping event node
`bottomCount + 2`'s union-find component back to its boundary port pair (the `internalCupCounts`
inversion + short-chord adjacency) is the remaining planar step.  `= true`. -/
def fxMode_hasArcCupEventNodeCorrespondence : Bool := true

end FX1Poly.Polygraph
