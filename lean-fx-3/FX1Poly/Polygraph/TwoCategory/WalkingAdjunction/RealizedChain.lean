import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineReadback

/-! # mode-3 floor — the boundary-coherent REALIZED-SPINE CHAIN + the precise obstruction to the
normal-form reconstruction (`nfReconstruct`)

`AdjunctionTwoCellWordProblem` reduced the seed's full `TwoCellConv` decision to `(traceDecision, reconstruct)`,
and `FreeTwoCellSpineReadback` sharpened `reconstruct` to its interchange-free-NORMAL-FORM restriction
`AdjunctionNfTraceReconstruction` (= `nfReconstruct`), recording that a direct boundary-indexed TOTAL readback
`List SpineAtom → RawTwoCellExpr … sourcePath targetPath` cannot exist (the empty list is the spine of every
identity, forcing the empty case to inhabit an arbitrary boundary — a dependent-motive wall).  This file builds
the object that DODGES that totality wall — a coherence-refined chain carrying its inter-atom boundary equalities
in the indexing, with a TOTAL cast-free readback — and then pins down, with a machine-checked witness, the
DIFFERENT wall that blocks the cell↔chain bridge (hence `nfReconstruct`).

## What this file ships (each piece zero-axiom)

  ★ `RealizedSpineChain sourcePath targetPath` — the **boundary-coherent chain**: a list of `SpineAtom`s whose
    inter-atom boundary coherences are BAKED INTO the indexing (`cons atom rest` has `rest` start exactly at
    `atomFrameTarget atom`, and the whole chain start exactly at `atomFrameSource atom`; the empty chain
    `nil path` exists only at the reflexive boundary `path ⇒ path`).  Realizable by construction — no atom is
    ever forced onto an arbitrary boundary, so the totality wall is dodged.
  ★ `chainToCell` — the **TOTAL, cast-free readback** `RealizedSpineChain … → RawTwoCellExpr …`: right-associated
    whiskered-atom reassembly (`nil ↦ id`, `cons atom rest ↦ atomFrame atom ⊟ chainToCell rest`), structural
    recursion on the chain.  This is exactly the `List SpineAtom → cell` function the totality wall forbids,
    recovered once the boundary coherence is carried in the index.
  ★ `chainAtoms` / `singletonRealizedChain` / `concatRealizedChain` — the chain's underlying atom list, the
    one-atom chain, and chain concatenation (associative on the nose by construction).
  ★ `chainToCell_spine` (★) — **faithfulness of the readback**: the reassembled cell's spine is exactly the
    chain's atom list (`(chainToCell chain).spine = chainAtoms chain`).  So the chain is a faithful spine
    refinement — the bridge a future reconstruction would thread `SpineTraceEquiv` along.
  ★ `chainToCell_concat` (★) — the readback is a **homomorphism up to conversion**: reassembling a concatenated
    chain is `TwoCellConv` to the vertical composite of the two reassemblies (`vcompAssoc` / `vcompIdLeft` /
    `vcompCongrRight`, all shipped).  So the readback respects the monoid structure the trace equivalence acts on.

## What is DEFERRED — and WHY (the honest, witnessed obstruction) — gates stay `false`

`nfReconstruct` needs, for the two NORMAL forms, a chain whose readback is `TwoCellConv` to the normal form
(`chainToCell chain ≈ nfCell a`).  That **cell↔chain bridge does NOT hold with the shipped 3-polygraph**, and the
reason is NOT the totality wall (this file dodges it) but the deferred whisker functoriality
(`fxMode_hasInterchangeAndWhiskerFunctoriality = false` in `FreeTwoCellModel`).  The per-atom readback
`atomFrame atom = leftContext ◁ (rightContext ▷ gen)` ALWAYS wraps in both whiskerings — even by IDENTITY
1-cells, and even when the original cell whiskered by a COMPOSITE path was built from nested single whiskers —
and NO shipped `TwoCellStep` strips an identity-1-cell whisker or splits a composite-1-cell whisker (those are
the deferred unit / functoriality laws, whose boundaries differ only PROPOSITIONALLY by `composePath`
right-identity / associativity).  Concretely, machine-checked below:

  * `adjunctionUnitFrame_isInterchangeNormal` — `atomFrame` of the unit's spine atom (=
    `nil ◁ (nil ▷ gen unit)`) is already a NORMAL FORM: the identity-1-cell whisker wrappers are irreducible.
  * `adjunctionUnitFrame_spine_eq_unit` — yet it has the SAME spine as the bare `gen unit`.
  * `adjunctionUnitFrame_normalForm_ne_unit` — but a DISTINCT interchange-free normal form.

So the spine is STRICTLY COARSER than the interchange-free normal form: `cellFirst.spine = cellSecond.spine`
(the strongest `SpineTraceEquiv` hypothesis) does NOT determine `nfCell cellFirst = nfCell cellSecond`.  A
reconstruction therefore cannot read the spine back to a unique cell; it must identify spine-equal but
normal-form-distinct cells, which is precisely the deferred whisker functoriality.  Hence `nfReconstruct` is NOT
dischargeable on the shipped `TwoCellConv` (it would in fact be unsound there unless those cells are convertible,
which is itself the deferred Godement-with-functoriality question), and `fxMode_hasRealizedChainCellBridge` /
`fxMode_hasSpineTraceReconstruction` / `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasDecidableTwoCellEquality` stay `false`.  What this file adds is the boundary-coherent readback that
dodges the totality wall, its faithfulness and homomorphism, and the machine-checked RELOCATION of the residual
from the (now-dodged) totality wall to the (deferred) whisker-functoriality wall.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the chain readback is structural recursion; the faithfulness is `composePath`-right-identity congruence; the
homomorphism is `vcompAssoc` / `vcompIdLeft` congruence; the obstruction witness is `rfl` on the spine and the
shipped free-2-cell `DecidableEq` on the normal forms).  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The boundary-coherent chain + its cast-free total readback -/

/-- The **boundary-coherent realized-spine chain** from `sourcePath` to `targetPath`: a list of `SpineAtom`s with
the inter-atom boundary coherences BAKED INTO the indexing.  `nil path` is the empty chain at the reflexive
boundary `path ⇒ path`; `cons atom rest` prepends `atom` to a chain that starts EXACTLY at `atomFrameTarget atom`,
producing a chain that starts EXACTLY at `atomFrameSource atom`.  Realizable by construction — every atom meets
its neighbour on the nose — so the `List SpineAtom → cell` totality wall is dodged. -/
inductive RealizedSpineChain (signature : ModeSignature)
    {sourceMode targetMode : signature.graph.Mode} :
    ModalityPath signature.graph sourceMode targetMode →
    ModalityPath signature.graph sourceMode targetMode → Type where
  /-- The empty chain — exists only at the reflexive boundary `path ⇒ path`. -/
  | nil (path : ModalityPath signature.graph sourceMode targetMode) :
      RealizedSpineChain signature path path
  /-- Prepend an atom whose frame target is exactly where the rest of the chain begins. -/
  | cons (atom : SpineAtom signature sourceMode targetMode)
      {chainTarget : ModalityPath signature.graph sourceMode targetMode}
      (rest : RealizedSpineChain signature (atomFrameTarget atom) chainTarget) :
      RealizedSpineChain signature (atomFrameSource atom) chainTarget

/-- ★ The **total, cast-free readback** of a boundary-coherent chain to a free 2-cell: right-associated
whiskered-atom reassembly.  The empty chain reads back as the identity 2-cell; a cons reads back as the per-atom
frame `atomFrame atom` vertically composed with the rest.  This is the `List SpineAtom → RawTwoCellExpr …
sourcePath targetPath` function the totality wall forbids — total here because the chain carries the boundary
coherence in its index, so no cast is needed. -/
def chainToCell {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RealizedSpineChain signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath
  | _, _, .nil path => RawTwoCellExpr.id path
  | _, _, .cons atom rest => RawTwoCellExpr.vcomp (atomFrame atom) (chainToCell rest)

/-- The chain's underlying atom list (the spine the chain realizes). -/
def chainAtoms {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RealizedSpineChain signature sourcePath targetPath →
    List (SpineAtom signature sourceMode targetMode)
  | _, _, .nil _ => []
  | _, _, .cons atom rest => atom :: chainAtoms rest

/-- The one-atom chain — the readback of a single spine atom, anchored at its frame boundary. -/
def singletonRealizedChain {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    RealizedSpineChain signature (atomFrameSource atom) (atomFrameTarget atom) :=
  RealizedSpineChain.cons atom (RealizedSpineChain.nil (atomFrameTarget atom))

/-- Concatenate two boundary-coherent chains meeting at a common middle 1-cell (associative on the nose;
structural recursion on the first chain). -/
def concatRealizedChain {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath middlePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RealizedSpineChain signature sourcePath middlePath →
    RealizedSpineChain signature middlePath targetPath →
    RealizedSpineChain signature sourcePath targetPath
  | _, _, _, .nil _, secondChain => secondChain
  | _, _, _, .cons atom rest, secondChain => .cons atom (concatRealizedChain rest secondChain)

/-- Smoke: the readback of the empty chain is the identity 2-cell (definitional). -/
theorem chainToCell_nil {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (path : ModalityPath signature.graph sourceMode targetMode) :
    chainToCell (RealizedSpineChain.nil path) = RawTwoCellExpr.id path := rfl

/-- Smoke: the readback of a cons is the head frame vertically composed with the rest (definitional). -/
theorem chainToCell_cons {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode)
    {chainTarget : ModalityPath signature.graph sourceMode targetMode}
    (rest : RealizedSpineChain signature (atomFrameTarget atom) chainTarget) :
    chainToCell (RealizedSpineChain.cons atom rest)
      = RawTwoCellExpr.vcomp (atomFrame atom) (chainToCell rest) := rfl

/-! ## Faithfulness: the readback's spine is the chain's atom list -/

/-- Reading one `atomFrame` back into a spine difference-list prepends exactly one atom — the original atom with
its boundary accumulators composed onto the contexts (definitional). -/
theorem atomFrame_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    (atomFrame atom).spineDiff leftAcc rightAcc rest
      = ⟨atom.leftMidMode, atom.rightMidMode, composePath leftAcc atom.leftContext,
          atom.generatorDom, atom.generatorCod, atom.generator,
          composePath atom.rightContext rightAcc⟩ :: rest := rfl

/-- At the TOP accumulators (empty boundary), reading an `atomFrame` back recovers exactly the original atom: the
left context's identity composition is definitional, the right context's needs `composePath`-right-identity. -/
theorem atomFrame_spineDiff_top {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    (atomFrame atom).spineDiff (identityPath sourceMode) (identityPath targetMode) rest
      = atom :: rest := by
  rw [atomFrame_spineDiff]
  cases atom with
  | mk leftMidMode rightMidMode leftContext generatorDom generatorCod generator rightContext =>
    show (⟨leftMidMode, rightMidMode, leftContext, generatorDom, generatorCod, generator,
        composePath rightContext (identityPath targetMode)⟩ : SpineAtom signature sourceMode targetMode)
        :: rest
      = ⟨leftMidMode, rightMidMode, leftContext, generatorDom, generatorCod, generator, rightContext⟩ :: rest
    rw [composePath_identityPath_right]

/-- ★ **Faithfulness of the readback.**  The reassembled cell's spine is exactly the chain's atom list — so the
boundary-coherent chain is a faithful spine refinement, the bridge a reconstruction would thread `SpineTraceEquiv`
along.  Structural recursion on the chain (the cons step folds in `atomFrame_spineDiff_top`). -/
theorem chainToCell_spine {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (chain : RealizedSpineChain signature sourcePath targetPath) →
    (chainToCell chain).spine = chainAtoms chain
  | _, _, .nil _ => rfl
  | _, _, .cons atom rest => by
      show (RawTwoCellExpr.vcomp (atomFrame atom) (chainToCell rest)).spine = atom :: chainAtoms rest
      dsimp only [RawTwoCellExpr.spine]
      rw [show (RawTwoCellExpr.vcomp (atomFrame atom) (chainToCell rest)).spineDiff
              (identityPath sourceMode) (identityPath targetMode) []
            = (atomFrame atom).spineDiff (identityPath sourceMode) (identityPath targetMode)
                ((chainToCell rest).spineDiff (identityPath sourceMode) (identityPath targetMode) [])
          from rfl,
        show (chainToCell rest).spineDiff (identityPath sourceMode) (identityPath targetMode) []
            = (chainToCell rest).spine from rfl,
        chainToCell_spine rest, atomFrame_spineDiff_top]

/-! ## The readback respects composition (homomorphism up to conversion) -/

/-- ★ **The readback is a homomorphism up to conversion.**  Reassembling a concatenated chain is `TwoCellConv` to
the vertical composite of the two reassemblies: the empty-first case is the inverse of `vcompIdLeft`, the cons
case threads the inductive hypothesis through `vcompCongrRight` and re-associates by `vcompAssoc`. -/
theorem chainToCell_concat {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath middlePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (firstChain : RealizedSpineChain signature sourcePath middlePath) →
    (secondChain : RealizedSpineChain signature middlePath targetPath) →
    TwoCellConv signature (chainToCell (concatRealizedChain firstChain secondChain))
      (RawTwoCellExpr.vcomp (chainToCell firstChain) (chainToCell secondChain))
  | _, _, _, .nil _, secondChain =>
      TwoCellConv.symm (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (chainToCell secondChain)))
  | _, _, _, .cons atom rest, secondChain =>
      TwoCellConv.trans
        (TwoCellConv.vcompCongrRight (atomFrame atom) (chainToCell_concat rest secondChain))
        (TwoCellConv.symm (TwoCellConv.ofStep
          (TwoCellStep.vcompAssoc (atomFrame atom) (chainToCell rest) (chainToCell secondChain))))

/-! ## The precise obstruction: the spine is strictly coarser than the interchange-free normal form -/

/-- The unit's single spine atom (empty whisker contexts) — the per-atom datum whose readback exhibits the
obstruction. -/
def adjunctionUnitSpineAtom : SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base where
  leftMidMode := AdjunctionMode.base
  rightMidMode := AdjunctionMode.base
  leftContext := ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base
  generatorDom := ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base
  generatorCod := adjunctionLeftThenRight
  generator := AdjunctionTwoCell.unit
  rightContext := ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base

/-- This atom is the unit's whole spine — so its `atomFrame` is the per-atom readback of the unit's spine. -/
theorem adjunctionUnitSpineAtom_isUnitSpine :
    adjunctionUnitTwoCell.spine = [adjunctionUnitSpineAtom] := rfl

/-- ★ The per-atom readback `atomFrame adjunctionUnitSpineAtom` (= `nil ◁ (nil ▷ gen unit)`) is already an
interchange-free NORMAL FORM: NO shipped `TwoCellStep` strips the identity-1-cell whisker wrappers — they are the
deferred whisker-unit law (`fxMode_hasInterchangeAndWhiskerFunctoriality`). -/
theorem adjunctionUnitFrame_isInterchangeNormal :
    (atomFrame adjunctionUnitSpineAtom).isInterchangeNormal = true := rfl

/-- ★ Yet the per-atom readback has the SAME spine as the bare `gen unit` (the wrappers are spine-invisible). -/
theorem adjunctionUnitFrame_spine_eq_unit :
    (atomFrame adjunctionUnitSpineAtom).spine = adjunctionUnitTwoCell.spine := rfl

/-- ★ **The spine is strictly coarser than the interchange-free normal form.**  The per-atom readback
`atomFrame adjunctionUnitSpineAtom` and the bare `gen unit` have EQUAL spines (above) but DISTINCT interchange-free
normal forms (here, by the shipped free-2-cell `DecidableEq`).  So `cellFirst.spine = cellSecond.spine` — the
strongest `SpineTraceEquiv` hypothesis — does NOT determine `nfCell cellFirst = nfCell cellSecond`: a
reconstruction cannot read the spine back to a unique cell.  This is the precise, machine-checked obstruction to
`nfReconstruct` on the shipped 3-polygraph — the deferred whisker functoriality, not the (now-dodged) totality
wall. -/
theorem adjunctionUnitFrame_normalForm_ne_unit :
    nfCell (atomFrame adjunctionUnitSpineAtom) ≠ nfCell adjunctionUnitTwoCell :=
  of_decide_eq_false
    (inst := adjunctionRawTwoCellDecidableEq
      (nfCell (atomFrame adjunctionUnitSpineAtom)) (nfCell adjunctionUnitTwoCell))
    rfl

/-! ## Honesty marker -/

/-- **Honesty marker.**  The boundary-coherent chain `RealizedSpineChain` + its total cast-free readback
`chainToCell` DODGE the totality wall (the `List SpineAtom → cell` readback the predecessor proved impossible),
and the readback is faithful (`chainToCell_spine`) and a homomorphism up to conversion (`chainToCell_concat`).
But the cell↔chain BRIDGE `chainToCell chain ≈ nfCell a` — which `nfReconstruct` needs — does NOT hold on the
shipped `TwoCellConv`: the per-atom readback reassembles a cell with the SAME spine as the original but a DISTINCT
interchange-free normal form (`adjunctionUnitFrame_spine_eq_unit` + `adjunctionUnitFrame_normalForm_ne_unit`),
because `atomFrame`'s identity-1-cell / composite-1-cell whisker wrappers cannot be stripped without the deferred
whisker functoriality (`fxMode_hasInterchangeAndWhiskerFunctoriality = false`).  So `nfReconstruct` is NOT
dischargeable here, and the keystone residual stays `(traceDecision, nfReconstruct)` — with `nfReconstruct` now
RELOCATED from the totality wall to the whisker-functoriality wall.  `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasDecidableTwoCellEquality` stay `false`.  `= false`. -/
def fxMode_hasRealizedChainCellBridge : Bool := false

end FX1Poly.Polygraph
