import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderClosure

/-! # MODE-COMMUTE — the CAP x CAP faithful reorder sibling closure (r20)

The r19 keystone `FaithfulReorderEquiv` / `extractArc_eq_of_faithfulReorderEquiv` closed the five LITERAL
crossing swaps plus the CUP x CUP partition swap under reflexivity / symmetry / transitivity, conservatively
EXCLUDING every cap-swap partition pair BY CONSTRUCTION.  That exclusion was narratively pinned on "the cap
wall": a cap MERGE flips a merged union-find root against the join order (`ArcCoreSwapCapFlipRefutation`,
machine-refuted), so the ROOT-LEVEL renaming vehicle `rootComm` cannot carry a cap-cap swap and
`fxMode_hasArcGodementSwapRenameableProof2` stays permanently `false`.  This file makes the honest scope
precise: the cap wall is REAL only at that root-level renaming vehicle.  The PARTITION-level simulation
`ArcPartitionSim` is representative-free (`componentsCorr`, not root equality), so it SIDESTEPS the cap-cap
root flip — the native core `capCapSwap_arcPartitionSim` (r14, "the combo the renaming vehicle provably cannot
handle") is exactly the vehicle invented for this, and it already ships packaged as `arcSwapCorePackage_capCap`.

## The additive sibling (the WP-PROP-r20 pattern)

`FaithfulReorderEquiv` is SHIPPED and is never edited.  The cap-cap arm goes in a NEW sibling relation
`FaithfulReorderEquivWithCapCap` that EMBEDS the whole r19 relation through a single `ofR19` constructor and
adds ONE new generating arm `ofCapCapSwap` off `arcSwapCorePackage_capCap`, plus `symm` / `trans`.  The
embedding keeps the extended-closure proof one-directional and minimal: the `ofR19` case discharges by the
shipped `extractArc_eq_of_faithfulReorderEquiv` in one line (no re-proof of the five literal + cup-cup arms),
the `ofCapCapSwap` case by the new faithful cap-cap port, `symm` / `trans` by `Eq.symm` / `Eq.trans`.

## The bricks (in dependency order)

  * `arcFaithfulCapCapSuffixExtractCommute` — ★ THE PORT.  The two run orders of a CAP x CAP swap
    (`stepCapArc (stepCapArc state positionLow) (gap + positionLow)` vs
    `stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow`), which differ by the fresh-block
    transposition `arcFreshBlockTransposition state.nextFresh 1 1`, extract to EQUAL `FullArcStructure`s after
    ANY admissible crossing-carrying faithful suffix `rest`.  A one-liner over the engine-generic faithful
    peel `extractArc_eq_rest_faithful_of_swapCorePackage` fed `arcSwapCorePackage_capCap` — the cup-cup
    delivery `arcFaithfulCupCupSuffixExtractCommute` with `_cupCup` swapped for `_capCap` and nothing else.
  * `FaithfulReorderEquivWithCapCap` — the sibling relation: `ofR19` embeds r19, `ofCapCapSwap` is the new
    cap-cap partition arm, plus `symm` / `trans`.  Full four-constructor enumeration keeps the invariance
    induction propext-free.
  * `faithfulReorder_ofCapCap` — the smart constructor for the new arm (mirrors r19's
    `faithfulReorder_ofCupCup`).
  * `reorderWithCapCap_of_faithfulReorder` — the embedding r19 => sibling (`ofR19`).
  * `extractArc_eq_of_faithfulReorderEquivWithCapCap` — ★ THE EXTENDED CLOSURE THEOREM: extract-after-`rest`
    is invariant along the WHOLE sibling closure.

## Non-vacuity — fires on ALL FOUR partition-swap families

The four partition packages `arcSwapCorePackage_{cupCup, cupCap, capCup, capCap}` are ALL proven at the
partition level; the literal crossing swaps have provably-EQUAL endpoints (an `ofLiteralSwap` carries a state
equality), so only the four PARTITION families have endpoints that genuinely differ.  The extended closure /
the engine-generic port fires on each, every fire paired with a decide-confirmed refl-failure probe:

  * CAP x CAP (the new arm, via the sibling closure) — endpoints differ in `links` (the caps drop the same
    surviving wires, so `openWires` COINCIDE; the join-order difference lives entirely in the union-find).
  * CUP x CUP (via the sibling closure through `ofR19`) — endpoints differ in `openWires`.
  * CUP x CAP and CAP x CUP (via the engine-generic port directly, NOT added as inductive arms — the r20
    scope adds only cap-cap) — endpoints differ in `openWires`.

Plus a MIXED multi-step witness: a `trans` chain composing a literal re-expression, the genuine cap-cap
renaming, and a second literal re-expression, its two endpoints differing in `links`.

Raw Lean 4 + Init; structural induction on the derivation, no `omega` / `simp`-AC / `WellFounded.fix` /
quotients / `propext`.  Strictly ADDITIVE — the shipped r19 relation and its marker are byte-intact; this file
only adds.  The three permanent keystones stay `false`, re-asserted by `rfl`.  Per-declaration
`#assert_no_axioms` AND an independent `#print axioms` gated in the audit twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The port — the CAP x CAP faithful suffix extract commutation -/

/-- ★ **THE CAP x CAP FAITHFUL SUFFIX DELIVERY.**  The two run orders of a CAP x CAP swap
(`stepCapArc (stepCapArc state positionLow) (gap + positionLow)` vs
`stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow`), which differ by the fresh-block
transposition `arcFreshBlockTransposition state.nextFresh 1 1`, extract to EQUAL `FullArcStructure`s after ANY
admissible (crossing-carrying) faithful suffix `rest`.  Built off `arcSwapCorePackage_capCap` — whose
`coreSim` is the NATIVE representative-free `capCapSwap_arcPartitionSim`, precisely the partition core that
survives the cap-cap root flip that refutes `rootComm` — fed to the engine-generic faithful peel
`extractArc_eq_rest_faithful_of_swapCorePackage`.  The cup-cup delivery with `_cupCup` swapped for `_capCap`
and nothing else. -/
theorem arcFaithfulCapCapSuffixExtractCommute {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat) (lowWindowFits : positionLow + 2 ≤ state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode))
    (admissible : SpineAdmissibleFaithful rest
      (stepCapArc (stepCapArc state positionLow) (gap + positionLow))) :
    extractArc bottomCount
        (processArcSpineFaithful
          (stepCapArc (stepCapArc state positionLow) (gap + positionLow)) rest)
      = extractArc bottomCount
          (processArcSpineFaithful
            (stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow) rest) :=
  extractArc_eq_rest_faithful_of_swapCorePackage bottomCount _ _
    (arcSwapCorePackage_capCap state fresh forest nextFreshPos bottomCount boundaryBelowFresh
      gap positionLow lowWindowFits)
    rest admissible

/-! ## The sibling relation -/

/-- ★ **The faithful reorder closure WITH the cap-cap arm (r20).**  A NEW sibling relation embedding the whole
r19 `FaithfulReorderEquiv` through `ofR19` and adding the CAP x CAP partition arm `ofCapCapSwap` (whose two run
orders differ FOREVER by the width-`1`/`1` fresh-block transposition, reconciled only up to the partition
view), plus `symm` / `trans`.  The r19 relation is never edited; this rides atop it.  A full four-constructor
enumeration keeps the extended invariance induction propext-free. -/
inductive FaithfulReorderEquivWithCapCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (rest : List (SpineAtom signature sourceMode targetMode)) :
    ArcWireState → ArcWireState → Prop where
  | ofR19 {stateLeft stateRight : ArcWireState}
      (equiv : FaithfulReorderEquiv bottomCount rest stateLeft stateRight) :
      FaithfulReorderEquivWithCapCap bottomCount rest stateLeft stateRight
  | ofCapCapSwap (state : ArcWireState)
      (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
      (nextFreshPos : 0 < state.nextFresh) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
      (gap positionLow : Nat) (lowWindowFits : positionLow + 2 ≤ state.openWires.length)
      (admissible : SpineAdmissibleFaithful rest
        (stepCapArc (stepCapArc state positionLow) (gap + positionLow))) :
      FaithfulReorderEquivWithCapCap bottomCount rest
        (stepCapArc (stepCapArc state positionLow) (gap + positionLow))
        (stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow)
  | symm {stateLeft stateRight} :
      FaithfulReorderEquivWithCapCap bottomCount rest stateLeft stateRight →
      FaithfulReorderEquivWithCapCap bottomCount rest stateRight stateLeft
  | trans {stateLeft stateMid stateRight} :
      FaithfulReorderEquivWithCapCap bottomCount rest stateLeft stateMid →
      FaithfulReorderEquivWithCapCap bottomCount rest stateMid stateRight →
      FaithfulReorderEquivWithCapCap bottomCount rest stateLeft stateRight

/-- cap-cap partition reorder step (the r20 arm; the native representative-free partition core the renaming
vehicle cannot handle).  Mirrors r19's `faithfulReorder_ofCupCup`. -/
theorem faithfulReorder_ofCapCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (rest : List (SpineAtom signature sourceMode targetMode))
    (state : ArcWireState) (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat) (lowWindowFits : positionLow + 2 ≤ state.openWires.length)
    (admissible : SpineAdmissibleFaithful rest
      (stepCapArc (stepCapArc state positionLow) (gap + positionLow))) :
    FaithfulReorderEquivWithCapCap bottomCount rest
      (stepCapArc (stepCapArc state positionLow) (gap + positionLow))
      (stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow) :=
  FaithfulReorderEquivWithCapCap.ofCapCapSwap state fresh forest nextFreshPos boundaryBelowFresh
    gap positionLow lowWindowFits admissible

/-- ★ **The embedding r19 => sibling.**  Every r19 `FaithfulReorderEquiv` node lifts to the sibling relation
through the single `ofR19` constructor — the whole five-literal + cup-cup closure is re-usable verbatim. -/
theorem reorderWithCapCap_of_faithfulReorder {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (rest : List (SpineAtom signature sourceMode targetMode))
    {stateLeft stateRight : ArcWireState}
    (equiv : FaithfulReorderEquiv bottomCount rest stateLeft stateRight) :
    FaithfulReorderEquivWithCapCap bottomCount rest stateLeft stateRight :=
  FaithfulReorderEquivWithCapCap.ofR19 equiv

/-! ## THE EXTENDED CLOSURE THEOREM -/

/-- ★ **THE EXTENDED CLOSURE THEOREM (r20).**  Any two states related by
`FaithfulReorderEquivWithCapCap bottomCount rest` extract to EQUAL `FullArcStructure`s after the SAME admissible
faithful suffix `rest`.  Structural induction on the derivation, full four-constructor enumeration (no
wildcard, so propext-free): the `ofR19` arm discharges by the shipped r19 closure
`extractArc_eq_of_faithfulReorderEquiv` (no re-proof of the five literal + cup-cup arms), the `ofCapCapSwap` arm
by the new cap-cap port `arcFaithfulCapCapSuffixExtractCommute`, and `symm` / `trans` by `Eq.symm` /
`Eq.trans`.  The observation-invariance-over-the-equivalence-closure of trace theory, now extended by the
cap-cap partition family. -/
theorem extractArc_eq_of_faithfulReorderEquivWithCapCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (rest : List (SpineAtom signature sourceMode targetMode))
    {stateLeft stateRight : ArcWireState}
    (equiv : FaithfulReorderEquivWithCapCap bottomCount rest stateLeft stateRight) :
    extractArc bottomCount (processArcSpineFaithful stateLeft rest)
      = extractArc bottomCount (processArcSpineFaithful stateRight rest) := by
  induction equiv with
  | ofR19 inner => exact extractArc_eq_of_faithfulReorderEquiv bottomCount rest inner
  | ofCapCapSwap state fresh forest nextFreshPos boundaryBelowFresh gap positionLow
      lowWindowFits admissible =>
      exact arcFaithfulCapCapSuffixExtractCommute state fresh forest nextFreshPos bottomCount
        boundaryBelowFresh gap positionLow lowWindowFits rest admissible
  | symm _ ih => exact ih.symm
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight

/-! ## Non-vacuity — fires on ALL FOUR partition-swap families + a MIXED witness -/

/-- ★ **CAP x CAP fire (the new arm).**  The cap-cap swap on the width-6 fresh seed at `gap = 2`,
`positionLow = 0` followed by the crossing suffix `[crossAtom]`, lifted to the sibling relation. -/
theorem capCapReorder_witness :
    FaithfulReorderEquivWithCapCap 6 [crossAtom]
      (stepCapArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0))
      (stepCapArc (stepCapArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) :=
  faithfulReorder_ofCapCap 6 [crossAtom] cupCupSuffixProbeSeed (arcStateFresh_initial 6)
    isUnionFindForest_nil (by decide) (by decide) 2 0 (by decide)
    ⟨Or.inr ⟨crossAtom_generatorDom_length, crossAtom_generatorCod_length, by decide⟩, trivial⟩

/-- ★ **The extended closure FIRES on the cap-cap swap.**  The two cap-cap run orders extract EQUALLY after the
crossing-carrying faithful suffix — the r20 headline, a suffix the shipped engine's corrupt box arm could not
carry. -/
theorem capCapReorder_extractEq :
    extractArc 6
        (processArcSpineFaithful (stepCapArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0)) [crossAtom])
      = extractArc 6
          (processArcSpineFaithful (stepCapArc (stepCapArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) [crossAtom]) :=
  extractArc_eq_of_faithfulReorderEquivWithCapCap 6 [crossAtom] capCapReorder_witness

/-- ★ **Refl-failure probe (cap-cap): the two run states GENUINELY DIFFER in `links`.**  Both caps drop the
same surviving wires, so the `openWires` COINCIDE — the join-order difference lives entirely in the union-find
`links`.  So `capCapReorder_extractEq` is content-bearing: the extract equality is the partition-fold absorbing
a real, non-identity join-order difference, not `rfl` on the states.  By `decide` on the concrete link lists. -/
theorem capCapReorder_statesDiffer :
    (processArcSpineFaithful
        (stepCapArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0)) [crossAtom]).links
      ≠ (processArcSpineFaithful
          (stepCapArc (stepCapArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) [crossAtom]).links := by
  decide

/-- ★ **CUP x CUP fire (through the r19 embedding).**  The cup-cup swap re-expressed through `ofR19`; the
extended closure fires on it, recovering the r19 delivery through the SIBLING relation. -/
theorem cupCupReorder_extractEq :
    extractArc 6
        (processArcSpineFaithful
          (stepCupArc (stepCupArc cupCupSuffixProbeSeed 0) (2 + 2 + 0)) [crossAtom])
      = extractArc 6
          (processArcSpineFaithful
            (stepCupArc (stepCupArc cupCupSuffixProbeSeed (2 + 0)) 0) [crossAtom]) :=
  extractArc_eq_of_faithfulReorderEquivWithCapCap 6 [crossAtom]
    (reorderWithCapCap_of_faithfulReorder 6 [crossAtom]
      (faithfulReorder_ofCupCup 6 [crossAtom] cupCupSuffixProbeSeed (arcStateFresh_initial 6)
        isUnionFindForest_nil (by decide) (by decide) 2 0 (by decide)
        ⟨Or.inr ⟨crossAtom_generatorDom_length, crossAtom_generatorCod_length, by decide⟩, trivial⟩))

/-- ★ **Refl-failure probe (cup-cup): the two run states GENUINELY DIFFER in `openWires`.**  The cups allocate
fresh wires at different positions in the two orders. -/
theorem cupCupReorder_statesDiffer :
    (processArcSpineFaithful
        (stepCupArc (stepCupArc cupCupSuffixProbeSeed 0) (2 + 2 + 0)) [crossAtom]).openWires
      ≠ (processArcSpineFaithful
          (stepCupArc (stepCupArc cupCupSuffixProbeSeed (2 + 0)) 0) [crossAtom]).openWires := by
  decide

/-- ★ **CUP x CAP fire (via the engine-generic port directly).**  The cup-cap partition package is proven at
the partition level; the engine-generic faithful peel fires on it after the crossing suffix.  Kept as a direct
port fire, NOT an inductive arm — the r20 sibling adds ONLY the cap-cap arm. -/
theorem cupCapSuffixExtractCommute :
    extractArc 6
        (processArcSpineFaithful
          (stepCapArc (stepCupArc cupCupSuffixProbeSeed 0) (2 + 2 + 0)) [crossAtom])
      = extractArc 6
          (processArcSpineFaithful
            (stepCupArc (stepCapArc cupCupSuffixProbeSeed (2 + 0)) 0) [crossAtom]) :=
  extractArc_eq_rest_faithful_of_swapCorePackage 6 _ _
    (arcSwapCorePackage_cupCap cupCupSuffixProbeSeed (arcStateFresh_initial 6) isUnionFindForest_nil
      (by decide) 6 (by decide) 2 0 (by decide)) [crossAtom]
    ⟨Or.inr ⟨crossAtom_generatorDom_length, crossAtom_generatorCod_length, by decide⟩, trivial⟩

/-- ★ **Refl-failure probe (cup-cap): the two run states GENUINELY DIFFER in `openWires`.** -/
theorem cupCapSuffix_statesDiffer :
    (processArcSpineFaithful
        (stepCapArc (stepCupArc cupCupSuffixProbeSeed 0) (2 + 2 + 0)) [crossAtom]).openWires
      ≠ (processArcSpineFaithful
          (stepCupArc (stepCapArc cupCupSuffixProbeSeed (2 + 0)) 0) [crossAtom]).openWires := by
  decide

/-- ★ **CAP x CUP fire (via the engine-generic port directly).**  The dual of `cupCapSuffixExtractCommute`. -/
theorem capCupSuffixExtractCommute :
    extractArc 6
        (processArcSpineFaithful
          (stepCupArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0)) [crossAtom])
      = extractArc 6
          (processArcSpineFaithful
            (stepCapArc (stepCupArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) [crossAtom]) :=
  extractArc_eq_rest_faithful_of_swapCorePackage 6 _ _
    (arcSwapCorePackage_capCup cupCupSuffixProbeSeed (arcStateFresh_initial 6) isUnionFindForest_nil
      (by decide) 6 (by decide) 2 0 (by decide)) [crossAtom]
    ⟨Or.inr ⟨crossAtom_generatorDom_length, crossAtom_generatorCod_length, by decide⟩, trivial⟩

/-- ★ **Refl-failure probe (cap-cup): the two run states GENUINELY DIFFER in `openWires`.** -/
theorem capCupSuffix_statesDiffer :
    (processArcSpineFaithful
        (stepCupArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0)) [crossAtom]).openWires
      ≠ (processArcSpineFaithful
          (stepCapArc (stepCupArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) [crossAtom]).openWires := by
  decide

/-- ★ **The MIXED multi-step cap-cap reorder witness.**  A three-node `trans` chain over the width-6 seed with
the crossing suffix `[crossAtom]`: a literal re-expression at the cap-cap redex (`ofR19 (ofLiteralSwap rfl)`),
the GENUINE cap-cap partition renaming (`ofCapCapSwap`, endpoints differing by the fresh-block transposition),
and a second literal re-expression at the reduct.  Composed by `trans` — exercising the `ofR19`, `ofCapCapSwap`
and `trans` arms in one derivation. -/
theorem mixedCapCapReorderWitness :
    FaithfulReorderEquivWithCapCap 6 [crossAtom]
      (stepCapArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0))
      (stepCapArc (stepCapArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) :=
  (FaithfulReorderEquivWithCapCap.ofR19 (FaithfulReorderEquiv.ofLiteralSwap rfl)).trans
    (capCapReorder_witness.trans
      (FaithfulReorderEquivWithCapCap.ofR19 (FaithfulReorderEquiv.ofLiteralSwap rfl)))

/-- ★ **The extended closure FIRES on the MIXED cap-cap reorder.** -/
theorem mixedCapCapReorder_extractEq :
    extractArc 6
        (processArcSpineFaithful (stepCapArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0)) [crossAtom])
      = extractArc 6
          (processArcSpineFaithful (stepCapArc (stepCapArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) [crossAtom]) :=
  extractArc_eq_of_faithfulReorderEquivWithCapCap 6 [crossAtom] mixedCapCapReorderWitness

/-- ★ **Refl-failure probe (mixed): the two endpoint run states GENUINELY DIFFER in `links`.** -/
theorem mixedCapCapReorder_statesDiffer :
    (processArcSpineFaithful
        (stepCapArc (stepCapArc cupCupSuffixProbeSeed 0) (2 + 0)) [crossAtom]).links
      ≠ (processArcSpineFaithful
          (stepCapArc (stepCapArc cupCupSuffixProbeSeed (2 + 2 + 0)) 0) [crossAtom]).links := by
  decide

/-! ## Honesty marker + permanent-false pins -/

/-- ★ **Honesty marker — the CAP x CAP faithful reorder-closure extract invariance is SHIPPED.**
`FaithfulReorderEquivWithCapCap bottomCount rest` embeds the whole r19 closure through `ofR19` and adds the
CAP x CAP partition arm `ofCapCapSwap` off `arcSwapCorePackage_capCap` (native representative-free core);
`extractArc_eq_of_faithfulReorderEquivWithCapCap` proves the extract-after-`rest` INVARIANT along the WHOLE
sibling closure over the FAITHFUL engine.  Non-vacuous on all FOUR partition-swap families
(`capCapReorder_extractEq` / `cupCupReorder_extractEq` / `cupCapSuffixExtractCommute` /
`capCupSuffixExtractCommute`) and a MIXED multi-step witness (`mixedCapCapReorder_extractEq`), each with a
decide-confirmed refl-failure probe (cap-cap and mixed differ in `links` — the `openWires` coincide;
cup-cup / cup-cap / cap-cup differ in `openWires`).  HONEST SCOPE: this is the STATE+KIND swap granularity over
the faithful engine; the cap wall is real ONLY at the ROOT-LEVEL renaming vehicle (`rootComm`), which the
partition core sidesteps.  It does NOT build the general-CELL peel `ArcGodementSamePartitionFresh` and does NOT
prove the root-level renaming witness.  The shipped r19 relation and its marker are byte-intact.  `= true`. -/
def fxMode_hasArcFaithfulReorderCapCapExtractInvariance : Bool := true

/-- **Honesty pin — the general-signature peel stays the open keystone.**  The cap-cap sibling does not build
the crossing-inclusive general block-swap witness over arbitrary faithful cells;
`fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcFaithfulReorderCapCapClosure_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**  The mode-side general-
signature peel `ArcGodementSamePartitionFresh` lives out of lane; this file does not advance it.
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcFaithfulReorderCapCapClosure_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the root-level renaming vehicle stays PERMANENTLY refuted.**  The cap-cap sibling rides the
representative-free PARTITION core, which sidesteps the cap-cap root flip; it does NOT resurrect the root-level
renaming vehicle `rootComm`, which is machine-refuted at the join-order flip (`ArcCoreSwapCapFlipRefutation`).
`fxMode_hasArcGodementSwapRenameableProof2` stays `false` PERMANENTLY.  `rfl`. -/
theorem arcFaithfulReorderCapCapClosure_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
