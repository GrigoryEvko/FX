import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineReadback
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # mode-3 — the whisker re-framing kit (atom-level whisker-context manipulation)

The completeness reconstruction rebuilds WHISKERED cells from their spine/matching data: the
readback's per-atom frame is `leftContext ◁ (rightContext ▷ gen generator)` (`atomFrame`), and
the reconstruction's whisker cases must PUSH an outer whisker context INTO each atom — converting
between the one-big-whisker and iterated-whisker presentations of the same atom.  This file ships
that conversion kit at full signature generality, over the completed convertibility
`TwoCellConvFull` (which now hosts ALL FIVE whisker-functoriality laws: the two unit collapses,
the two composite splits, and the disjoint-whisker exchange).

  * `SpineAtom.extendLeft` / `SpineAtom.extendRight` — the atom with its whiskering context
    extended by an outer 1-cell (the data-level shadow of whiskering the frame);
  * `RawTwoCellExpr.castBoundary_castBoundary` — boundary casts FUSE;
  * `RawTwoCellExpr.whiskerLeft_castBoundary` / `whiskerRight_castBoundary` — whiskering
    commutes with a boundary cast;
  * `TwoCellConvFull.ofCastLeft` — move a boundary cast across the relation;
  * `TwoCellConvFull.castBoundaryCongr` — the relation transports along a boundary cast;
  * ★ `whiskerLeft_atomFrame_convFull` — LEFT re-framing: whiskering an atom's frame on the
    left is convertible to the frame of the left-extended atom (`whiskerLeftComp`);
  * ★ `whiskerRight_atomFrame_convFull` — RIGHT re-framing: whiskering an atom's frame on the
    right is convertible to the frame of the right-extended atom (`whiskerExchange` pushes the
    right whisker through the frame's left context, then `whiskerRightComp` merges).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin (the cast
helpers are `cases` on the boundary equalities — every cast collapses definitionally on
`refl`; the two re-framing theorems are constructor plumbing). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Atom context extension -/

/-- The atom with its LEFT whiskering context extended by an outer 1-cell — the data-level
shadow of `whiskerLeft outer` on the atom's frame. -/
def SpineAtom.extendLeft {signature : ModeSignature}
    {newSourceMode sourceMode targetMode : signature.graph.Mode}
    (outer : ModalityPath signature.graph newSourceMode sourceMode)
    (atom : SpineAtom signature sourceMode targetMode) :
    SpineAtom signature newSourceMode targetMode :=
  { leftMidMode := atom.leftMidMode
    rightMidMode := atom.rightMidMode
    leftContext := composePath outer atom.leftContext
    generatorDom := atom.generatorDom
    generatorCod := atom.generatorCod
    generator := atom.generator
    rightContext := atom.rightContext }

/-- The atom with its RIGHT whiskering context extended by an outer 1-cell — the data-level
shadow of `whiskerRight outer` on the atom's frame. -/
def SpineAtom.extendRight {signature : ModeSignature}
    {sourceMode targetMode newTargetMode : signature.graph.Mode}
    (outer : ModalityPath signature.graph targetMode newTargetMode)
    (atom : SpineAtom signature sourceMode targetMode) :
    SpineAtom signature sourceMode newTargetMode :=
  { leftMidMode := atom.leftMidMode
    rightMidMode := atom.rightMidMode
    leftContext := atom.leftContext
    generatorDom := atom.generatorDom
    generatorCod := atom.generatorCod
    generator := atom.generator
    rightContext := composePath atom.rightContext outer }

/-! ## Boundary-cast algebra -/

/-- Boundary casts FUSE: two successive casts are the cast along the composite equalities. -/
theorem RawTwoCellExpr.castBoundary_castBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' sourcePath'' targetPath targetPath' targetPath'' :
      ModalityPath signature.graph sourceMode targetMode}
    (hsourceFirst : sourcePath = sourcePath') (htargetFirst : targetPath = targetPath')
    (hsourceSecond : sourcePath' = sourcePath'') (htargetSecond : targetPath' = targetPath'')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    RawTwoCellExpr.castBoundary hsourceSecond htargetSecond
        (RawTwoCellExpr.castBoundary hsourceFirst htargetFirst cell)
      = RawTwoCellExpr.castBoundary (hsourceFirst.trans hsourceSecond)
          (htargetFirst.trans htargetSecond) cell := by
  cases hsourceFirst; cases htargetFirst; cases hsourceSecond; cases htargetSecond; rfl

/-- LEFT whiskering commutes with a boundary cast (the cast's equalities pick up the whiskering
1-cell by `congrArg`). -/
theorem RawTwoCellExpr.whiskerLeft_castBoundary {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph middleMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.castBoundary hsource htarget cell)
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCell) hsource)
          (congrArg (composePath oneCell) htarget)
          (RawTwoCellExpr.whiskerLeft oneCell cell) := by
  cases hsource; cases htarget; rfl

/-- RIGHT whiskering commutes with a boundary cast. -/
theorem RawTwoCellExpr.whiskerRight_castBoundary {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode middleMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.castBoundary hsource htarget cell)
      = RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path oneCell) hsource)
          (congrArg (fun path => composePath path oneCell) htarget)
          (RawTwoCellExpr.whiskerRight oneCell cell) := by
  cases hsource; cases htarget; rfl

/-- Move a boundary cast ACROSS the relation: if the cast cell converts, the bare cell converts
to the inversely-cast partner. -/
theorem TwoCellConvFull.ofCastLeft {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha : RawTwoCellExpr signature sourcePath targetPath}
    {cellBeta : RawTwoCellExpr signature sourcePath' targetPath'}
    (conv : TwoCellConvFull signature
      (RawTwoCellExpr.castBoundary hsource htarget cellAlpha) cellBeta) :
    TwoCellConvFull signature cellAlpha
      (RawTwoCellExpr.castBoundary hsource.symm htarget.symm cellBeta) := by
  cases hsource; cases htarget; exact conv

/-- The relation transports along a boundary cast on BOTH sides. -/
theorem TwoCellConvFull.castBoundaryCongr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConvFull signature cellAlpha cellBeta) :
    TwoCellConvFull signature (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact conv

/-! ## The atom re-framing pair -/

/-- ★ **LEFT re-framing**: whiskering an atom's frame on the left is `TwoCellConvFull` to the
frame of the LEFT-EXTENDED atom — `whiskerLeftComp` read in reverse merges the outer whisker
into the atom's stored left context. -/
theorem whiskerLeft_atomFrame_convFull {signature : ModeSignature}
    {newSourceMode sourceMode targetMode : signature.graph.Mode}
    (outer : ModalityPath signature.graph newSourceMode sourceMode)
    (atom : SpineAtom signature sourceMode targetMode) :
    TwoCellConvFull signature
      (RawTwoCellExpr.whiskerLeft outer (atomFrame atom))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc outer atom.leftContext
          (composePath atom.generatorDom atom.rightContext))
        (composePath_assoc outer atom.leftContext
          (composePath atom.generatorCod atom.rightContext))
        (atomFrame (SpineAtom.extendLeft outer atom))) :=
  TwoCellConvFull.ofCastLeft
    (composePath_assoc outer atom.leftContext
      (composePath atom.generatorDom atom.rightContext)).symm
    (composePath_assoc outer atom.leftContext
      (composePath atom.generatorCod atom.rightContext)).symm
    (TwoCellConvFull.symm (TwoCellConvFull.whiskerLeftComp outer atom.leftContext
      (RawTwoCellExpr.whiskerRight atom.rightContext (RawTwoCellExpr.gen atom.generator))))

/-- ★ **RIGHT re-framing**: whiskering an atom's frame on the right is `TwoCellConvFull` to the
frame of the RIGHT-EXTENDED atom — the disjoint-whisker EXCHANGE pushes the outer right whisker
through the frame's left context, then `whiskerRightComp` read in reverse merges it into the
atom's stored right context. -/
theorem whiskerRight_atomFrame_convFull {signature : ModeSignature}
    {sourceMode targetMode newTargetMode : signature.graph.Mode}
    (outer : ModalityPath signature.graph targetMode newTargetMode)
    (atom : SpineAtom signature sourceMode targetMode) :
    TwoCellConvFull signature
      (RawTwoCellExpr.whiskerRight outer (atomFrame atom))
      (RawTwoCellExpr.castBoundary
        ((congrArg (composePath atom.leftContext)
            (composePath_assoc atom.generatorDom atom.rightContext outer).symm).trans
          (composePath_assoc atom.leftContext
            (composePath atom.generatorDom atom.rightContext) outer).symm)
        ((congrArg (composePath atom.leftContext)
            (composePath_assoc atom.generatorCod atom.rightContext outer).symm).trans
          (composePath_assoc atom.leftContext
            (composePath atom.generatorCod atom.rightContext) outer).symm)
        (atomFrame (SpineAtom.extendRight outer atom))) := by
  refine TwoCellConvFull.trans
    (TwoCellConvFull.ofCastLeft
      (composePath_assoc atom.leftContext
        (composePath atom.generatorDom atom.rightContext) outer)
      (composePath_assoc atom.leftContext
        (composePath atom.generatorCod atom.rightContext) outer)
      (TwoCellConvFull.symm (TwoCellConvFull.whiskerExchange atom.leftContext outer
        (RawTwoCellExpr.whiskerRight atom.rightContext (RawTwoCellExpr.gen atom.generator))))) ?_
  have nestedReframe := TwoCellConvFull.whiskerLeftCongr atom.leftContext
    (TwoCellConvFull.ofCastLeft
      (composePath_assoc atom.generatorDom atom.rightContext outer)
      (composePath_assoc atom.generatorCod atom.rightContext outer)
      (TwoCellConvFull.symm (TwoCellConvFull.whiskerRightComp atom.rightContext outer
        (RawTwoCellExpr.gen atom.generator))))
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at nestedReframe
  have castCongr := TwoCellConvFull.castBoundaryCongr
    (composePath_assoc atom.leftContext
      (composePath atom.generatorDom atom.rightContext) outer).symm
    (composePath_assoc atom.leftContext
      (composePath atom.generatorCod atom.rightContext) outer).symm
    nestedReframe
  rw [RawTwoCellExpr.castBoundary_castBoundary] at castCongr
  exact castCongr

/-! ## Honesty marker -/

/-- **Honesty marker — the whisker re-framing kit is SHIPPED, signature-generic.**  All five
whisker-functoriality laws live on `TwoCellConvFull` (`whiskerLeftUnit` / `whiskerRightUnit` /
`whiskerLeftComp` / `whiskerRightComp` / `whiskerExchange`), and the atom-level re-framing pair
(`whiskerLeft_atomFrame_convFull` / `whiskerRight_atomFrame_convFull`) converts an outer whisker
of a spine atom's frame into the frame of the context-extended atom — the per-atom step the
chain-level reconstruction consumes.  The chain transforms themselves (whisker actions on
boundary-coherent chains) are the realized-chain bridge's work, not this kit's.  `= true`. -/
def fxMode_hasWhiskerReframingKit : Bool := true

end FX1Poly.Polygraph
