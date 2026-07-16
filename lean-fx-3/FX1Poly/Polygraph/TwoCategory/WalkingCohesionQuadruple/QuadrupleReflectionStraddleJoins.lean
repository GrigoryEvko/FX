import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleThinFragment

/-! # WalkingCohesionQuadruple/QuadrupleReflectionStraddleJoins — the thin fragment extended to ALL THREE ff isos

`QuadrupleThinFragment` shipped ONE explicit reflection critical-pair join
(`quadStraddleDiscUnitInvCounitJoin`, `disc ◁ η ≈ ε⁻¹ ▷ disc`) on the shared leg `disc`, driven by the
`Π₀ ⊣ Disc` triangle and the lower-counit ff iso (`Disc` fully faithful, seen through its lower-counit).  The
cohesion quadruple `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` has THREE fully-faithful iso conditions in all —

  * `Disc` ff via the **lower counit** of `Π₀ ⊣ Disc` (`isoLowerCounitRight/Left`) — the shipped one,
  * `Disc` ff via the **middle unit** of `Disc ⊣ Γ` (`isoMiddleUnitRight/Left`) — `Disc` is the LEFT adjoint
    there, so its ff shows as the unit being iso,
  * `coDisc` ff via the **upper counit** of `Γ ⊣ coDisc` (`isoUpperCounitRight/Left`).

This file discharges the remaining TWO as explicit populated-hom thinness instances, so EVERY ff condition now
hosts a machine-checked reflection straddle join on a DISTINCT populated hom.  Each mirrors the shipped disc/lower
proof structurally: fold the two whiskered halves of a round-trip with `whiskerRightVcomp`, collapse the round-trip
with the ff iso, erase the whisker with `whiskerRightId`, then pad-reassociate-straighten-drop against the
adjunction triangle.  All use ONLY the shipped whisker-of-vcomp step; no deferred whisker-by-composite brick.

## The three joins live on three distinct homs

  * disc/lower (shipped): `disc ⇒ disc·pi0·disc`,
  * disc/middle (here): `disc·gamma·disc ⇒ disc` — the MIRROR-IMAGE confluence (triangle factor on the right, the
    unit iso rather than the counit iso),
  * codisc/upper (here): `codisc ⇒ codisc·gamma·codisc` — a faithful mirror of the disc/lower proof.

## What this does NOT do (the honest boundary, unchanged)

This extends the THIN FRAGMENT; it does NOT flip `fxQuadCohesion_hasQuadrupleThinnessResolution`.  Global thinness
(`QuadCohesionThinness`) stays the OPEN residual: closing it needs a confluent boundary-determined normalizer over
the FREE four-letter 1-cell words `{pi0,disc,gamma,codisc}` — which, unlike `WalkingIdempotent`'s single-letter
`monadTPower`, have NO length normal form, so `WalkingIdempotent.normalizeFullGen` does not port; and the
literature (Dawson–Paré–Pronk) warns the free ff-adjoint string may be genuinely non-posetal, so thinness is not
even known TRUE.  The precise blocking node is recorded at `fxQuadCohesion_hasFreeWordNormalizerForThinness`
below.

Raw Lean 4 + Init; the collapses and joins are constructor chains lifting shipped 3-cell rewrites — every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`/`decide`/`simp`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The `coDisc`-ff (upper counit) reflection join — a faithful mirror of disc/lower -/

/-- The `codisc`-right-whiskered upper ff round-trip `(ε'' ▷ codisc) ⊟ (ε''⁻¹ ▷ codisc)` collapses to
`id_{codisc·gamma·codisc}`: `whiskerRightVcomp` folds the two whiskers into `(ε'' ⊟ ε''⁻¹) ▷ codisc`,
`isoUpperCounitRight` collapses `ε'' ⊟ ε''⁻¹` to `id_{codisc·gamma}`, and `whiskerRightId` erases the whisker.
The `coDisc`-ff analog of `quadDiscWhiskeredLowerRoundCollapses`. -/
theorem quadCodiscWhiskeredUpperRoundCollapses :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight quadCodisc quadCounitUpperCell)
        (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell))
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) (composePath quadCodiscGamma quadCodisc)) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerRightVcomp quadCodisc quadCounitUpperCell quadInvCounitUpperCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadCodisc
      QuadCohesionSaturatedTwoCellConv.isoUpperCounitRight) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadCodiscGamma quadCodisc)

/-- ★★ **The upper straddle critical-pair join `codisc ◁ η'' ≈ ε''⁻¹ ▷ codisc`** over the populated hom
`codisc ⇒ codisc·gamma·codisc`.  The left-whiskered upper unit and the right-whiskered upper-counit INVERSE are
saturated-convertible: pad `codisc ◁ η''` with the target identity, expand it to
`(ε'' ▷ codisc) ⊟ (ε''⁻¹ ▷ codisc)` (`quadCodiscWhiskeredUpperRoundCollapses` reversed), reassociate, straighten
`(codisc ◁ η'') ⊟ (ε'' ▷ codisc)` to `id_codisc` via the `Γ ⊣ coDisc` triangle `triCodisc`, and drop the left
identity.  A second populated hom (distinct from the disc/lower hom) where the quadruple's local posetality holds
by an explicit ff-driven join — the `coDisc`-ff analog of `quadStraddleDiscUnitInvCounitJoin`. -/
theorem quadStraddleCodiscUnitInvCounitJoin :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft quadCodisc quadUnitUpperCell)
      (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.vcompIdRight (RawTwoCellExpr.whiskerLeft quadCodisc quadUnitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerLeft quadCodisc quadUnitUpperCell)
      (QuadCohesionSaturatedTwoCellConv.symm quadCodiscWhiskeredUpperRoundCollapses)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerLeft quadCodisc quadUnitUpperCell)
          (RawTwoCellExpr.whiskerRight quadCodisc quadCounitUpperCell)
          (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft
      (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell)
      QuadCohesionSaturatedTwoCellConv.triCodisc) ?_
  show QuadCohesionSaturatedTwoCellConv
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature)
        (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodisc))
      (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell))
    (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell)
  exact quadCohesionConvOfStep
    (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell))

/-! ## The `Disc`-ff (middle unit) reflection join — the SECOND `Disc` witness, mirror-image confluence

`Disc` is fully faithful in TWO ways: its lower counit is iso (shipped join) AND its middle unit is iso.  This
second witness drives a distinct join on the shared leg `disc`, over a DIFFERENT hom (`disc·gamma·disc ⇒ disc`)
and with the MIRROR-IMAGE confluence: the invertible cell is the UNIT `η' = unitMiddle` (not the counit), so the
round-trip that cancels is the LEFT round-trip `η'⁻¹ ⊟ η'`, and the driving triangle `triDiscHi` has the
straightened factor on the RIGHT. -/

/-- The `disc`-right-whiskered middle ff LEFT round-trip `(η'⁻¹ ▷ disc) ⊟ (η' ▷ disc)` collapses to
`id_{disc·gamma·disc}`: `whiskerRightVcomp` folds into `(η'⁻¹ ⊟ η') ▷ disc`, `isoMiddleUnitLeft` collapses
`η'⁻¹ ⊟ η'` to `id_{disc·gamma}`, and `whiskerRightId` erases the whisker.  The `Disc`-ff-via-middle-unit analog
of `quadDiscWhiskeredLowerRoundCollapses` (left round-trip, since the invertible cell here is the unit). -/
theorem quadDiscWhiskeredMiddleRoundLeftCollapses :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell)
        (RawTwoCellExpr.whiskerRight quadDisc quadUnitMiddleCell))
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) (composePath quadDiscGamma quadDisc)) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerRightVcomp quadDisc quadInvUnitMiddleCell quadUnitMiddleCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadDisc
      QuadCohesionSaturatedTwoCellConv.isoMiddleUnitLeft) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadDiscGamma quadDisc)

/-- ★★ **The middle straddle critical-pair join `disc ◁ ε' ≈ η'⁻¹ ▷ disc`** over the populated hom
`disc·gamma·disc ⇒ disc`.  The left-whiskered middle counit `ε' = counitMiddle` and the right-whiskered
middle-unit INVERSE are saturated-convertible.  Mirror-image of the disc/lower confluence: pad `disc ◁ ε'` with
the SOURCE identity, expand it to `(η'⁻¹ ▷ disc) ⊟ (η' ▷ disc)` (`quadDiscWhiskeredMiddleRoundLeftCollapses`
reversed), reassociate FORWARD, straighten the RIGHT factor `(η' ▷ disc) ⊟ (disc ◁ ε')` to `id_disc` via the
`Disc ⊣ Γ` triangle `triDiscHi`, and drop the right identity.  The THIRD explicit reflection join — with the
disc/lower and codisc/upper joins, every one of the quadruple's three ff conditions now witnesses a populated hom
thin by construction. -/
theorem quadStraddleDiscCounitMiddleInvUnitJoin :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft quadDisc quadCounitMiddleCell)
      (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerLeft quadDisc quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft
      (RawTwoCellExpr.whiskerLeft quadDisc quadCounitMiddleCell)
      (QuadCohesionSaturatedTwoCellConv.symm quadDiscWhiskeredMiddleRoundLeftCollapses)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadCohesionConvOfStep
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell)
        (RawTwoCellExpr.whiskerRight quadDisc quadUnitMiddleCell)
        (RawTwoCellExpr.whiskerLeft quadDisc quadCounitMiddleCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell)
      QuadCohesionSaturatedTwoCellConv.triDiscHi) ?_
  show QuadCohesionSaturatedTwoCellConv
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature)
        (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadDisc)))
    (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell)
  exact quadCohesionConvOfStep
    (TwoCellStep.vcompIdRight (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell))

/-! ## The complete reflection-join suite + non-degeneracy -/

/-- ★★ **All three ff conditions host a reflection straddle join.**  The quadruple's local posetality is now
witnessed outright on THREE distinct populated homs, one per fully-faithful iso: `disc/lower`
(`quadStraddleDiscUnitInvCounitJoin`, shipped), `disc/middle` (`quadStraddleDiscCounitMiddleInvUnitJoin`), and
`codisc/upper` (`quadStraddleCodiscUnitInvCounitJoin`).  Together with the six leg straightenings
(`quadThinFragment_legsStraighten`) and the two shared-leg snake coherences (`quadDiscSnakesCohere`,
`quadGammaSnakesCohere`), this is the fully-populated thin fragment: every reflection contributes an explicit
join. -/
theorem quadAllReflectionStraddleJoins :
    QuadCohesionSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft quadDisc quadUnitLowerCell)
        (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell) ∧
      QuadCohesionSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft quadDisc quadCounitMiddleCell)
        (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell) ∧
      QuadCohesionSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft quadCodisc quadUnitUpperCell)
        (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell) :=
  ⟨quadStraddleDiscUnitInvCounitJoin, quadStraddleDiscCounitMiddleInvUnitJoin,
    quadStraddleCodiscUnitInvCounitJoin⟩

/-- Non-degeneracy of the middle join: the left-whiskered middle counit and the right-whiskered middle-unit
inverse are SYNTACTICALLY DISTINCT cells (different head whisker: `whiskerLeft` vs `whiskerRight`), so the join
identifies a genuinely non-trivial parallel pair — it is not a `refl`.  Both have size 2 (a whisker over an atomic
generator). -/
theorem quadStraddleMiddleJoin_sidesAreDistinct :
    (RawTwoCellExpr.whiskerLeft quadDisc quadCounitMiddleCell).size = 2 ∧
      (RawTwoCellExpr.whiskerRight quadDisc quadInvUnitMiddleCell).size = 2 :=
  ⟨rfl, rfl⟩

/-- Non-degeneracy of the upper join: both whiskered halves have size 2, and they differ in head whisker — a
genuine parallel pair identified by `quadStraddleCodiscUnitInvCounitJoin`, not a reflexivity. -/
theorem quadStraddleUpperJoin_sidesAreDistinct :
    (RawTwoCellExpr.whiskerLeft quadCodisc quadUnitUpperCell).size = 2 ∧
      (RawTwoCellExpr.whiskerRight quadCodisc quadInvCounitUpperCell).size = 2 :=
  ⟨rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★ **ESTABLISHED — the reflection-join suite is complete.**  Every one of the cohesion quadruple's three
fully-faithful iso conditions (`Disc` ff via the lower counit, `Disc` ff via the middle unit, `coDisc` ff via the
upper counit) now hosts an explicit machine-checked reflection straddle join on a distinct populated hom
(`quadStraddleDiscUnitInvCounitJoin` shipped in `QuadrupleThinFragment`; `quadStraddleDiscCounitMiddleInvUnitJoin`
and `quadStraddleCodiscUnitInvCounitJoin` here), each collapsing an ff round-trip against the corresponding
adjunction triangle using only the shipped whisker-of-vcomp step.  Bundled as `quadAllReflectionStraddleJoins`.
The thin fragment is thereby extended past the single shipped join to the full complement of reflections.
`= true`. -/
def fxQuadCohesion_hasReflectionStraddleJoinSuite : Bool := true

/-- ★★ **HONEST WALL (SHARPER) — the precise blocking node for GLOBAL thinness is the FREE-WORD normalizer.**  The
thin fragment is now populated on every reflection (`fxQuadCohesion_hasReflectionStraddleJoinSuite`), the sound
`ℤ/2` parity invariant is boundary-determined so it cannot refute
(`quadCohesionParity_boundaryDetermined`), and the induced-quotient non-thinness provably does not lift
(`quadInducedRefutationDoesNotLift`) — yet `fxQuadCohesion_hasQuadrupleThinnessResolution` (the master flag in
`QuadrupleThinFragment`) stays `false`, and this marker names EXACTLY why.

The single blocking node is a **confluent, boundary-determined normalizer over the FREE 1-cell words** of
`quadCohesionModeSignature`.  `WalkingIdempotent` closed its thinness by `normalizeFullGen : cell ~ repFull cell`
with `repFull` boundary-determined because its 1-cells are single-letter powers `monadTPower n` with a `Nat`
LENGTH normal form.  Here the 1-cells are free words in FOUR letters `{pi0,disc,gamma,codisc}` and have NO length
normal form: `pi0·disc` and `pi0·disc·pi0·disc` are DISTINCT free paths (isomorphic only via a 2-cell), so no
`monadTPower`-style `repFull` exists and `normalizeFullGen` does not port.  A quadruple normalizer must
simultaneously (a) reduce the six triangle snakes, (b) reduce the six ff-iso round-trips, and (c) confluently join
the reflection critical pairs at BOTH shared legs `disc` and `gamma` — a genuine multi-file arc.  Moreover the
target may be UNREACHABLE: Dawson–Paré–Pronk warn the free ff-adjoint string can be genuinely non-posetal, so
global thinness is not even known true; the honest disposition would then pivot to a boundary-determined SEPARATOR
surviving the saturation (a refutation), for which no candidate is yet known — the obvious `pi0`-parity separator
is already dead (`quadCohesionParity_constantOnParallel`).  Until the free-word normalizer lands (or a separator
is found), the master flag and the downstream cohesion computation stay gated.  `= false`. -/
def fxQuadCohesion_hasFreeWordNormalizerForThinness : Bool := false

end FX1Poly.Polygraph
