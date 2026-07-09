import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSaturatedConv

/-! # WalkingIdempotent/IdempotentMonadModel — the two-element chain `{0 ≤ 1}` model and boundary soundness

The walking idempotent monad's 1-cells collapse under `mu` iso: `t.t ≅ t`, so every `t^n` with `n ≥ 1` is
isomorphic to `t`, and the 1-cells reduce to two classes — the identity `t^0` and `t` — the "walking idempotent
monoid", the ordinal **2** = `{0 ≤ 1}`.  This file ships that model: the width collapse `t^0 ↦ 0`, `t^{n+1} ↦ 1`
and the poset order on `{0 ≤ 1}`, validates the four generators against it, and gives the BOUNDARY soundness of
the model under convertibility.

## Why soundness here is the DEGENERATE (boundary-only) direction

Because `mu` is iso, `hom(t^m, t^n)` has AT MOST ONE 2-cell (Lack, "locally posetal") — the 2-cell carries NO data
beyond its boundary `(min(m,1), min(n,1))`.  So the model image of a 2-cell depends ONLY on its source/target
paths, which any convertibility already shares: soundness `mapEqOfConv` is trivially `rfl`, and it gives NO
decision power.  The genuine content is the CONVERSE — every parallel pair really is convertible (thinness / local
posetality) — which is `IdempotentMonadDecision`.  This is the honest analog of the walking monad's
`MonadSaturatedCanonicalization` where the SOUND half is easy and the COMPLETE half (`convOfMapEq`) is the weight.

Raw Lean 4 + Init; the collapse is a structural `Nat` recursion and the boundary map reads only the index, so every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The two-element chain `{0 ≤ 1}` -/

/-- The width bit of a natural: `0 ↦ false` (the `0` of the chain), any successor `↦ true` (the `1`).  Structural
`Nat` recursion, so its equations are definitional. -/
def natWidthBit : Nat → Bool
  | 0 => false
  | _ + 1 => true

/-- The **width collapse** `t^n ↦ min(n, 1)` as an element of the chain `{0 ≤ 1}` (`Bool`): `t^0 = id ↦ 0`
(`false`), every `t^{n+1} ↦ 1` (`true`) — the `mu`-iso collapse of the idempotent monad's 1-cells. -/
def monadWidthCollapse (path : ModalityPath monadGraph MonadMode.point MonadMode.point) : Bool :=
  natWidthBit path.length

/-- The order of the chain `{0 ≤ 1}` (`false ≤ true`): `source ≤ target` iff `source = 0` or `target = 1`, i.e.
`!source || target`.  A 2-cell `t^m ⇒ t^n` of the walking idempotent monad exists (uniquely) iff
`idempotentInhabited (collapse t^m) (collapse t^n)`. -/
def idempotentInhabited (source target : Bool) : Bool :=
  (!source) || target

/-! ## Validating the generators against the chain -/

/-- Smoke: the UNIT `eta : id ⇒ t` is an arrow `0 ≤ 1` of the chain (inhabited). -/
theorem idempotentInhabited_unit :
    idempotentInhabited (monadWidthCollapse (ModalityPath.nil (graph := monadGraph) MonadMode.point))
      (monadWidthCollapse monadT) = true := rfl

/-- Smoke: the MULTIPLICATION `mu : t.t ⇒ t` is an arrow `1 ≤ 1` (an endo-arrow of the top — `mu` iso). -/
theorem idempotentInhabited_mul :
    idempotentInhabited (monadWidthCollapse monadTThenT) (monadWidthCollapse monadT) = true := rfl

/-- Smoke: BOTH idempotence faces `t ⇒ t.t` are arrows `1 ≤ 1` — parallel with equal endpoints, so the chain
CANNOT tell them apart (it validates the identification `eta ▷ t = t ◁ eta`). -/
theorem idempotentInhabited_idempotenceFaces :
    idempotentInhabited (monadWidthCollapse monadT) (monadWidthCollapse monadTThenT) = true := rfl

/-- ★ Smoke: there is NO arrow `1 ≤ 0` in the chain — no 2-cell `t ⇒ id`.  This is the idempotent monad's rigidity:
`mu` collapses widths but nothing collapses `t` to the identity (the monad has a unit, not a counit). -/
theorem idempotentInhabited_no_collapse_to_identity :
    idempotentInhabited (monadWidthCollapse monadT)
      (monadWidthCollapse (ModalityPath.nil (graph := monadGraph) MonadMode.point)) = false := rfl

/-! ## The boundary image and its (degenerate) soundness -/

/-- The **boundary image** of a free 2-cell in the chain model: the pair `(collapse source, collapse target)` of
its boundary 1-cells.  This is the whole model image — a thin 2-cell carries no further data. -/
def idempotentBoundaryOf {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (_cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) : Bool × Bool :=
  (monadWidthCollapse sourcePath, monadWidthCollapse targetPath)

/-- ★ **Boundary soundness**: convertible cells have equal boundary image.  Degenerate (the boundary reads only the
shared source/target paths of the parallel pair, so it holds by `rfl` regardless of the convertibility) — the
honest statement that the chain model's SOUND direction carries no decision power; the content is the converse
(thinness), in `IdempotentMonadDecision`. -/
theorem idempotentBoundaryOf_congr_of_conv {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (_conv : IdempotentMonadSaturatedTwoCellConv cellA cellB) :
    idempotentBoundaryOf cellA = idempotentBoundaryOf cellB := rfl

/-- Smoke: the two idempotence faces `eta ▷ t` and `t ◁ eta` have EQUAL boundary image `(1, 1)` — the model sees
the identification the idempotence law asserts. -/
theorem idempotentBoundaryOf_idempotenceFaces :
    idempotentBoundaryOf monadEtaTCell = idempotentBoundaryOf monadTEtaCell := rfl

/-- Smoke: that common boundary image is `(true, true)` — both faces are arrows `1 ⇒ 1` of the chain. -/
theorem idempotentBoundaryOf_idempotenceFaces_value :
    idempotentBoundaryOf monadEtaTCell = (true, true) := rfl

/-! ## Honesty marker -/

/-- **ESTABLISHED (degenerate direction).**  The two-element chain `{0 ≤ 1}` model (`monadWidthCollapse` +
`idempotentInhabited`) validates all four generators — `eta : 0 ≤ 1`, `mu : 1 ≤ 1`, the two idempotence faces
`1 ⇒ 1` (indistinguishable, as idempotence demands), and NO `1 ⇒ 0` — and its BOUNDARY image is sound under
convertibility (`idempotentBoundaryOf_congr_of_conv`).  This is honestly the EASY half: the image reads only the
boundary, so it decides nothing between parallel cells.  The decision weight is the CONVERSE — local posetality /
thinness — named as the residual in `IdempotentMonadDecision`.  `= true`. -/
def fxIdempotentMonad_hasChainModelBoundarySound : Bool := true

end FX1Poly.Polygraph
