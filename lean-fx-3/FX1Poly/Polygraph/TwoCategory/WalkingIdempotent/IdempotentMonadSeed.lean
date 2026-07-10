import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # WalkingIdempotent/IdempotentMonadSeed — the walking IDEMPOTENT monad: the monad seed plus one equation

The walking IDEMPOTENT monad reuses the walking-monad presentation (`MonadSeed` — one mode, one endo-1-cell `t`,
the unit `eta` and multiplication `mu`) and adds exactly ONE equation making the monad idempotent.  By Street
("The formal theory of monads") / nLab (*idempotent monad*), a monad is idempotent iff any one of the equivalent
conditions holds: `mu : t.t ⇒ t` is a natural ISOMORPHISM; `mu` is (componentwise) monic; the two unit whiskerings
`t ◁ eta` and `eta ▷ t : t ⇒ t.t` are EQUAL (the "well-pointed" condition); the Eilenberg–Moore forgetful functor
is full and faithful.  We take the MINIMAL one — the well-pointedness equation `eta ▷ t = t ◁ eta` — because it
adds NO new generator (unlike positing an inverse `delta : t ⇒ t.t` with two round-trip equations).

## The two faces of idempotence

This file builds the two parallel free 2-cells the idempotence law identifies:

  * **`monadEtaTCell`** `eta ▷ t : t ⇒ t.t`  — the unit whiskered on the RIGHT by `t`,
  * **`monadTEtaCell`** `t ◁ eta : t ⇒ t.t`  — the unit whiskered on the LEFT by `t`.

Both are `t ⇒ t.t` (the whiskering source paths `nil.t` and `t.nil` are each definitionally `t`), so the
idempotence relation between them is well-typed.  Under the walking monad's `Δ₊` model they are the two elements
of `hom_{Δ₊}([1],[2])` (`monadMonotoneMapOf` folds them to the two coface maps `δ_0`, `δ_1`); idempotence
identifies `δ_0 = δ_1`, and that identification makes every hom-category THIN (Lack, *A 2-Categories Companion*:
"locally posetal … at most one 2-cell between parallel 1-cells").

Raw Lean 4 + Init; the cells are free-2-cell expressions, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- **`eta ▷ t`** — the unit whiskered on the RIGHT by `t`: a free 2-cell `t ⇒ t.t` (the source `nil.t` and the
target `t.t` are `monadT` and `monadTThenT` definitionally).  The FIRST face of idempotence; folds to the coface
`δ_0` in the `Δ₊` model. -/
def monadEtaTCell : RawTwoCellExpr monadModeSignature monadT monadTThenT :=
  RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell

/-- **`t ◁ eta`** — the unit whiskered on the LEFT by `t`: a free 2-cell `t ⇒ t.t` (the source `t.nil` is `monadT`
definitionally, the target `t.t` is `monadTThenT`).  The SECOND face of idempotence; folds to the coface `δ_1` in
the `Δ₊` model.  The walking IDEMPOTENT monad's defining equation is `monadEtaTCell ≈ monadTEtaCell`. -/
def monadTEtaCell : RawTwoCellExpr monadModeSignature monadT monadTThenT :=
  RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell

/-! ## Freeness / boundary smokes -/

/-- Smoke: `eta ▷ t` has size `2` (a generator under one whiskering) — a genuine composite, not a bare atom. -/
theorem monadEtaTCell_size : monadEtaTCell.size = 2 := rfl

/-- Smoke: `t ◁ eta` has size `2` — the same shape on the other side. -/
theorem monadTEtaCell_size : monadTEtaCell.size = 2 := rfl

/-- Smoke: the two idempotence faces are SYNTACTICALLY distinct free cells (different head whiskering — `size` is
equal but they are the `whiskerRight` vs `whiskerLeft` of the unit).  Their identification is the CONTENT of the
idempotence law, not a definitional equality. -/
theorem monadEtaTCell_ne_monadTEtaCell_headWhisker :
    monadEtaTCell.isVcompCell = false ∧ monadTEtaCell.isVcompCell = false :=
  ⟨rfl, rfl⟩

end FX1Poly.Polygraph
