import FX1Poly.Tier0.Mode.FreeTwoCellInterchangeFreeDecidable

/-! # mode-3 floor — decidable 2-cell equality, instantiated at the walking-adjunction seed

`FreeTwoCellExprDecidableEq` + `FreeTwoCellInterchangeFreeDecidable` decide free-2-cell syntactic equality and
interchange-free convertibility for ANY signature with decidable generators.  This file instantiates them at
the canonical non-degenerate witness — the affine walking-adjunction seed `adjunctionModeSignature` (`left ⊣
right` with unit / counit generators) — the signature the fib-3 keystone targets.

  * `adjunctionModeDecEq` / `adjunctionModalityDecEq` / `adjunctionTwoCellDecEq` — decidable equality of the
    seed's modes, modality generators (subsingleton homs: at most one generator per parallel boundary), and
    2-cell generators (likewise subsingleton).
  * `adjunctionRawTwoCellDecidableEq` — hence `DecidableEq` on the seed's free 2-cell expressions.
  * `adjunctionDecidableInterchangeFreeConv` — and the seed's interchange-free 2-cell convertibility is a literal
    `Decidable`: the convergence-floor decision the keystone's POSITIVE half consumes (its sound embedding into
    the full `TwoCellConv` is `normalFormEq_imp_twoCellConv`).

The three `rfl`-checked smoke theorems witness that the WHOLE pipeline COMPUTES by definitional reduction on the
seed — `decEq` reduces, and the `Acc.rec` interchange-free normalizer reduces (`unit ⊟ id` normalizes to `unit`
and is decided interchange-free convertible to it).  Nothing here flips a keystone flag: the remaining brick is
the modulo-interchange (Godement) quotient of the resulting normal forms (the NEGATIVE half of the FULL
`TwoCellConv` decision, the genuine confluence-modulo-interchange hurdle) — an honest next step, not discharged.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the subsingleton decisions are full constructor enumeration; the smoke theorems are `rfl` on the computing
decision procedures).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## Decidable equality of the adjunction-seed generators -/

/-- Decidable equality of the adjunction-seed modes. -/
def adjunctionModeDecEq : DecidableEq AdjunctionMode
  | .base, .base => isTrue rfl
  | .tip, .tip => isTrue rfl
  | .base, .tip => isFalse (fun modesEqual => AdjunctionMode.noConfusion modesEqual)
  | .tip, .base => isFalse (fun modesEqual => AdjunctionMode.noConfusion modesEqual)

/-- The adjunction-seed modality homs are subsingletons: at each parallel boundary there is at most one
generator (`left : base ⟶ tip`, `right : tip ⟶ base`), so any two are equal — full constructor enumeration,
the impossible cross-boundary cases discharged by the index mismatch. -/
def adjunctionModalityDecEq (sourceMode targetMode : AdjunctionMode) :
    DecidableEq (AdjunctionModality sourceMode targetMode)
  | .left, .left => isTrue rfl
  | .right, .right => isTrue rfl

/-- The adjunction-seed 2-cell generators are subsingletons at each boundary (`unit`, `counit` sit at distinct
parallel boundaries), so any two parallel ones are equal. -/
def adjunctionTwoCellDecEq {sourceMode targetMode : AdjunctionMode}
    (sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode) :
    DecidableEq (AdjunctionTwoCell sourcePath targetPath)
  | .unit, .unit => isTrue rfl
  | .counit, .counit => isTrue rfl

/-! ## Decidable free-2-cell equality + interchange-free convertibility at the seed -/

/-- ★ **Decidable equality of free 2-cell expressions over the walking-adjunction seed.** -/
def adjunctionRawTwoCellDecidableEq {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} :
    DecidableEq (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  RawTwoCellExpr.decidableEq adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq

/-- ★ **Interchange-free 2-cell convertibility over the walking-adjunction seed is decidable** — the
convergence-floor decision the fib-3 keystone's positive half consumes. -/
def adjunctionDecidableInterchangeFreeConv
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (Core.EquationalTheory
      (fun leftCell rightCell => TwoCellStepInterchangeFree adjunctionModeSignature leftCell rightCell)
      cellFirst cellSecond) :=
  decidableInterchangeFreeConv adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq
    cellFirst cellSecond

/-! ## Smoke: the whole decision pipeline computes by definitional reduction -/

/-- Syntactic decEq computes: the composite `unit ⊟ id` is NOT syntactically equal to the bare `unit`. -/
theorem adjunctionUnitThenId_ne_unit_decidably :
    (adjunctionRawTwoCellDecidableEq adjunctionUnitThenId adjunctionUnitTwoCell).decide = false := rfl

/-- Syntactic decEq computes: the unit equals itself. -/
theorem adjunctionUnit_eq_unit_decidably :
    (adjunctionRawTwoCellDecidableEq adjunctionUnitTwoCell adjunctionUnitTwoCell).decide = true := rfl

/-- ★ The interchange-free convertibility decision computes (the `Acc.rec` normalizer reduces): `unit ⊟ id` is
decided interchange-free CONVERTIBLE to `unit` (the `vcompIdRight` structural law). -/
theorem adjunctionUnitThenId_interchangeFreeConv_unit_decidably :
    (adjunctionDecidableInterchangeFreeConv adjunctionUnitThenId adjunctionUnitTwoCell).decide = true := rfl

end FX1Poly.Tier0
