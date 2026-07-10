import FX1Poly.Polygraph.TwoCategory.Table.PresentationOpDuality
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeGen
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedNormalizer
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZOrderCompleteness

/-! # Polygraph/TwoCategory/Table/WalkerDualityInstances — the three decided DUAL walkers (#2024, WALKER-DUALITY B3)

The `op` decision transport (`Table/PresentationOpDuality.lean`, `decideSaturatedConvUnderOp`) is walker-agnostic:
a shipped decider for a base saturated conv decides its `op`-dual through the duality iff.  This file INSTANTIATES
it at the three shipped decided walkers, DOUBLING the decided-walker census with no new normalizer:

  * **the walking COMONAD** = `op` of the walking monad — `decideSaturatedConvOverComonadNative` is
    `decideSaturatedConvUnderOp decideSaturatedConvOverMonadNative`; the counit / comult co-laws are `opCellRel`
    of the monad's unit / mult laws.  BOTH verdicts exercised on real dual words: the co-associativity dual pair
    `isTrue`, the separating co-faces dual pair `isFalse`.
  * **the idempotent COMONAD** = `op` of the idempotent monad — `decideSaturatedConvUnderOp
    decideSaturatedConvOverIdempotentNative`; the idempotent decider is locally posetal (`isTrue` everywhere), so
    the dual is `isTrue` of the transported posetality, exercised on a real dual word.
  * **co-KZ** = the DIRECTED KZ order REVERSED.  Honest caveat: KZ's `KZTwoCellLE` is a directed preorder (no
    `symm`), NOT the symmetric `SaturatedConvOver` carrier the `op` involution acts on, so co-KZ is `op` of a
    PREORDER — a pure argument-swap `coKZTwoCellLE a b := KZTwoCellLE b a`, decided by `decideKZLETotal b a`.  Both
    verdicts: the reversed generator `isTrue`, the forward (strict) direction `isFalse`.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Table

open FX1Poly.Polygraph
open FX1Poly.Polygraph.Amalgam

/-! ## The walking comonad = `op` of the walking monad -/

/-- The walking-comonad signature — `op` of the walking monad's: one object, one endo-1-cell `t`, the unit / mult
2-generators READ BACKWARDS as counit (`t => id`) / comult (`t => t.t`). -/
def comonadModeSignature : ModeSignature := opSignature monadModeSignature

/-- The walking-comonad co-laws — `opCellRel` of the monad's three laws (left counit, right counit,
coassociativity), each a 2-cell reversal of a monad law. -/
def ComonadLawRel : CellRel comonadModeSignature := opCellRel MonadLawRel

/-- ★ **The walking-comonad saturated decider** — the `op` of the shipped born-generic monad decider, through the
duality iff.  No new normalizer: `decideSaturatedConvUnderOp decideSaturatedConvOverMonadNative` decides the
comonad word problem by deciding the monad word problem on the `op`'d cells.  The census-doubling move. -/
def decideSaturatedConvOverComonadNative :
    DecidableSaturatedConvForRel comonadModeSignature ComonadLawRel :=
  decideSaturatedConvUnderOp decideSaturatedConvOverMonadNative

/-- The comonad decider decides the size-3 co-associativity dual pair (the `op` of the monad's associativity
witnesses) to `true`. -/
def comonadDecidesTrue_coassoc : Bool :=
  match decideSaturatedConvOverComonadNative (opCell monadAssocLeftCell) (opCell monadAssocRightCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- The comonad decider returns `true` on the co-associativity dual pair (by `rfl`). -/
theorem comonadDecidesTrue_coassoc_holds : comonadDecidesTrue_coassoc = true := rfl

/-- The comonad decider decides the separating co-faces dual pair (the `op` of the monad's separating unit faces)
to `false` — the genuine `isFalse` separation transported through `op`. -/
def comonadDecidesFalse_faces : Bool :=
  match decideSaturatedConvOverComonadNative
      (opCell (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell))
      (opCell (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell)) with
  | isTrue _ => true
  | isFalse _ => false

/-- The comonad decider returns `false` on the separating co-faces dual pair (by `rfl`). -/
theorem comonadDecidesFalse_faces_holds : comonadDecidesFalse_faces = false := rfl

/-! ## The idempotent comonad = `op` of the idempotent monad -/

/-- The idempotent-comonad signature — `op` of the idempotent monad's (same generators as the monad). -/
def idempotentComonadModeSignature : ModeSignature := opSignature monadModeSignature

/-- The idempotent-comonad co-laws — `opCellRel` of the idempotent monad's laws. -/
def IdempotentComonadLawRel : CellRel idempotentComonadModeSignature := opCellRel IdempotentLawRel

/-- ★ **The idempotent-comonad saturated decider** — the `op` of the shipped idempotent decider, through the
duality iff.  The idempotent decider is locally posetal (`isTrue` everywhere), so the dual is `isTrue` of the
transported posetality. -/
def decideSaturatedConvOverIdempotentComonadNative :
    DecidableSaturatedConvForRel idempotentComonadModeSignature IdempotentComonadLawRel :=
  decideSaturatedConvUnderOp decideSaturatedConvOverIdempotentNative

/-- The idempotent-comonad decider decides a real dual pair to `true` (locally posetal, transported). -/
def idempotentComonadDecidesTrue_coassoc : Bool :=
  match decideSaturatedConvOverIdempotentComonadNative
      (opCell monadAssocLeftCell) (opCell monadAssocRightCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- The idempotent-comonad decider returns `true` on the dual pair (by `rfl`). -/
theorem idempotentComonadDecidesTrue_coassoc_holds : idempotentComonadDecidesTrue_coassoc = true := rfl

/-! ## co-KZ = the DIRECTED KZ order REVERSED

Honest framing: `KZTwoCellLE` is a DIRECTED preorder (lax-idempotency, no `symm`), NOT the symmetric
`SaturatedConvOver` carrier the `op` involution acts on.  So co-KZ is the `op` of a PREORDER — order reversal, a
pure argument swap — not the symmetric-carrier dual.  This matches the directed caveat of
`fxTab_hasKZWalkerMigration = false`. -/

/-- The co-KZ 2-cell order — the DIRECTED KZ order reversed (`a <=(coKZ) b` means `b <=(KZ) a`). -/
def coKZTwoCellLE {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) : Prop :=
  KZTwoCellLE cellB cellA

/-- ★ **The co-KZ order decider** — the `op` (reversal) of the shipped total KZ order decider: decide
`coKZTwoCellLE a b` by deciding `KZTwoCellLE b a`.  A pure argument swap; decidability transports trivially. -/
def decideCoKZLETotal {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    Decidable (coKZTwoCellLE cellA cellB) :=
  decideKZLETotal cellB cellA

/-- The co-KZ decider decides the reversed KZ generator `eta.t <=(coKZ) t.eta` (i.e. `t.eta <=(KZ) eta.t`, the
shipped `kzGen`) to `true`. -/
def coKZDecidesTrue_reversed : Bool :=
  match decideCoKZLETotal kzEtaTCell kzTEtaCell with
  | isTrue _ => true
  | isFalse _ => false

/-- The co-KZ decider returns `true` on the reversed generator (by `rfl`). -/
theorem coKZDecidesTrue_reversed_holds : coKZDecidesTrue_reversed = true := rfl

/-- The co-KZ decider decides the FORWARD (strict) direction `t.eta <=(coKZ) eta.t` (i.e. `eta.t <=(KZ) t.eta`) to
`false` — the strictness of the directed order, witnessing co-KZ is a genuine order reversal. -/
def coKZDecidesFalse_forward : Bool :=
  match decideCoKZLETotal kzTEtaCell kzEtaTCell with
  | isTrue _ => true
  | isFalse _ => false

/-- The co-KZ decider returns `false` on the forward direction (by `rfl`). -/
theorem coKZDecidesFalse_forward_holds : coKZDecidesFalse_forward = false := rfl

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the THREE decided DUAL walkers SHIP (WALKER-DUALITY B3), doubling the decided-walker
census.**  The walking COMONAD (`decideSaturatedConvOverComonadNative`, BOTH verdicts: co-associativity `isTrue`,
separating co-faces `isFalse`) and the idempotent COMONAD (`decideSaturatedConvOverIdempotentComonadNative`,
`isTrue` — the underlying idempotent decider is locally posetal) are each the `op` of their shipped dual through
the walker-agnostic `decideSaturatedConvUnderOp`, no new normalizer.  co-KZ (`decideCoKZLETotal`, BOTH verdicts:
reversed generator `isTrue`, forward strict direction `isFalse`) is the DIRECTED KZ order REVERSED — honestly the
`op` of a preorder (argument swap), NOT the symmetric-carrier involution.  All zero-axiom, decided by `rfl`.
`= true`. -/
def fxTab_hasWalkerDualityInstances : Bool := true

end FX1Poly.Polygraph.Table
