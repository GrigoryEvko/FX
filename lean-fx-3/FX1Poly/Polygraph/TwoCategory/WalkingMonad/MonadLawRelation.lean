import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedOver

/-! # WalkingMonad/MonadLawRelation — the three monad laws as a bespoke-free `CellRel` home + the generic carrier
(POLY-TAB r6 monad re-founding, PORT-IN leaf; mirrors `WalkingIdempotent/IdempotentLawRelation`)

The base law relation `MonadLawRel` for the generic `SaturatedConvOver monadModeSignature MonadLawRel` carrier
already ships as data in `Amalgam/SaturatedOver` (the INT-SIG-ALIGN #2079 exemplar: `MonadLawRel` + the two-way
iso `monadSaturated_iff_generic`).  Its constant-closure references only the CONV-FREE law composites
(`monadLeftUnitCell` / `monadRightUnitCell` / `monadAssocLeftCell` / `monadAssocRightCell` / `monadIdTCell`), NOT the
bespoke inductive `MonadSaturatedTwoCellConv` — so the generic carrier's law layer is already bespoke-free at the
constant level even though `SaturatedOver` imports the bespoke file transitively.

This leaf gives the monad re-founding lane a NAMED bespoke-free home for the carrier and its law rows, matching the
idempotent template (`IdempotentLawRelation.lean` provided `IdempotentLawRel` + `idempotenceRowConv`).  The native
soundness / completeness / decision files consume the carrier and the law rows from here; every declaration below has
a constant-closure that contains NO `MonadSaturatedTwoCellConv` (each is `ofRelation` of a `MonadLawRel` row, or an
abbreviation, over the conv-free law composites).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The generic saturated carrier of the walking monad -/

/-- ★ **The walking monad's GENERIC saturated 2-cell convertibility** — `SaturatedConvOver monadModeSignature
MonadLawRel`, the generic per-presentation saturated congruence (`Amalgam/SaturatedOver`) at the walking monad's
three-law relation `MonadLawRel`.  This is the born-generic carrier the monad re-founding lane decides over; it is
LOGICALLY IDENTICAL to the bespoke `MonadSaturatedTwoCellConv` (`monadSaturated_iff_generic`) but its constructors are
the generic ctors, so a term built from them has no `MonadSaturatedTwoCellConv` in its provenance. -/
abbrev MonadSaturatedConvGen {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath) : Prop :=
  SaturatedConvOver monadModeSignature MonadLawRel cellAlpha cellBeta

/-! ## The three monad laws as generic saturated conv rows -/

/-- The LEFT-unit monad law `mu . (eta |> t) ~ id_t` as a generic saturated conv row. -/
theorem monadLeftUnitRowGen :
    SaturatedConvOver monadModeSignature MonadLawRel monadLeftUnitCell monadIdTCell :=
  SaturatedConvOver.ofRelation MonadLawRel.leftUnit

/-- The RIGHT-unit monad law `mu . (t <| eta) ~ id_t` as a generic saturated conv row. -/
theorem monadRightUnitRowGen :
    SaturatedConvOver monadModeSignature MonadLawRel monadRightUnitCell monadIdTCell :=
  SaturatedConvOver.ofRelation MonadLawRel.rightUnit

/-- The ASSOCIATIVITY monad law `mu . (mu |> t) ~ mu . (t <| mu)` as a generic saturated conv row. -/
theorem monadAssocRowGen :
    SaturatedConvOver monadModeSignature MonadLawRel monadAssocLeftCell monadAssocRightCell :=
  SaturatedConvOver.ofRelation MonadLawRel.assoc

/-! ## Non-vacuity -/

/-- A real law row fires directly — the associativity law `mu . (mu |> t) ~ mu . (t <| mu)` holds in the generic
saturated conv via `ofRelation MonadLawRel.assoc` (identifying two syntactically distinct `t.t.t ⇒ t` composites at
positive width), so the base relation is genuinely non-empty and the three monad laws do real work. -/
theorem monadAssocRowConv :
    SaturatedConvOver monadModeSignature MonadLawRel monadAssocLeftCell monadAssocRightCell :=
  SaturatedConvOver.ofRelation MonadLawRel.assoc

/-! ## Honesty marker -/

/-- **ESTABLISHED — the walking monad's generic law carrier has a bespoke-free NAMED home (POLY-TAB r6, S1).**  The
carrier abbreviation `MonadSaturatedConvGen` and the three monad-law rows (`monadLeftUnitRowGen` /
`monadRightUnitRowGen` / `monadAssocRowGen`, plus the non-vacuity witness `monadAssocRowConv`) are provided over the
already-shipped `MonadLawRel` (`Amalgam/SaturatedOver`), each a generic `ofRelation` term whose constant-closure
contains NO `MonadSaturatedTwoCellConv`.  Mirrors the idempotent `IdempotentLawRelation` port-in leaf.  `= true`. -/
def fxMonad_hasLawRelationLeaf : Bool := true

end FX1Poly.Polygraph.Amalgam
