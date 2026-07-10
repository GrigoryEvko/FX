import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedOver
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSeed

/-! # WalkingIdempotent/IdempotentLawRelation — the four idempotent-monad laws as a bespoke-free `CellRel`
(POLY-TAB r5 retirement, PORT-IN leaf)

The base law relation `IdempotentLawRel` for the generic `SaturatedConvOver monadModeSignature IdempotentLawRel`
carrier, relocated OUT of the retiring `Amalgam/SaturatedComponentDecider.lean` (which rode the bespoke
`IdempotentMonadSaturatedTwoCellConv` inductive) into this bespoke-free leaf.  It imports only the generic saturated
substrate (`Amalgam/SaturatedOver`) and the conv-free idempotence faces (`WalkingIdempotent/IdempotentMonadSeed`) —
NO bespoke walking-idempotent-monad convertibility.  The native r4 lane
(`IdempotentSaturated{MuInvertible,Ladder,GeneralBricks,RightWhisker,Normalizer}`) consumes `IdempotentLawRel` from
here; the relation's home is now bespoke-free, unblocking the retirement of the whole old idempotent chain.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The four walking-idempotent-monad laws as a `CellRel` -/

/-- The **walking idempotent monad's four laws as a `CellRel`** — the three monad laws (left unit, right unit,
associativity) plus the idempotence law `eta |> t ~ t <| eta`.  The base relation for which
`SaturatedConvOver monadModeSignature IdempotentLawRel` is the walking idempotent monad's saturated conv. -/
inductive IdempotentLawRel :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → Prop where
  /-- The left-unit law `mu . (eta |> t) ~ id_t`. -/
  | leftUnit : IdempotentLawRel monadLeftUnitCell monadIdTCell
  /-- The right-unit law `mu . (t <| eta) ~ id_t`. -/
  | rightUnit : IdempotentLawRel monadRightUnitCell monadIdTCell
  /-- The associativity law `mu . (mu |> t) ~ mu . (t <| mu)`. -/
  | assoc : IdempotentLawRel monadAssocLeftCell monadAssocRightCell
  /-- The idempotence law `eta |> t ~ t <| eta` (well-pointedness). -/
  | idempotence : IdempotentLawRel monadEtaTCell monadTEtaCell

/-! ## Non-vacuity -/

/-- A real law row fires directly — the idempotence law `eta |> t ~ t <| eta` holds in the generic saturated conv
via `ofRelation IdempotentLawRel.idempotence` (NOT derivable from the free structure or the monad laws alone), so
the base relation is genuinely non-empty and idempotence does real work. -/
theorem idempotenceRowConv :
    SaturatedConvOver monadModeSignature IdempotentLawRel monadEtaTCell monadTEtaCell :=
  SaturatedConvOver.ofRelation IdempotentLawRel.idempotence

end FX1Poly.Polygraph.Amalgam
