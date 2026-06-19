import FX1Poly.Tier0.Term.Core.RawSize

/-! # FX1Poly/Core/.../IotaSN/SizeCompatClosureSN
    — the generic strong-normalization-by-size combinator: ANY reduction relation on `RawTerm` whose
    every step strictly decreases the structural `RawTerm.size` is well-founded (Tait-free, RPO-free)

`RawIotaFullStepSN` ships SN for the full oriented-iota reduction via the RECURSIVE PATH ORDER over
`eraseToRose` — the right measure for the rows the RPO can orient (eliminators outrank `gen_app`).  But a
TABLE-NATIVE oriented row whose two heads sit at EQUAL RPO rank cannot be oriented by that precedence:
`iotaGenRank` puts every non-eliminator generator at rank 0, so a type-former-to-type-former rewrite (the
definitional-univalence row `Id_U A B`-reduces-to-`Equiv A B`, both type codes at rank 0) gets no decrease
from the RPO.  The shipped `stepOverOrientedTable_wellFounded` therefore excludes the table-native rows by
design, leaving their SN argued-but-not-instantiated.

This file ships the SIZE-measure SIBLING of the RPO route as a single reusable combinator:
`wellFounded_of_sizeStrictlyDecreasing`.  When a relation strictly decreases `RawTerm.size` — which a
type-former-to-type-former rewrite that DROPS a child does (the univalence row drops the `universeCode`
child, `Id_U A B` -> `Equiv A B`) — it is strongly normalizing by `size`, with no RPO, no Tait, no beta-SN
import.  The combinator is relation-agnostic: it takes the per-step size-decrease proof as a hypothesis
(a higher-order theorem parameter — fine, unlike an inductive parameter), so a bespoke congruence closure
(`DefinitionalUnivalenceRowSN`) supplies the closure-wide size-decrease and reads SN off this combinator.

## Honest scope

Size-strict-decrease is a STRONG hypothesis: it captures relations that DROP or SHRINK terms (the
definitional-univalence row, the gel-boundary projections), but NOT relations that can GROW the term —
beta's argument duplication and the Church-encoded iota successor cases build nested `gen_app`, so they do
not decrease `size`; their SN genuinely needs the RPO / Tait machinery.  This is therefore the EASY half: a
real, reusable SN combinator for the orientation-trivial fragment the RPO leaves uncovered, NOT a joint SN
with beta/iota/eta (which needs a Geser-style commuting-union of the `size` and RPO measures).

## Zero-axiom verification

`Subrelation.wf` + `InvImage.wf RawTerm.size` over `Nat.lt_wfRel.wf` (the idiom of
`etaRootTableSuccessor_wellFounded`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-- **★ The generic strong-normalization-by-size combinator.**  Any reduction relation `stepRelation` on
`RawTerm` whose every step strictly decreases `RawTerm.size` is well-founded (as the flipped
"successor" relation `fun laterTerm earlierTerm => stepRelation earlierTerm laterTerm`), by
`Subrelation.wf` + `InvImage.wf RawTerm.size` over `Nat.lt_wfRel.wf`.  RPO-free, Tait-free, beta-free —
the size-measure sibling of `iotaFullStep_wellFounded`.  The size-decrease is the hypothesis, so any
bespoke closure that proves it inherits SN through this one combinator. -/
theorem wellFounded_of_sizeStrictlyDecreasing
    {stepRelation : {scope : Nat} → RawTerm scope → RawTerm scope → Prop}
    (decreasesSize : ∀ {scope : Nat} {source target : RawTerm scope},
      stepRelation source target → target.size < source.size)
    {scope : Nat} :
    WellFounded (fun (laterTerm earlierTerm : RawTerm scope) =>
      stepRelation earlierTerm laterTerm) :=
  Subrelation.wf
    (r := InvImage Nat.lt RawTerm.size)
    (fun step => decreasesSize step)
    (InvImage.wf RawTerm.size Nat.lt_wfRel.wf)

end FX1Poly.Core
