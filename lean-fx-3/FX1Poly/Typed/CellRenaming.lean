import FX1Poly.Typed.CellConstructors
import FX1Poly.Core.RawTermRename
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/CellRenaming — how `RawTerm.rename` acts on the typing cells

The pure-`RawTerm` renaming substrate: the per-cell computation rules for how a
renaming acts on the kernel's typing cells (`variableCell`, `universeCodeCell`,
`emptyTypeCell`, `piTyCodeCell`, `sigmaTyCodeCell`) plus the binder-crossing
`rename_lift_weaken_commute` naturality square.  These lemmas mention NO typing
judgement — they are statements about `RawTerm.rename` over the cell
constructors, consumed by every renaming/weakening arm in the typed metatheory
(formation engine, grown engine, the BFT/denote reducibility substrate).

They were extracted here from the old `HasTypeWeakening` so the substrate stands
on the cell constructors alone, independent of any typing engine — the engine
files import THIS, never the other way around.

## Zero-axiom verification

The leaf-cell computations reduce by `rfl` (the canonical fold is definitionally
transparent on the literal child spine); `rename_lift_weaken_commute` is two
`rename_compose` rewrites + a pointwise `Fin`-eta agreement.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Renaming a variable cell applies the renaming to the de Bruijn index. -/
theorem rename_variableCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (index : Fin sourceScope) :
    RawTerm.rename rawRenaming (variableCell index)
      = variableCell (rawRenaming index) :=
  rfl

/-- Renaming a universe-code cell leaves it unchanged — universe codes are
closed (their payload does not depend on scope). -/
theorem rename_universeCodeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.rename rawRenaming (universeCodeCell levelExpr flag)
      = universeCodeCell levelExpr flag :=
  rfl

/-- Renaming the empty-type code cell leaves it unchanged — `emptyTypeCell` is a
closed nullary leaf (no payload data, no children).  Holds by `rfl` for the same
reason as `rename_universeCodeCell`: `RawTerm.rename` is `fold GenAlgebra.canonical`,
which over the literal `childNil` rebuilds the same cell.  The substrate of
CON-A2 route E's `emptyFormation` weakening arm. -/
theorem rename_emptyTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (emptyTypeCell (scope := sourceScope))
      = emptyTypeCell :=
  rfl

/-- Renaming a Π-type code cell distributes over the two children: the domain
(child shift `0`) is renamed by the renaming itself, the codomain (child shift
`1`, living under one fresh binder) by the renaming lifted once
(`iterateLiftRaw rawRenaming 1` — exactly the lift `foldChildren` applies to a
shift-`1` child, line 224 of `Fold.lean`).  Holds by `rfl`: `RawTerm.rename` is
`fold GenAlgebra.canonical`, which iotas over the literal `childCons … childNil`
spine, and the `Unit` payload's `payload_scope_invariant_of_not_var` cast reduces
to `rfl` exactly as in the nullary `rename_universeCodeCell`.

Spelled with `iterateLiftRaw _ 1` (not `LiftsRaw.liftForRaw _`, the defeq single
lift) to match the substrate's `RawTermSubst0Commute` convention, so the typed
Π-weakening case chains directly with the `*_iterateLiftRaw_*` commutation
lemmas. -/
theorem rename_piTyCodeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.rename rawRenaming (piTyCodeCell domainCode codomainCode)
      = piTyCodeCell (RawTerm.rename rawRenaming domainCode)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) codomainCode) :=
  rfl

/-- Renaming distributes over a `sigmaTyCodeCell` exactly as over a
`piTyCodeCell` (the two cells differ only in the head generator, which the
canonical fold treats uniformly): the domain (child shift `0`) by the renaming
itself, the codomain (child shift `1`, under one fresh binder) by the renaming
lifted once.  Holds by `rfl` — the dual of `rename_piTyCodeCell`, the
binder-crossing brick the Σ-formation case of `renameRespectingContext`
consumes. -/
theorem rename_sigmaTyCodeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.rename rawRenaming (sigmaTyCodeCell domainCode codomainCode)
      = sigmaTyCodeCell (RawTerm.rename rawRenaming domainCode)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) codomainCode) :=
  rfl

/-- Lifting a renaming commutes with weakening: renaming under one fresh binder
(`RawRenaming.lift`) after weakening equals weakening after the un-lifted
renaming.  The naturality square `lift ρ ∘ weaken = weaken ∘ ρ` at the term
level.

This is the binder-crossing crux the `piFormation` case of
`renameRespectingContext` needs: its codomain premise is checked under
`Γ.cons domain`, so the IH fires with the LIFTED renaming, and discharging the
lifted context-condition reduces (at both the de Bruijn-0 and successor index)
to exactly this commutation on the looked-up binding types.  It is the only
place `renameRespectingContext` lifts its renaming (the binder-introducing arms
do; the leaf arms do not).

Proof: `RawTerm.rename_compose` (twice) reduces both sides to a single composed
renaming, and the two composites agree pointwise (`lift ρ ∘ weaken` and
`weaken ∘ ρ` both send `pos ↦ Fin.succ (ρ pos)`, `rfl` by Fin-eta +
proof-irrelevance), discharged by `RawTerm.rename_pointwise`. -/
theorem rename_lift_weaken_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename (RawRenaming.lift rawRenaming)
        (RawTerm.rename RawRenaming.weaken sourceTerm)
      = RawTerm.rename RawRenaming.weaken
          (RawTerm.rename rawRenaming sourceTerm) := by
  rw [RawTerm.rename_compose, RawTerm.rename_compose]
  exact RawTerm.rename_pointwise (fun _position => rfl) sourceTerm

end FX1Poly.Typed
