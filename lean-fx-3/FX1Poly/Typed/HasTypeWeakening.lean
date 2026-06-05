import FX1Poly.Typed.HasType
import FX1Poly.Core.RawTermRename
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeWeakening — typed renaming + weakening

`HasType` is preserved under renaming (and its weakening special case).
This is the structural half of the fibration property (SR) and the engine
behind the typed substitution lemma and IsType-stability.  No `Conv.trans`
needed — weakening is structural.

This file starts with the two `rename` computations the typing arms need:
how a renaming acts on a variable cell and a universe-code cell.
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

/-! ## The general renaming lemma

`HasType` is preserved along ANY renaming that respects the context — a
renaming `rawRenaming` together with the side condition that it sends each
source binding's looked-up type to the corresponding target binding's
looked-up type (commuting with `rename`).  Weakening is the special case
where the target context is the source extended by one binding.

The `targetContext` / `rawRenaming` / context-condition are quantified
INSIDE the conclusion (after the `:`), so `induction typed` carries them in
the motive and re-introduces them per case — the source context is an index
of `typed`, so it generalizes correctly through the induction.  The
binder-introducing arms (`piFormation` / `sigmaFormation`) lift the
context-condition across the fresh binder; the leaf arms pass it verbatim.

Critically `Conv.trans`-free: the `conv` case forwards `Conv.rename` (#370)
without ever composing conversions — so typed weakening does not depend on raw
confluence. -/
theorem HasType.renameRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (typed : HasType profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasType profile targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) := by
  induction typed with
  | var sourceContext index =>
      intro targetScope targetContext rawRenaming contextCondition
      rw [rename_variableCell, contextCondition index]
      exact HasType.var targetContext (rawRenaming index)
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise ihReclassifier =>
      intro targetScope targetContext rawRenaming contextCondition
      have premiseTyped :=
        ihTypedPremise targetContext rawRenaming contextCondition
      have reclassifierTypedRenamed :=
        ihReclassifier targetContext rawRenaming contextCondition
      rw [rename_universeCodeCell] at reclassifierTypedRenamed
      exact HasType.conv levelExpr flag premiseTyped
        (Conv.rename rawRenaming converts) reclassifierTypedRenamed
  | universeFormation sourceContext levelExpr flag =>
      intro targetScope targetContext rawRenaming contextCondition
      rw [rename_universeCodeCell, rename_universeCodeCell]
      exact HasType.universeFormation targetContext levelExpr flag
  | piFormation sourceContext domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      intro targetScope targetContext rawRenaming contextCondition
      rw [rename_piTyCodeCell, rename_universeCodeCell]
      refine HasType.piFormation targetContext _ _ domainLevel codomainLevel flag ?_ ?_
      · -- domain code is renamed by `rawRenaming` itself; its IH discharges it
        have domainRenamed :=
          ihDomain targetContext rawRenaming contextCondition
        rw [rename_universeCodeCell] at domainRenamed
        exact domainRenamed
      · -- codomain code lives under one fresh binder, so its IH fires with the
        -- LIFTED renaming into the extended target context; the lifted context
        -- condition reduces to `rename_lift_weaken_commute` on each looked-up type
        have codomainRenamed :=
          ihCodomain (targetContext.cons (RawTerm.rename rawRenaming domainCode))
            (RawRenaming.lift rawRenaming) ?liftedCondition
        · rw [rename_universeCodeCell] at codomainRenamed
          exact codomainRenamed
        case liftedCondition =>
          intro index
          obtain ⟨indexValue, indexBound⟩ := index
          cases indexValue with
          | zero =>
              show RawTerm.rename (RawRenaming.lift rawRenaming)
                  (RawTerm.rename RawRenaming.weaken domainCode)
                = RawTerm.rename RawRenaming.weaken
                    (RawTerm.rename rawRenaming domainCode)
              exact rename_lift_weaken_commute rawRenaming domainCode
          | succ k =>
              show RawTerm.rename (RawRenaming.lift rawRenaming)
                  (RawTerm.rename RawRenaming.weaken
                    (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
                = RawTerm.rename RawRenaming.weaken
                    (targetContext.lookup
                      (rawRenaming ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
              rw [rename_lift_weaken_commute,
                contextCondition ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩]
  | sigmaFormation sourceContext domainCode codomainCode domainLevel codomainLevel
      flag domainTyped codomainTyped ihDomain ihCodomain =>
      -- exact mirror of the `piFormation` case: the cell rename distributes the
      -- same way (`rename_sigmaTyCodeCell`), the domain IH fires with the bare
      -- renaming, and the codomain IH fires with the LIFTED renaming under the
      -- extended target context (the same lifted context-condition via
      -- `rename_lift_weaken_commute`)
      intro targetScope targetContext rawRenaming contextCondition
      rw [rename_sigmaTyCodeCell, rename_universeCodeCell]
      refine HasType.sigmaFormation targetContext _ _ domainLevel codomainLevel flag ?_ ?_
      · have domainRenamed :=
          ihDomain targetContext rawRenaming contextCondition
        rw [rename_universeCodeCell] at domainRenamed
        exact domainRenamed
      · have codomainRenamed :=
          ihCodomain (targetContext.cons (RawTerm.rename rawRenaming domainCode))
            (RawRenaming.lift rawRenaming) ?liftedCondition
        · rw [rename_universeCodeCell] at codomainRenamed
          exact codomainRenamed
        case liftedCondition =>
          intro index
          obtain ⟨indexValue, indexBound⟩ := index
          cases indexValue with
          | zero =>
              show RawTerm.rename (RawRenaming.lift rawRenaming)
                  (RawTerm.rename RawRenaming.weaken domainCode)
                = RawTerm.rename RawRenaming.weaken
                    (RawTerm.rename rawRenaming domainCode)
              exact rename_lift_weaken_commute rawRenaming domainCode
          | succ k =>
              show RawTerm.rename (RawRenaming.lift rawRenaming)
                  (RawTerm.rename RawRenaming.weaken
                    (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
                = RawTerm.rename RawRenaming.weaken
                    (targetContext.lookup
                      (rawRenaming ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
              rw [rename_lift_weaken_commute,
                contextCondition ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩]

/-- Typed weakening: `HasType` survives extending the context by one fresh
binding, with both subject and classifier shifted by `RawRenaming.weaken`.
The corollary of `renameRespectingContext` whose context-condition is the
`lookup_cons_succ` unfolder — and that condition holds DEFINITIONALLY
(`fun _ => rfl`): `weaken index` unfolds to `Fin.succ index`, the `cons`
telescope's `lookup` fires its successor arm, and the `Fin` proof collapses
by proof-irrelevance, leaving exactly `rename weaken (context.lookup index)`.

This is the structural cartesian-lift skeleton of the fibration: a typing
derivation in `context` lifts to one in `context.cons newBinding`. -/
theorem HasType.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} (newBinding : RawTerm scope)
    (typed : HasType profile context subject classifier) :
    HasType profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  typed.renameRespectingContext (context.cons newBinding) RawRenaming.weaken
    (fun _ => rfl)

end FX1Poly.Typed
