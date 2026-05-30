import FX1Poly.Typed.HasType
import FX1Poly.Core.RawTermRename
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeWeakening — typed renaming + weakening (TY-SR support)

The first typed metatheory lemma: `HasType` is preserved under renaming
(and its weakening special case).  This is the structural half of the
fibration property (SR) and the engine behind the typed substitution lemma
(#457) and IsType-stability (#468).  No `Conv.trans` needed — weakening is
structural — so it is UNBLOCKED, unlike the deferred probes.

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

/-! ## The general renaming lemma

`HasType` is preserved along ANY renaming that respects the context — a
renaming `rawRenaming` together with the side condition that it sends each
source binding's looked-up type to the corresponding target binding's
looked-up type (commuting with `rename`).  Weakening is the special case
where the target context is the source extended by one binding.

The `targetContext` / `rawRenaming` / context-condition are quantified
INSIDE the conclusion (after the `:`), so `induction typed` carries them in
the motive and re-introduces them per case — the source context is an index
of `typed`, so it generalizes correctly through the induction.  The core has
no binder-introducing arm yet, so the context-condition never needs lifting;
that is exactly why renaming is tractable at this stage.

Critically `Conv.trans`-free: the `conv` case forwards `Conv.rename` (#370)
without ever composing conversions.  So typed weakening is UNBLOCKED, unlike
the uniqueness / no-Type-in-Type probes that wait on raw confluence. -/
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
  | var index =>
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
  | universeFormation levelExpr flag =>
      intro targetScope targetContext rawRenaming contextCondition
      rw [rename_universeCodeCell, rename_universeCodeCell]
      exact HasType.universeFormation targetContext levelExpr flag

/-- Typed weakening: `HasType` survives extending the context by one fresh
binding, with both subject and classifier shifted by `RawRenaming.weaken`.
The corollary of `renameRespectingContext` whose context-condition is the
`lookup_cons_succ` unfolder (#467) — and that condition holds DEFINITIONALLY
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
