import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Typed.Metatheory.SubjectReduction.StepPreservesDimensionalSubjectUsability
import FX1Poly.Core.Rewriting.Conversion.ConvRenameReflection

/-! # FX1Poly/Typed/Metatheory/Validity/WfContextUnionNoConsInterval
    — #1805: the interval is genuinely NON-FIBRANT (pinned into context well-formedness)

`WfContextUnion`'s `.cons` arm now forbids the interval (`¬ Conv bindingType intervalTypeCell`,
`HasTypeUnionValidity`), the exact DUAL of its `.lockCons` arm (`dimensionType = intervalTypeCell`).  An ordinary
fibrant binder may not bind the dimension; the dimension enters the context only under the affine `lockCons`
LOCK.  This file harvests that discipline:

  * `not_conv_weaken_intervalTypeCell` — the rename-stable lifter: `¬ Conv X interval ⟹ ¬ Conv (weaken X)
    interval` (the interval is renaming-fixed, so `Conv.reflectWeaken` strips the lookup's de Bruijn shift).
  * `WfContextUnion.noConsBindingIsInterval` — the DERIVATION: a `WfContextUnion` context satisfies
    `NoConsBindingIsInterval` (no `cons`-bound — dimensionally-INaccessible — position looks up to the interval).
    Structural recursion mirroring `lockedLookupIsInterval`: the `cons` leaf reads the new `¬ Conv` conjunct, the
    `lockCons`-0 leaf is dimensionally accessible (hypothesis impossible), deeper indices recurse and re-lift.
  * `HasTypeUnion.stepPreservesDimensionalSubjectUsability_ofWfContext` — the SR-residual closer re-pointed onto
    the threaded `WfContextUnion` presupposition: it OBTAINS `NoConsBindingIsInterval` from well-formedness
    internally, removing it as a free hypothesis.
  * `intervalConsNotWellFormed` — the headline non-fibrancy witness: `WfContextUnion (empty.cons intervalTypeCell)`
    is uninhabitable (its `¬ Conv intervalTypeCell intervalTypeCell` conjunct is refuted by `Conv.refl`).
  * `wfContextUnion_consUniverseInhabited` — non-vacuity: the strengthened `cons` arm is still inhabited (a
    universe-code binder is well-formed — a universe code is never the interval).

## Zero-axiom verification

`Conv.reflectWeaken` + `rename_intervalTypeCell` + the `lookup` / `isDimensionallyAccessibleAt` unfolders +
`Bool.noConfusion` + the existing head-distinctness `intervalTypeCell_not_conv_universeCodeCell`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- **The interval is renaming-fixed under conversion (weakening instance).**  If a term is not convertible to
the interval, neither is its single-binder weakening: `intervalTypeCell` is closed (`rename_intervalTypeCell`), so
`Conv.reflectWeaken` strips the `weaken` off both sides of a hypothetical `Conv (weaken X) interval`.  This is the
lifter the `NoConsBindingIsInterval` derivation needs to push the `¬ Conv` discipline through the de Bruijn shift
that `lookup` applies under each binder. -/
theorem not_conv_weaken_intervalTypeCell {scope : Nat} {term : RawTerm scope}
    (notInterval : ¬ Conv term intervalTypeCell) :
    ¬ Conv (RawTerm.rename RawRenaming.weaken term) (intervalTypeCell : RawTerm (scope + 1)) := by
  intro convWeaken
  apply notInterval
  apply Conv.reflectWeaken
  show Conv (RawTerm.rename RawRenaming.weaken term)
    (RawTerm.rename RawRenaming.weaken (intervalTypeCell : RawTerm scope))
  rw [rename_intervalTypeCell RawRenaming.weaken]
  exact convWeaken

/-- **★ Union well-formedness pins the interval-non-fibrancy discipline (#1805 derivation).**  Every `cons`-bound
(dimensionally-INaccessible) position of a `WfContextUnion` context looks up to a NON-interval — so an
interval-typed variable is necessarily a LOCKED dimension.  Structural recursion mirroring `lockedLookupIsInterval`
(its dimensional dual): the `cons`-0 leaf reads the well-formedness `¬ Conv` conjunct directly; the `lockCons`-0
leaf is dimensionally ACCESSIBLE, so the `= false` hypothesis is impossible (`Bool.noConfusion`); the deeper-binder
cases recurse on the prefix and re-lift the `¬ Conv` across the one weakening shift
(`not_conv_weaken_intervalTypeCell`).  This DISSOLVES `NoConsBindingIsInterval` as a free hypothesis: it now flows
from the threaded `WfContextUnion` presupposition. -/
theorem wfContextUnion_noConsBindingIsIntervalAt {profile : PolyProfile} :
    {scope : Nat} → (context : TypingContext profile scope) → WfContextUnion context →
      (index : Fin scope) → context.isDimensionallyAccessibleAt index = false →
        ¬ Conv (context.lookup index) intervalTypeCell
  | _, .empty, _wellFormed, index, _dimInaccessible =>
      absurd index.isLt (Nat.not_lt_zero index.val)
  | _, .cons _restContext bindingType, wellFormed, ⟨0, _⟩, _dimInaccessible => by
      rw [TypingContext.lookup_cons_zero]
      exact not_conv_weaken_intervalTypeCell wellFormed.2.2
  | _, .cons restContext _bindingType, wellFormed, ⟨position + 1, isLtSucc⟩, dimInaccessible => by
      rw [TypingContext.lookup_cons_succ]
      exact not_conv_weaken_intervalTypeCell
        (wfContextUnion_noConsBindingIsIntervalAt restContext wellFormed.1
          ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ dimInaccessible)
  | _, .lockCons _restContext _dimensionType, _wellFormed, ⟨0, _⟩, dimInaccessible =>
      Bool.noConfusion dimInaccessible
  | _, .lockCons restContext _dimensionType, wellFormed, ⟨position + 1, isLtSucc⟩, dimInaccessible => by
      rw [TypingContext.lookup_lockCons_succ]
      exact not_conv_weaken_intervalTypeCell
        (wfContextUnion_noConsBindingIsIntervalAt restContext wellFormed.1
          ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ dimInaccessible)

/-- **★ The `WfContextUnion`-signed `NoConsBindingIsInterval` (#1805).**  The named, curried-free form of the
derivation above: a union-well-formed context satisfies the interval-non-fibrancy discipline. -/
theorem WfContextUnion.noConsBindingIsInterval {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextUnion context) :
    context.NoConsBindingIsInterval :=
  wfContextUnion_noConsBindingIsIntervalAt context wellFormed

/-- **★ Dimensional usability preserved under reduction — re-pointed onto `WfContextUnion` (#1805).**  The
SR-residual closer `HasTypeUnion.stepPreservesDimensionalSubjectUsability` no longer carries the
`NoConsBindingIsInterval` discipline as a FREE hypothesis: it is OBTAINED from the threaded `WfContextUnion`
presupposition via `WfContextUnion.noConsBindingIsInterval`.  This is the W5-blocker dissolution — the pathApp
`.dimensional` argument-usability residual is dischargeable from well-formedness alone, no extra side condition. -/
theorem HasTypeUnion.stepPreservesDimensionalSubjectUsability_ofWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {reduct : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (reductTyped : HasTypeUnion profile context reduct intervalTypeCell) :
    context.isSubjectUsableAtModality reduct ObligationModality.dimensional = true :=
  HasTypeUnion.stepPreservesDimensionalSubjectUsability
    (WfContextUnion.noConsBindingIsInterval wellFormed) reductTyped

/-- **★ The interval is GENUINELY NON-FIBRANT (#1805 headline witness).**  An ordinary `cons` binding of the
interval is ill-formed: `WfContextUnion (empty.cons intervalTypeCell)` is uninhabitable because its `cons`-arm
conjunct demands `¬ Conv intervalTypeCell intervalTypeCell`, refuted by reflexivity.  The dimension can therefore
enter a well-formed context ONLY under the affine `lockCons` lock — the use-site statement of non-fibrancy. -/
theorem intervalConsNotWellFormed {profile : PolyProfile} :
    ¬ WfContextUnion ((TypingContext.empty : TypingContext profile 0).cons intervalTypeCell) :=
  fun wellFormed => WfContextUnion.headNotInterval wellFormed (Conv.refl intervalTypeCell)

/-- **Non-vacuity of the strengthened `cons` arm.**  The #1805 non-interval conjunct does NOT empty out fibrant
binders: a context binding a single universe code is union-well-formed (the universe code is a type via
`universeFormation`, and is never convertible to the interval via `intervalTypeCell_not_conv_universeCodeCell`).
So fibrant `cons` binders remain inhabited — only the interval is excluded. -/
theorem wfContextUnion_consUniverseInhabited {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    WfContextUnion ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag)) :=
  WfContextUnion.cons WfContextUnion.empty
    ⟨levelExpr.lsucc, flag, HasTypeUnion.universeFormation TypingContext.empty levelExpr flag⟩
    (fun convInterval =>
      intervalTypeCell_not_conv_universeCodeCell levelExpr flag (Conv.sym convInterval))

end FX1Poly.Typed
