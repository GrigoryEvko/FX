import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericVariableInversion
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility
import FX1Poly.Typed.Metatheory.Universe.UniverseCodeConversion
import FX1Poly.Typed.Cell.CellRenaming

/-! # FX1Poly/Typed/Metatheory/Validity/TypedAtUniverseFibrantlyUsable
    — the typed-implies-fibrantly-usable bridge (#1829 A1-CONJUNCT-WIRE rigorous core)

The four `HasTypeUnionValidity.classifierIsType` composite-data-former rows
(`listFormed_ofValidity` / `optionFormed_ofValidity` / `idFormed_ofCarrier` /
`bridgeFormed_ofBodyPremise`) each demand a BASE-context FIBRANT usability of a type code
(`context.isSubjectUsableAtModality elementType .fibrant = true`) that is NOT one of the
intro row's own obligation subjects (the listCons obligation is `head@elementType`, not
`elementType` itself), so it cannot be read off the intro `modalitiesUsable`.  The fact that
discharges them is the bridge `typedAtUniverseImpliesFibrantlyUsable`: a subject typed AT A
UNIVERSE CODE is fibrantly usable.

## Why the bridge is TRUE in reachable contexts but needs the interval-lock discipline

`isSubjectUsableAtModality subject .fibrant` only fails for `subject = var i` sitting EXACTLY
at a `lockCons`-depth-0 position (`isFibrantlyAccessibleAt context i = false`); any non-var head
is usable (`isSubjectUsableAtModality_ofNonVarHead`), and any cons-bound var is fibrantly
accessible.  A var at a `lockCons`-0 position is typed at the locked `dimensionType` — and per
the FitchTT / A1 design (fib-3a) the lock is pinned to the affine interval multiplier, so its
`dimensionType` is `intervalTypeCell`.  But `intervalTypeCell` is NOT `Conv`-related to a universe
code (distinct non-reducing head formers `gen_intervalCode` vs `gen_universeCode`), so a var typed
at a universe code CANNOT be at a `lockCons`-0 position — it is fibrantly accessible, hence usable.

The bridge therefore rests on ONE structural discipline: **every `lockCons` in the context carries
`intervalTypeCell`** (`AllLocksAreInterval`).  That discipline is the principled tightening of the
union well-formedness `WfContextUnion` (its `.lockCons` arm should add `dimensionType = intervalTypeCell`;
the construction site already locks `intervalTypeCell`, line 960-962 of `HasTypeUnionValidity`).

This file ships the FULL mathematical engine PARAMETERIZED over `AllLocksAreInterval` — entirely
self-contained, with NO dependency on `WfContextUnion` (so no import cycle with the validity file
that consumes the final lemma).  The `WfContextUnion`-signed deliverable
`typedAtUniverseImpliesFibrantlyUsable` is the three-line bridge
`WfContextUnion → AllLocksAreInterval → (this engine)`, landed where `WfContextUnion` is visible
(see the report / the validity file once its `.lockCons` arm carries the interval field).

## Zero-axiom verification

`invertAtVarHeadGeneric` (var-head inversion), `Conv.iff_normalForms_eq_of_confluence` (the
normal-form collapse, no SN premise), `rfl`-closed cell-rename / step-normality / head-generator
facts, structural recursion on the telescope, `Generator.noConfusion` / `Bool.noConfusion`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Audit-gated
in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-! ## The cell substrate the bridge needs -/

/-- Renaming the interval-type code cell leaves it unchanged — `intervalTypeCell` is a closed
nullary leaf (no payload data, no children), structurally identical to `emptyTypeCell`.  Holds by
`rfl` for the same reason as `rename_emptyTypeCell` / `rename_universeCodeCell`: `RawTerm.rename`
is `fold GenAlgebra.canonical`, which over the literal `childNil` rebuilds the same cell.  The
brick `lockedLookupIsInterval` uses to collapse the per-binder weakening shifts on the looked-up
interval. -/
theorem rename_intervalTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (intervalTypeCell (scope := sourceScope))
      = intervalTypeCell :=
  rfl

/-- **★ Interval ≢ universe under conversion (head no-confusion).**  The interval-type code
`intervalTypeCell` is NEVER convertible to a universe code `universeCodeCell levelExpr flag`.  Both
are step normal forms (head `gen_intervalCode` resp. `gen_universeCode`, `childNil` spine — no
redex root), so global confluence (`Conv.iff_normalForms_eq_of_confluence`, no SN premise) would
collapse their convertibility to syntactic equality — but their head generators are distinct.  The
exact `variableCell_not_conv_universeCodeCell` recipe at the interval head; the contradiction the
bridge derives once a `lockCons`-0 var (typed at the locked interval) is also claimed typed at a
universe code. -/
theorem intervalTypeCell_not_conv_universeCodeCell {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (universeCodeCell levelExpr flag) := by
  intro conv
  have intervalIsNormal : RawTerm.isStepNormalForm (intervalTypeCell : RawTerm scope) := rfl
  have universeIsNormal : RawTerm.isStepNormalForm (universeCodeCell levelExpr flag : RawTerm scope) := rfl
  have codesEqual : (intervalTypeCell : RawTerm scope) = universeCodeCell levelExpr flag :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) intervalIsNormal
      (StepStar.refl _) universeIsNormal).mp conv
  have headEq := congrArg RawTerm.headGenerator codesEqual
  rw [headGenerator_universeCodeCell,
    show RawTerm.headGenerator (intervalTypeCell : RawTerm scope) = Generator.gen_intervalCode from rfl]
    at headEq
  exact absurd headEq (by decide)

/-! ## The interval-lock discipline — the structural tightening the bridge rests on -/

/-- **The interval-lock discipline.**  Every `lockCons` in `context` carries the affine interval
`intervalTypeCell` as its locked dimension type (ordinary `cons` bindings are unconstrained).  Names
the structural fragment over which the typed-implies-fibrantly-usable bridge holds — exactly the
fragment the union well-formedness `WfContextUnion` pins once its `.lockCons` arm carries
`dimensionType = intervalTypeCell` (the FitchTT / fib-3a affine-multiplier discipline). -/
def TypingContext.AllLocksAreInterval {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext _bindingType => restContext.AllLocksAreInterval
  | _, .lockCons restContext dimensionType =>
      restContext.AllLocksAreInterval ∧ dimensionType = intervalTypeCell

/-- The empty context satisfies the interval-lock discipline. -/
theorem TypingContext.AllLocksAreInterval.empty {profile : PolyProfile} :
    (TypingContext.empty : TypingContext profile 0).AllLocksAreInterval := trivial

/-- A `cons` satisfies the discipline iff its prefix does (a plain binder adds no lock). -/
theorem TypingContext.AllLocksAreInterval.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restDiscipline : restContext.AllLocksAreInterval) :
    (restContext.cons bindingType).AllLocksAreInterval := restDiscipline

/-- Extend the discipline by an interval lock: a `lockCons intervalTypeCell` on a disciplined prefix
is disciplined.  The constructor every reachable lock is built by (the `pathLam` body binds the
affine interval), so the discipline holds for the whole kernel by construction. -/
theorem TypingContext.AllLocksAreInterval.lockConsInterval {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope}
    (restDiscipline : restContext.AllLocksAreInterval) :
    (restContext.lockCons (intervalTypeCell : RawTerm scope)).AllLocksAreInterval :=
  ⟨restDiscipline, rfl⟩

/-- The prefix of a disciplined `cons` is disciplined. -/
theorem TypingContext.AllLocksAreInterval.ofCons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (discipline : (restContext.cons bindingType).AllLocksAreInterval) :
    restContext.AllLocksAreInterval := discipline

/-- The prefix of a disciplined `lockCons` is disciplined. -/
theorem TypingContext.AllLocksAreInterval.ofLockCons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {dimensionType : RawTerm scope}
    (discipline : (restContext.lockCons dimensionType).AllLocksAreInterval) :
    restContext.AllLocksAreInterval := discipline.1

/-- **★ The locked lookup is the interval.**  Under the interval-lock discipline, every variable
that is NOT fibrantly accessible (i.e. resolves to a `lockCons`-depth-0 position) looks up to the
interval-type code `intervalTypeCell`.  Structural recursion on the telescope mirroring `lookup` /
`isFibrantlyAccessibleAt`: the `cons`-0 and `lockCons`-succ-via-`cons`-shaped leaves are settled by
the accessibility match, the deeper-binder cases recurse and collapse the weakening shift via
`rename_intervalTypeCell`, and the `lockCons`-0 leaf reads the discipline's `dimensionType =
intervalTypeCell` and again collapses the one weakening shift.  The structural fact the bridge
contradicts against `intervalTypeCell_not_conv_universeCodeCell`. -/
theorem TypingContext.lockedLookupIsInterval {profile : PolyProfile} :
    {scope : Nat} → (context : TypingContext profile scope) →
      context.AllLocksAreInterval → (index : Fin scope) →
        context.isFibrantlyAccessibleAt index = false →
          context.lookup index = intervalTypeCell
  | _, .empty, _discipline, index, _notAccessible =>
      absurd index.isLt (Nat.not_lt_zero index.val)
  | _, .cons _restContext _bindingType, _discipline, ⟨0, _⟩, notAccessible =>
      Bool.noConfusion notAccessible
  | _, .cons restContext _bindingType, discipline, ⟨position + 1, isLtSucc⟩, notAccessible => by
      rw [TypingContext.lookup_cons_succ]
      rw [restContext.lockedLookupIsInterval discipline.ofCons
        ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ notAccessible]
      exact rename_intervalTypeCell RawRenaming.weaken
  | _, .lockCons _restContext dimensionType, discipline, ⟨0, _⟩, _notAccessible => by
      rw [TypingContext.lookup_lockCons_zero, discipline.2]
      exact rename_intervalTypeCell RawRenaming.weaken
  | _, .lockCons restContext _dimensionType, discipline, ⟨position + 1, isLtSucc⟩, notAccessible => by
      rw [TypingContext.lookup_lockCons_succ]
      rw [restContext.lockedLookupIsInterval discipline.ofLockCons
        ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ notAccessible]
      exact rename_intervalTypeCell RawRenaming.weaken

/-! ## The bridge (parameterized over the interval-lock discipline) -/

/-- **★ The typed-implies-fibrantly-usable bridge (engine form).**  Under the interval-lock
discipline `AllLocksAreInterval`, a subject typed at a UNIVERSE CODE is fibrantly usable.  This is
the full mathematical content of `typedAtUniverseImpliesFibrantlyUsable`, decoupled from the union
well-formedness `WfContextUnion` (so there is no import cycle with the validity file that consumes
the final lemma): the `WfContextUnion`-signed deliverable is the three-line bridge
`WfContextUnion → AllLocksAreInterval → this`.

Proof: case on whether the subject's head is `gen_var`.  A NON-variable head is unconditionally
fibrantly usable (`isSubjectUsableAtModality_ofNonVarHead`).  A variable head inverts via
`invertAtVarHeadGeneric` to `subject = variableCell index` with the context lookup convertible to
the universe code; usability there is exactly `isFibrantlyAccessibleAt context index`, and were that
`false`, the locked lookup would be `intervalTypeCell` (`lockedLookupIsInterval`), making
`intervalTypeCell` convertible to the universe code — refuted by
`intervalTypeCell_not_conv_universeCodeCell`. -/
theorem typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (locksInterval : context.AllLocksAreInterval)
    (typed : HasTypeUnion profile context subject (universeCodeCell levelExpr flag)) :
    context.isSubjectUsableAtModality subject ObligationModality.fibrant = true := by
  by_cases headIsVar : RawTerm.headGenerator subject = Generator.gen_var
  · -- Variable head: invert, then rule out a lockCons-0 position via interval/universe no-confusion.
    obtain ⟨index, subjectShape, lookupConv⟩ :=
      HasTypeUnion.invertAtVarHeadGeneric typed headIsVar
    subst subjectShape
    rw [show variableCell index = (.mkGen Generator.gen_var index .childNil : RawTerm scope) from rfl,
      isSubjectUsableAtModality_var, isAccessibleAtModality_fibrant]
    cases fibrantCheck : context.isFibrantlyAccessibleAt index with
    | true => rfl
    | false =>
        exact absurd
          (TypingContext.lockedLookupIsInterval context locksInterval index fibrantCheck ▸ lookupConv)
          (intervalTypeCell_not_conv_universeCodeCell levelExpr flag)
  · -- Non-variable head: unconditionally fibrantly usable.
    cases subject with
    | mkGen generator payload children =>
        exact isSubjectUsableAtModality_ofNonVarHead context generator payload children
          ObligationModality.fibrant headIsVar

end FX1Poly.Typed
