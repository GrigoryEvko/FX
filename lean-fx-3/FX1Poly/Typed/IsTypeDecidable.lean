import FX1Poly.Typed.HasTypeInversion
import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.HasTypeDecidableConv
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/IsTypeDecidable
    — characterization of which cells are types (current var/conv/universe fragment)

`IsType context classifier` unfolds to `∃ levelExpr flag, HasType context
classifier (universeCodeCell levelExpr flag)`.  On the current `HasType` fragment
(`var` / `conv` / `universeFormation`) this is a decidable trichotomy on
`classifier`'s head generator:

* `gen_universeCode` head ⇒ always a type (`IsType.universeCodeCell`, via
  `HasType.universeFormation`);
* `gen_var` head ⇒ a type *iff* the looked-up classifier is itself a universe
  code (`IsType.variableCell_iff_lookupIsUniverseCode`) — the only case that
  consults the context; forward by `inversionVariable` + normal-form rigidity
  (`Conv.eq_of_isType`), backward by the universe-code destructor + the variable
  rule;
* any other head ⇒ never a type (`IsType.not_of_headGenerator`, via
  `typedSubjectIsVariableOrUniverseCode`).

These three lemmas are the full mathematical content of `Decidable IsType`
(#303); the decision procedure assembles them by casing on the cell's head
generator (`DecidableEq Generator`) over the two cell destructors in
`UniverseCodeShape` — built next on top of this characterization.

## Zero-axiom verification

The forward variable case rests on normal-form rigidity (`Conv.eq_of_isType`,
itself zero-axiom) rather than on any normalizer: both endpoints of the
`inversionVariable` convertibility are types, hence non-stepping leaves, so the
`Conv` collapses to a literal cell equality.  The refutation `subst`s the
cell-shape equality and closes by `rfl` at default transparency (a concrete
cell's head generator reduces definitionally).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Universe-code cells are always types: `universeFormation` classifies
`universeCodeCell levelExpr flag` by `universeCodeCell levelExpr.lsucc flag`.
(Named `ofUniverseCodeCell`, not `universeCodeCell`, so it does not shadow the
cell constructor inside other `IsType.`-prefixed theorem bodies.) -/
theorem IsType.ofUniverseCodeCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsType profile context (universeCodeCell levelExpr flag) :=
  ⟨levelExpr.lsucc, flag, HasType.universeFormation context levelExpr flag⟩

/-- A variable cell is a type exactly when its looked-up classifier is a universe
code.

Forward: `inversionVariable` yields `Conv (universeCodeCell levelExpr flag)
(context.lookup index)`; both endpoints are types (`IsType.universeCodeCell` and
`WfContext.lookupIsType`), so normal-form rigidity (`Conv.eq_of_isType`)
collapses the `Conv` to a cell equality, whence the looked-up head is
`gen_universeCode`.

Backward: the universe-code destructor rebuilds `context.lookup index =
universeCodeCell levelExpr flag`, and the variable rule types `variableCell
index` by exactly its looked-up classifier. -/
theorem IsType.variableCell_iff_lookupIsUniverseCode {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContext context) (index : Fin scope) :
    IsType profile context (variableCell index)
      ↔ RawTerm.headGenerator (context.lookup index) = Generator.gen_universeCode := by
  constructor
  · rintro ⟨levelExpr, flag, typed⟩
    have converts :
        Conv (universeCodeCell levelExpr flag) (context.lookup index) :=
      HasType.inversionVariable wellFormed typed
    have lookupIsType : IsType profile context (context.lookup index) :=
      WfContext.lookupIsType context wellFormed index
    have codeIsType : IsType profile context (universeCodeCell levelExpr flag) :=
      IsType.ofUniverseCodeCell levelExpr flag
    have cellsEqual :
        universeCodeCell levelExpr flag = context.lookup index :=
      Conv.eq_of_isType codeIsType lookupIsType converts
    rw [← cellsEqual]
    exact headGenerator_universeCodeCell levelExpr flag
  · intro lookupHead
    obtain ⟨levelExpr, flag, lookupEqualsCode⟩ :=
      eq_universeCodeCell_of_headGenerator lookupHead
    refine ⟨levelExpr, flag, ?_⟩
    rw [← lookupEqualsCode]
    exact HasType.var context index

/-- A cell whose head generator is neither `gen_var` nor `gen_universeCode` is
never a type: every typed subject is a variable or universe-code cell
(`typedSubjectIsVariableOrUniverseCode`), so no derivation can type this cell as
a universe code. -/
theorem IsType.not_of_headGenerator {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (notVariable : RawTerm.headGenerator classifier ≠ Generator.gen_var)
    (notUniverseCode :
      RawTerm.headGenerator classifier ≠ Generator.gen_universeCode) :
    ¬ IsType profile context classifier := by
  rintro ⟨levelExpr, flag, typed⟩
  rcases typed.typedSubjectIsVariableOrUniverseCode with
    ⟨index, subjectIsVariable⟩ | ⟨codeLevel, codeFlag, subjectIsUniverseCode⟩
  · subst subjectIsVariable
    exact notVariable (headGenerator_variableCell index)
  · subst subjectIsUniverseCode
    exact notUniverseCode (headGenerator_universeCodeCell codeLevel codeFlag)

/-- Decide whether `classifier` inhabits some universe, for the current
fragment.  Assembles the three trichotomy lemmas by casing on the cell
`mkGen generator payload children` (single constructor → large elimination into
the `Type`-valued `Decidable`; `payload` carries the variable index as DATA,
which an `Exists` could not supply), then deciding on `generator` via
`DecidableEq Generator` (`dite`, never `by_cases` — the latter pulls
`Classical`):

* `gen_universeCode` → `isTrue` via `IsType.ofUniverseCodeCell`;
* `gen_var` → nested decision on `RawTerm.headGenerator (context.lookup payload)`
  routed through `IsType.variableCell_iff_lookupIsUniverseCode`;
* otherwise → `isFalse` via `IsType.not_of_headGenerator`
  (`RawTerm.headGenerator (mkGen generator …) ≡ generator`, so the negated
  `dite` hypotheses discharge it definitionally).

Each cell-shape collapse (`mkGen … = universeCodeCell / variableCell`) is the
`RawTermChildren.eq_childNil` rewrite, applied to the `IsType` Prop goal rather
than the `Decidable` goal to keep `rw`'s motive trivial. -/
def IsType.decidableOfWellFormed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (classifier : RawTerm scope) : Decidable (IsType profile context classifier) :=
  match classifier with
  | .mkGen generator payload children =>
      if hUniverse : generator = Generator.gen_universeCode then by
        subst hUniverse
        have cellIsUniverseCode :
            (RawTerm.mkGen Generator.gen_universeCode payload children)
              = universeCodeCell payload.1 payload.2 := by
          rw [RawTermChildren.eq_childNil children]
          rfl
        exact isTrue (by
          rw [cellIsUniverseCode]
          exact IsType.ofUniverseCodeCell payload.1 payload.2)
      else if hVariable : generator = Generator.gen_var then by
        subst hVariable
        have cellIsVariable :
            (RawTerm.mkGen Generator.gen_var payload children)
              = variableCell payload := by
          rw [RawTermChildren.eq_childNil children]
          rfl
        exact
          if hLookupIsUniverseCode :
              RawTerm.headGenerator (context.lookup payload)
                = Generator.gen_universeCode then
            isTrue (by
              rw [cellIsVariable]
              exact (IsType.variableCell_iff_lookupIsUniverseCode
                wellFormed payload).mpr hLookupIsUniverseCode)
          else
            isFalse (by
              rw [cellIsVariable]
              exact fun isTypeVariable =>
                hLookupIsUniverseCode
                  ((IsType.variableCell_iff_lookupIsUniverseCode
                    wellFormed payload).mp isTypeVariable))
      else
        isFalse (IsType.not_of_headGenerator hVariable hUniverse)

end FX1Poly.Typed
