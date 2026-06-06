import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.WfContextDescLookup
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/IsTypeDescRigidity
    — native rigidity + leaf characterization of formation type-hood (HT-A4 brick B1, off the old `HasType`)

The native formation `Decidable (IsTypeDesc Γ T)` decision procedure (HT-A4 #887) mirrors the old-engine
`IsType.decidableOfWellFormed` (`IsTypeDecidable.lean`) but consumes ONLY `HasTypeDesc` pieces — no
`HasType.toHasType` oracle.  That decider cases on `T`'s head generator; its load-bearing LEAF facts are the
rigidity that collapses a `Conv` to an equality at the variable case, plus the two non-recursive leaves
(universe code is always a type; a variable cell is a type iff its lookup is a universe code).  This file
ships those leaves natively.

## The bricks

* `IsTypeDesc.hasNoStep` — **formation types are NORMAL** (no outgoing `Step`).  The native subject-side
  rigidity, read straight off the shipped formation no-step invariant `HasTypeDesc.subjectAdmitsNoStep`
  (`HasTypeDescSubjectReduction.lean`): a formation TYPE is the subject of a `HasTypeDesc` derivation (at a
  universe code), and every formation-typed subject is normal.  The `HasTypeDesc` twin of `IsType.hasNoStep`.
* `Conv.eq_of_isTypeDesc` — **convertible formation types are EQUAL**.  Both endpoints are normal
  (`IsTypeDesc.hasNoStep`), so `Conv` collapses to `Eq` by rigidity (`Conv.eq_of_noStep`).  The `HasTypeDesc`
  twin of `Conv.eq_of_isType` — the tool the variable leaf uses to turn `inversionVariable`'s convertibility
  into a syntactic cell equality.
* `IsTypeDesc.ofUniverseCodeCell` — a universe code is always a formation type (`HasTypeDesc.universeFormation`
  classifies `universeCodeCell levelExpr flag` at `universeCodeCell levelExpr.lsucc flag`).  The decider's
  `gen_universeCode` leaf.
* `IsTypeDesc.variableCell_iff_lookupIsUniverseCode` — a variable cell is a type **iff** its lookup is a
  universe code.  The ONE leaf consulting the context (over `WfContextDesc`, the native formation
  well-formedness): forward by `HasTypeDesc.inversionVariable` + the rigidity above
  (`WfContextDesc.lookupIsTypeDesc` makes the lookup a type, so the `Conv` is an `Eq`); backward by the
  universe-code destructor + the variable rule `HasTypeDesc.var`.

NOT here (deferred to subsequent HT-A4 bricks): the non-type-former refutation leaf
(`subjectRootGeneratorGeneric`-driven), the recursive Π/Σ `decideWithWitness`, and the `Decidable`
assembly.

## Zero-axiom verification

`hasNoStep`/`eq_of_isTypeDesc` delegate to shipped zero-axiom rigidity (`subjectAdmitsNoStep`,
`Conv.eq_of_noStep`); `ofUniverseCodeCell` is the `universeFormation` constructor; the variable leaf is the
forward rigidity collapse + the backward `var` rule, exactly the old-engine proof with `HasTypeDesc` pieces.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Formation types are normal** — a `HasTypeDesc`-type (a term inhabiting some universe per the formation
engine) has no outgoing `Step`.  Reads off the shipped formation no-step invariant
`HasTypeDesc.subjectAdmitsNoStep`: the type IS the subject of its `HasTypeDesc`-at-a-universe-code derivation,
and every formation-typed subject is normal.  The native subject-side rigidity, twin of `IsType.hasNoStep`. -/
theorem IsTypeDesc.hasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsTypeDesc profile context classifier) :
    ∀ reduct : RawTerm scope, Step classifier reduct → False := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact typed.subjectAdmitsNoStep

/-- **Convertible formation types are equal** — two `HasTypeDesc`-types that convert are syntactically equal.
Both are normal (`IsTypeDesc.hasNoStep`), so the convertibility collapses to an equality by rigidity
(`Conv.eq_of_noStep`).  The native twin of `Conv.eq_of_isType`; the variable leaf turns
`HasTypeDesc.inversionVariable`'s convertibility into a cell equality through it. -/
theorem Conv.eq_of_isTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {firstType secondType : RawTerm scope}
    (firstIsType : IsTypeDesc profile context firstType)
    (secondIsType : IsTypeDesc profile context secondType)
    (convertibility : Conv firstType secondType) :
    firstType = secondType :=
  Conv.eq_of_noStep firstIsType.hasNoStep secondIsType.hasNoStep convertibility

/-- **A universe code is always a formation type.**  `HasTypeDesc.universeFormation` classifies
`universeCodeCell levelExpr flag` by `universeCodeCell levelExpr.lsucc flag`, so it inhabits a universe.
The decider's `gen_universeCode` leaf; the native twin of `IsType.ofUniverseCodeCell`. -/
theorem IsTypeDesc.ofUniverseCodeCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsTypeDesc profile context (universeCodeCell levelExpr flag) :=
  ⟨levelExpr.lsucc, flag, HasTypeDesc.universeFormation context levelExpr flag⟩

/-- **A variable cell is a formation type iff its lookup is a universe code.**  The ONE decision leaf that
consults the context, over `WfContextDesc` (native formation well-formedness).

Forward: `HasTypeDesc.inversionVariable` yields `Conv (universeCodeCell levelExpr flag) (context.lookup
index)`; both endpoints are formation types (`IsTypeDesc.ofUniverseCodeCell` and
`WfContextDesc.lookupIsTypeDesc`), so the rigidity `Conv.eq_of_isTypeDesc` collapses the `Conv` to a cell
equality, whence the lookup's head is `gen_universeCode`.

Backward: the universe-code destructor `eq_universeCodeCell_of_headGenerator` rebuilds `context.lookup index
= universeCodeCell levelExpr flag`, and the variable rule `HasTypeDesc.var` types `variableCell index` by
exactly its lookup.  The native twin of `IsType.variableCell_iff_lookupIsUniverseCode`. -/
theorem IsTypeDesc.variableCell_iff_lookupIsUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContextDesc context) (index : Fin scope) :
    IsTypeDesc profile context (variableCell index)
      ↔ RawTerm.headGenerator (context.lookup index) = Generator.gen_universeCode := by
  constructor
  · rintro ⟨levelExpr, flag, typed⟩
    have converts : Conv (universeCodeCell levelExpr flag) (context.lookup index) :=
      HasTypeDesc.inversionVariable typed
    have lookupIsType : IsTypeDesc profile context (context.lookup index) :=
      WfContextDesc.lookupIsTypeDesc context wellFormed index
    have codeIsType : IsTypeDesc profile context (universeCodeCell levelExpr flag) :=
      IsTypeDesc.ofUniverseCodeCell levelExpr flag
    have cellsEqual :
        universeCodeCell levelExpr flag = context.lookup index :=
      Conv.eq_of_isTypeDesc codeIsType lookupIsType converts
    rw [← cellsEqual]
    exact headGenerator_universeCodeCell levelExpr flag
  · intro lookupHead
    obtain ⟨levelExpr, flag, lookupEqualsCode⟩ :=
      eq_universeCodeCell_of_headGenerator lookupHead
    refine ⟨levelExpr, flag, ?_⟩
    rw [← lookupEqualsCode]
    exact HasTypeDesc.var context index

end FX1Poly.Typed
