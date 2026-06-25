import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionMemberCellRootGenerator
    — the member-cell root-generator projections (the TYTAB-1 collapse-inverter helpers)

The unified `intro` / `elim` typing arms carry their children as a packed `args : RawTermChildren
rule.argShifts scope` vector, so `rule.memberCell scope args` does not reduce to a concrete `.mkGen` head
until `args` is destructured.  These two lemmas destructure once per row and read off the head: the member
cell of any introducer / eliminator row is headed by exactly that row's generator.

Both are pure rule-table facts — `elimRuleOf_cases` / `introRuleOf_cases` enumerate the rows and `rfl`
reads the head per row.  They live UPSTREAM of every per-head inversion (and of the table-driven generic
inversion `HasTypeUnionGenericElimInversion`) so that the generic does not have to import the bespoke
`HasTypeUnionInversion` file — keeping the generic strictly above all the per-eliminator inversions it
subsumes.

## Zero-axiom

`rcases` over the shipped `elimRuleOf_cases` / `introRuleOf_cases` enumerators + per-row `match` on the
packed children + `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **The root generator of an eliminator row's member cell IS the row's generator.**  Destructures the
packed `args` vector per row so `memberCell` reduces, then reads the `.mkGen` head — `rfl` per row.  The
uniform head-projection the `elim`-arm inversions consume (a non-matching subject head clashes; a
matching head pins the generator). -/
theorem elimMemberCellRootGenerator {generator : Generator} {rule : ElimRule}
    (tableHit : elimRuleOf generator = some rule) {scope : Nat}
    (args : RawTermChildren rule.argShifts scope) :
    RawTerm.rootGenerator (rule.memberCell scope args) = generator := by
  rcases elimRuleOf_cases tableHit with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · match args with | .childCons _ (.childCons _ .childNil) => rfl
  · match args with | .childCons _ (.childCons _ .childNil) => rfl
  · match args with | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))) => rfl
  · match args with | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))) => rfl
  · match args with | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))) => rfl
  · match args with | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))) => rfl
  · match args with | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))) => rfl
  · match args with | .childCons _ (.childCons _ (.childCons _ .childNil)) => rfl
  · match args with | .childCons _ .childNil => rfl
  · match args with | .childCons _ .childNil => rfl
  · match args with | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))) => rfl

/-- **The root generator of an introducer row's member cell IS the row's generator.**  Destructures the
packed `args` vector per row so `memberCell` reduces, then reads the `.mkGen` head — `rfl` per row.  The
uniform head-projection the `intro`-arm inversions consume (a non-matching subject head clashes; a
matching head pins the generator). -/
theorem introMemberCellRootGenerator {generator : Generator} {rule : IntroRule}
    (tableHit : introRuleOf generator = some rule) {scope : Nat}
    (args : RawTermChildren rule.argShifts scope) :
    RawTerm.rootGenerator (rule.memberCell scope args) = generator := by
  rcases introRuleOf_cases tableHit with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- boolTrue (argShifts [])
  · rfl
  -- boolFalse (argShifts [])
  · rfl
  -- unit (argShifts [])
  · rfl
  -- interval0 (argShifts [])
  · rfl
  -- interval1 (argShifts [])
  · rfl
  -- natZero (argShifts [])
  · rfl
  -- lam (argShifts [0, 1])
  · match args with | .childCons _ (.childCons _ .childNil) => rfl
  -- pathLam (argShifts [1])
  · match args with | .childCons _ .childNil => rfl
  -- natSucc (argShifts [0])
  · match args with | .childCons _ .childNil => rfl
  -- listCons (argShifts [0, 0])
  · match args with | .childCons _ (.childCons _ .childNil) => rfl
  -- optionSome (argShifts [0])
  · match args with | .childCons _ .childNil => rfl
  -- optionNone (argShifts [])
  · rfl
  -- listNil (argShifts [])
  · rfl
  -- eitherInl (argShifts [0])
  · match args with | .childCons _ .childNil => rfl
  -- eitherInr (argShifts [0])
  · match args with | .childCons _ .childNil => rfl
  -- pair (argShifts [0, 0])
  · match args with | .childCons _ (.childCons _ .childNil) => rfl
  -- refl (argShifts [0])
  · match args with | .childCons _ .childNil => rfl

end FX1Poly.Typed
