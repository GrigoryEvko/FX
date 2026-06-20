import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables
import FX1Poly.Typed.Engine.RuleTables.FlatDescTelescopePi
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormer

/-! # FX1Poly/Typed/FormationRuleTable — TYTAB-1 formation-collapse foundation

The three FORMATION-role families (base-type, flat, term-indexed) all share the SAME subject shape
`.mkGen generator payload children` and the
SAME output kind (a universe / type code); they differ ONLY in their grown premise — none, a flat
`FlatDescTelescopePi` spine, or a `TermIndexedFormerTelescope`.  Because every formation premise
mentions only the GROWN engine (`HasTypeDescPi`-based telescopes), NEVER the union being defined, the
entire premise SHAPE is first-order data — so the three families now collapse into ONE generic
`formationRule` arm of `HasTypeUnionOver` reading a single tagged `FormationRule`.

This module is the descriptor + table the unified arm consumes — the formation analogue of
`DataIntroSpec` / `RecursiveDataIntroSpec`.  The collapse (3 arms -> 1, bundle field 3 -> 1, the
companion-induction merges) consumes these definitions; the unified `formationRule` arm
carries `isFormation` through a `cases rule` dispatch, so NO backward-compat smart constructors and NO
within-family disjointness lemmas are needed. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- ★ **The unified formation rule**, tagging which of the three formation families a row belongs to.
Each constructor wraps the family's existing per-generator descriptor, so the carried data is exactly
the shipped tables — no new content, just one tagged carrier. -/
inductive FormationRule where
  /-- A nullary base-type former (bool/empty/nat/unit/interval code): childless, no premise. -/
  | baseType (rule : BaseTypeRuleDesc)
  /-- A flat data-former (arrow/product/sum/either/equiv + the ʃ/♭/♯ modal codes): a flat telescope. -/
  | flat (rule : TypingRuleDesc)
  /-- A term-indexed former (Id / Bridge): a carrier-plus-endpoints telescope. -/
  | termIndexed (rule : TermIndexedFormerDesc)

/-- **The premise the unified formation arm demands**, dispatched by the rule's family.  Base types
demand nothing (`True`); flat formers demand the flat telescope; term-indexed formers demand the
carrier-plus-endpoints telescope.  Every premise is GROWN (no union recursion), so storing the premise
shape as data costs no positivity. -/
def FormationRule.premiseHolds (rule : FormationRule) (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) {binderShifts : List Nat}
    (children : RawTermChildren binderShifts scope) (levels : List LevelExpr)
    (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag) : Prop :=
  match rule with
  | .baseType _ => True
  | .flat _ => FlatDescTelescopePi profile context flag levels children
  | .termIndexed _ => TermIndexedFormerTelescope profile context children carrier level flag

/-- **The unified formation arm's output classifier**, dispatched by the rule's family: the base
type's pinned universe, the flat former's level-max universe, or the term-indexed former's
carrier-level universe. -/
def FormationRule.outputType (rule : FormationRule) (scope : Nat) (levels : List LevelExpr)
    (level : LevelExpr) (flag : UniverseFlag) : RawTerm scope :=
  match rule with
  | .baseType baseRule => baseRule.outputUniverse scope
  | .flat flatRule => flatRule.outputType scope levels flag
  | .termIndexed termIndexedRule => termIndexedRule.outputType scope level flag

/-- **The unified formation table.**  A generator's formation rule, found by trying the three family
tables in turn (the families are disjoint, so the order is immaterial to membership).  The unified
`formation` bundle field will be exactly this dispatcher; a `ProfileExtension` adding a type-former is
one more row here, never a new typing arm. -/
def formationRuleOf (generator : Generator) : Option FormationRule :=
  match baseTypeRuleDescOf generator with
  | some rule => some (.baseType rule)
  | none =>
    match flatTypingRuleDescOf generator with
    | some rule => some (.flat rule)
    | none =>
      match termIndexedFormerDescOf generator with
      | some rule => some (.termIndexed rule)
      | none => none

/-- `gen_boolCode` is a base-type formation row (metadata check, `rfl`). -/
theorem formationRuleOf_boolCode :
    formationRuleOf .gen_boolCode
      = some (.baseType
          { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }) :=
  rfl

/-- `gen_arrowCode` is a flat formation row (metadata check, `rfl`). -/
theorem formationRuleOf_arrowCode :
    formationRuleOf .gen_arrowCode = some (.flat { outputType := universeFormerOutput }) :=
  rfl

/-- `gen_idCode` is a term-indexed formation row (metadata check, `rfl`). -/
theorem formationRuleOf_idCode :
    formationRuleOf .gen_idCode = some (.termIndexed { outputType := termIndexedCarrierOutput }) :=
  rfl

/-- **Reverse extraction (base-type family).**  A formation table hit tagged `baseType` re-exposes the
underlying base-type table hit — the inversion the soundness cascade dispatches on.  Zero-axiom: nested
`Option`/`FormationRule` constructor analysis, no `simp`/`decide`. -/
theorem formationRuleOf_baseType_inv {generator : Generator} {rule : BaseTypeRuleDesc}
    (hit : formationRuleOf generator = some (FormationRule.baseType rule)) :
    baseTypeRuleDescOf generator = some rule := by
  cases hbase : baseTypeRuleDescOf generator with
  | some baseRule =>
      have reduced : formationRuleOf generator = some (FormationRule.baseType baseRule) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit
      injection hit with ctorEq
      injection ctorEq with ruleEq
      exact congrArg Option.some ruleEq
  | none =>
      exfalso
      have reduced : formationRuleOf generator
          = (match flatTypingRuleDescOf generator with
              | some flatRule => some (FormationRule.flat flatRule)
              | none =>
                match termIndexedFormerDescOf generator with
                | some termRule => some (FormationRule.termIndexed termRule)
                | none => none) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit
      cases hflat : flatTypingRuleDescOf generator with
      | some flatRule => rw [hflat] at hit; injection hit with ctorEq; injection ctorEq
      | none =>
          rw [hflat] at hit
          cases hterm : termIndexedFormerDescOf generator with
          | some termRule => rw [hterm] at hit; injection hit with ctorEq; injection ctorEq
          | none => rw [hterm] at hit; injection hit

/-- **Reverse extraction (flat family).** -/
theorem formationRuleOf_flat_inv {generator : Generator} {rule : TypingRuleDesc}
    (hit : formationRuleOf generator = some (FormationRule.flat rule)) :
    flatTypingRuleDescOf generator = some rule := by
  cases hbase : baseTypeRuleDescOf generator with
  | some baseRule =>
      exfalso
      have reduced : formationRuleOf generator = some (FormationRule.baseType baseRule) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit; injection hit with ctorEq; injection ctorEq
  | none =>
      have reduced : formationRuleOf generator
          = (match flatTypingRuleDescOf generator with
              | some flatRule => some (FormationRule.flat flatRule)
              | none =>
                match termIndexedFormerDescOf generator with
                | some termRule => some (FormationRule.termIndexed termRule)
                | none => none) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit
      cases hflat : flatTypingRuleDescOf generator with
      | some flatRule =>
          rw [hflat] at hit; injection hit with ctorEq; injection ctorEq with ruleEq
          exact congrArg Option.some ruleEq
      | none =>
          exfalso
          rw [hflat] at hit
          cases hterm : termIndexedFormerDescOf generator with
          | some termRule => rw [hterm] at hit; injection hit with ctorEq; injection ctorEq
          | none => rw [hterm] at hit; injection hit

/-- **Reverse extraction (term-indexed family).** -/
theorem formationRuleOf_termIndexed_inv {generator : Generator} {rule : TermIndexedFormerDesc}
    (hit : formationRuleOf generator = some (FormationRule.termIndexed rule)) :
    termIndexedFormerDescOf generator = some rule := by
  cases hbase : baseTypeRuleDescOf generator with
  | some baseRule =>
      exfalso
      have reduced : formationRuleOf generator = some (FormationRule.baseType baseRule) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit; injection hit with ctorEq; injection ctorEq
  | none =>
      have reduced : formationRuleOf generator
          = (match flatTypingRuleDescOf generator with
              | some flatRule => some (FormationRule.flat flatRule)
              | none =>
                match termIndexedFormerDescOf generator with
                | some termRule => some (FormationRule.termIndexed termRule)
                | none => none) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit
      cases hflat : flatTypingRuleDescOf generator with
      | some flatRule => exfalso; rw [hflat] at hit; injection hit with ctorEq; injection ctorEq
      | none =>
          rw [hflat] at hit
          cases hterm : termIndexedFormerDescOf generator with
          | some termRule =>
              rw [hterm] at hit; injection hit with ctorEq; injection ctorEq with ruleEq
              exact congrArg Option.some ruleEq
          | none => exfalso; rw [hterm] at hit; injection hit

end FX1Poly.Typed
