import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables
import FX1Poly.Typed.Engine.RuleTables.FlatDescTelescopePi
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable

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

/-! ## The union-obligation form of the formation premise (TYTAB-2)

`FormationRule.obligations` is the pure-data, `List (ElimObligation profile)`, twin of
`premiseHolds` — the analogue of `ElimRule.obligations` / `IntroRule.obligations`.  Each obligation
packs its own `{scope, context, subject, classifier}`; the arm-swap consumer states the formation
premise as a single `∀ obligation ∈ rule.obligations …, HasTypeUnionOver … obligation.context
obligation.subject obligation.classifier`, exactly the elim/intro form.

The three families encode as:

  * `.baseType` -> `[]` (no children, `premiseHolds = True`).
  * `.flat` -> one obligation per flat child: `head_i : universeCodeCell level_i flag`, the children
    zipped positionally with `levels` (flat rows have all-zero shifts, so every head sits at
    `scope + 0 = scope`; a length mismatch degenerates to `[]`, never hit on a real flat row).
  * `.termIndexed` -> the carrier at `universeCodeCell level flag`, then each endpoint at the carrier.

These three helpers mirror the `FlatDescTelescopePi` / `TermIndexedFormerTelescope` premises one-for-one. -/

/-- **The flat-family obligation list** — one child-at-universe obligation per flat child, the children
zipped positionally with `levels`.  Total single-shape recursion over both spines: the empty levels /
empty children case ends the list; a `childCons` whose head sits at binder-shift `0` (every flat row)
pairs with the head level into a `head : universeCodeCell headLevel flag` obligation; any other shift or
a length mismatch degenerates to `[]` (never hit on a real flat row, where shifts are all `0` and the
levels length matches the children count). -/
def flatFormationObligations (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    {binderShifts : List Nat} → RawTermChildren binderShifts scope → List LevelExpr →
      List (ElimObligation profile)
  | _, .childNil, _ => []
  | _, .childCons (shift := childShift) head rest, levels =>
    match childShift, head, levels with
    | 0, head, headLevel :: restLevels =>
      { scope := scope, context := context, subject := head,
        classifier := universeCodeCell headLevel flag }
        :: flatFormationObligations profile context flag rest restLevels
    | 0, _, [] => []
    | _ + 1, _, _ => []

/-- **The term-indexed endpoint obligation list** — every later child typed AT the fixed `carrier`,
mirroring `TermIndexedEndpoints` (each endpoint at binder-shift `0`).  Total recursion over the
endpoint children spine; a non-zero-shift child degenerates to `[]` (never hit — every endpoint is at
shift `0`). -/
def termIndexedEndpointObligations (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (carrier : RawTerm scope) :
    {shifts : List Nat} → RawTermChildren shifts scope → List (ElimObligation profile)
  | _, .childNil => []
  | _, .childCons (shift := childShift) head rest =>
    match childShift, head with
    | 0, endpoint =>
      { scope := scope, context := context, subject := endpoint, classifier := carrier }
        :: termIndexedEndpointObligations profile context carrier rest
    | _ + 1, _ => []

/-- **The union-obligation form of the formation premise**, dispatched by the rule's family — the
pure-data twin of `premiseHolds`.  Base types demand nothing; flat formers demand each child at its
universe code; term-indexed formers demand the carrier at a universe code then each endpoint at the
carrier.  The signature mirrors `premiseHolds` exactly so the unified arm can carry the same data. -/
def FormationRule.obligations (rule : FormationRule) (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) {binderShifts : List Nat}
    (children : RawTermChildren binderShifts scope) (levels : List LevelExpr)
    (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag) :
    List (ElimObligation profile) :=
  match rule with
  | .baseType _ => []
  | .flat _ => flatFormationObligations profile context flag children levels
  | .termIndexed _ =>
    match children with
    | .childNil => []
    | .childCons (shift := carrierShift) carrierHead rest =>
      match carrierShift, carrierHead with
      | 0, carrierChild =>
        { scope := scope, context := context, subject := carrierChild,
          classifier := universeCodeCell level flag }
          :: termIndexedEndpointObligations profile context carrier rest
      | _ + 1, _ => []

/-! ## Table metadata (cascade-death `rfl` lemmas)

The arm-swap consumers route through these `rfl` shapes: they pin the obligation list for a
representative row at a concrete children spine so the consumer reduces by definitional equality. -/

/-- **Flat row (arrow), 2-child spine.**  The flat formation obligation list on a `[0, 0]` spine
`[domainCode, codomainCode]` at levels `[domainLevel, codomainLevel]` is the two child-at-universe
obligations — the cascade-death shape the flat arm consumer reduces through. -/
theorem flatFormationObligations_twoChild {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    (domainCode codomainCode : RawTerm scope) (domainLevel codomainLevel : LevelExpr) :
    flatFormationObligations profile context flag
        (RawTermChildren.pairFlat domainCode codomainCode) [domainLevel, codomainLevel]
      = [ { scope := scope, context := context, subject := domainCode,
            classifier := universeCodeCell domainLevel flag },
          { scope := scope, context := context, subject := codomainCode,
            classifier := universeCodeCell codomainLevel flag } ] :=
  rfl

/-- **Flat row (arrow), 2-child spine, via the unified `obligations`.**  The full
`FormationRule.obligations` dispatcher on the flat arrow rule reduces to the two child-at-universe
obligations (the `flat` arm forwards to `flatFormationObligations`; the carrier / level args are
inert). -/
theorem FormationRule_obligations_flat_arrow {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    (domainCode codomainCode : RawTerm scope) (domainLevel codomainLevel : LevelExpr)
    (carrier : RawTerm scope) (level : LevelExpr) :
    (FormationRule.flat { outputType := universeFormerOutput }).obligations profile context
        (RawTermChildren.pairFlat domainCode codomainCode) [domainLevel, codomainLevel]
        carrier level flag
      = [ { scope := scope, context := context, subject := domainCode,
            classifier := universeCodeCell domainLevel flag },
          { scope := scope, context := context, subject := codomainCode,
            classifier := universeCodeCell codomainLevel flag } ] :=
  rfl

/-- **Base-type row (bool).**  The base-type formation obligation list is empty — the base former
demands no premise. -/
theorem FormationRule_obligations_baseType {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    (baseRule : BaseTypeRuleDesc) {binderShifts : List Nat}
    (children : RawTermChildren binderShifts scope) (levels : List LevelExpr)
    (carrier : RawTerm scope) (level : LevelExpr) :
    (FormationRule.baseType baseRule).obligations profile context children levels carrier level flag
      = [] :=
  rfl

/-- **Term-indexed row (idCode), 3-child spine.**  The term-indexed formation obligation list on a
`[0, 0, 0]` spine `[carrierCode, leftEndpoint, rightEndpoint]` is the carrier-at-universe obligation
followed by the two endpoint-at-carrier obligations — the cascade-death shape the term-indexed arm
consumer reduces through. -/
theorem FormationRule_obligations_termIndexed_idCode {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    (carrierCode leftEndpoint rightEndpoint : RawTerm scope) (level : LevelExpr)
    (levels : List LevelExpr) :
    (FormationRule.termIndexed { outputType := termIndexedCarrierOutput }).obligations profile context
        (RawTermChildren.tripleFlat carrierCode leftEndpoint rightEndpoint) levels carrierCode level
        flag
      = [ { scope := scope, context := context, subject := carrierCode,
            classifier := universeCodeCell level flag },
          { scope := scope, context := context, subject := leftEndpoint, classifier := carrierCode },
          { scope := scope, context := context, subject := rightEndpoint,
            classifier := carrierCode } ] :=
  rfl

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
