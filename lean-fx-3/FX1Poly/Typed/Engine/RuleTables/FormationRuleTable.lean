import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables
import FX1Poly.Typed.Engine.RuleTables.FlatDescTelescopePi
import FX1Poly.Typed.Engine.RuleTables.TermIndexedFormer
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
  /-- A CUMULATIVE dependent type-former (Π/Σ binder-shape, List/Option element-shape): a cumulative
  dependent telescope (`DescTelescopePi`).  The codomain of a Π/Σ crosses a binder (it is typed in the
  domain-extended context at `scope + 1`), so this family's obligations include a BINDER-CROSSING
  codomain obligation — the additive substrate (TYTAB-2 wave U1) for promoting the four cumulative codes
  `gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` (carried by `typingRuleDescOf`)
  into the union's formation table.  The carried `TypingRuleDesc` is the cumulative table's own row (same
  `universeFormerOutput` output shape as `.flat`). -/
  | cumulative (rule : TypingRuleDesc)

/-- **The unified formation arm's output classifier**, dispatched by the rule's family: the base
type's pinned universe, the flat former's level-max universe, or the term-indexed former's
carrier-level universe. -/
def FormationRule.outputType (rule : FormationRule) (scope : Nat) (levels : List LevelExpr)
    (level : LevelExpr) (flag : UniverseFlag) : RawTerm scope :=
  match rule with
  | .baseType baseRule => baseRule.outputUniverse scope
  | .flat flatRule => flatRule.outputType scope levels flag
  | .termIndexed termIndexedRule => termIndexedRule.outputType scope level flag
  | .cumulative cumulativeRule => cumulativeRule.outputType scope levels flag

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
    `scope + 0 = scope`).  When `levels` is SHORTER than the children, the surplus children are FORCED to
    `Type@0` rather than dropped — the free-`levels` fix (see below), so the obligation list always covers
    EVERY child and the form is non-invertibly type-code-valid only when all its children are types.
  * `.termIndexed` -> the carrier at `universeCodeCell level flag`, then each endpoint at the carrier.

These three helpers mirror the `FlatDescTelescopePi` / `TermIndexedFormerTelescope` premises one-for-one. -/

/-- **The flat-family obligation list** — one child-at-universe obligation per flat child, the children
zipped positionally with `levels`.  Total single-shape recursion over both spines: the empty-children case
ends the list; a `childCons` whose head sits at binder-shift `0` (every flat row) pairs with the head level
(or, when `levels` is exhausted, the FORCED `Type@0`) into a `head : universeCodeCell … flag` obligation.
★ THE FREE-`levels` FIX: a `levels`-shorter-than-children spine no longer degenerates to `[]` — every child
gets an obligation.  Before the fix a `productTypeCell garbage garbage : Type@0` could be typed with NO
component obligation (the `formationRule` constructor takes `levels` FREE), making union type-code VALIDITY
NON-INVERTIBLE.  Forcing the surplus children to `Type@0` closes that hole, so the product / either / list /
option / Π codes' component validities are now recoverable by inversion (the wave-W4 head inversions). -/
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
    | 0, head, [] =>
      -- LEVELS EXHAUSTED but a child remains: FORCE the child to be a type (at `lzero`) rather than
      -- degenerating to `[]`.  Closes the free-`levels` escape: a flat former whose `levels` list is shorter
      -- than its children can no longer be typed vacuously (the old `[]` admitted `productTypeCell garbage
      -- garbage : Type@0` with no component obligation).  Every REAL flat-row reconstruction passes a
      -- `levels` whose length matches the children, so this branch is hit only by the would-be degenerate
      -- typing — which it now blocks by demanding `head : Type@0`.
      { scope := scope, context := context, subject := head,
        classifier := universeCodeCell LevelExpr.lzero flag }
        :: flatFormationObligations profile context flag rest []
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

/-- **The Π / Σ codomain obligation builder** — given the domain (at the ambient scope) and the codomain
(stored at binder-shift `1`, hence already at `RawTerm (scope + 1)`) plus their two levels, the two
cumulative obligations: the domain at its universe code in the ambient context, and the BINDER-CROSSING
codomain at its universe code in the domain-extended context `context.cons domain` at `scope + 1`. -/
def cumulativeBinderObligations (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag)
    (domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) : List (ElimObligation profile) :=
  [ { scope := scope, context := context, subject := domain,
      classifier := universeCodeCell domainLevel flag },
    { scope := scope + 1, context := context.cons domain, subject := codomain,
      classifier := universeCodeCell codomainLevel flag } ]

/-- **The cumulative-family obligation list** — dispatched on the children spine (the binder-shape Π/Σ
spine `[0, 1]` vs the element-shape List/Option spine `[0]`).  The match enumerates every constructor at
each level (`childNil` / `childCons`, head shift `0` / `_ + 1`, tail `childNil` / `childCons`, codomain
shift `1` / other, levels `[]` / `_ :: _`), so it is TOTAL — no partial-match propext leak.  A Π/Σ spine
yields `cumulativeBinderObligations` (domain + binder-crossing codomain); a List/Option spine yields the
single element obligation.  ★ THE FREE-`levels` FIX (the cumulative twin of the flat fix): a `levels`-short
List/Option/Π/Σ spine no longer degenerates to `[]` — the element (or domain + codomain) is FORCED to
`Type@0`, so every child gets an obligation and the cumulative type-code's validity is INVERTIBLE (the
wave-W4 Π-codomain head inversion).  Only a genuinely malformed shift-shape spine (never a real row) yields
`[]`. -/
def cumulativeFormationObligations (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    {binderShifts : List Nat} → RawTermChildren binderShifts scope → List LevelExpr →
      List (ElimObligation profile)
  | _, .childNil, _ => []
  | _, .childCons (shift := firstShift) firstChild restChildren, levels =>
    match firstShift, firstChild with
    | 0, headChild =>
      match restChildren, levels with
      -- List / Option element-shape spine: element at shift 0, then `childNil`.
      | .childNil, elementLevel :: _ =>
        [ { scope := scope, context := context, subject := headChild,
            classifier := universeCodeCell elementLevel flag } ]
      -- LEVELS EXHAUSTED but the single element remains: FORCE the element to be a type (at `lzero`) rather
      -- than degenerating to `[]`.  Closes the cumulative free-`levels` escape for the List / Option formers,
      -- the twin of the flat fix above: a `listTypeCell garbage` / `optionTypeCell garbage` can no longer be
      -- typed vacuously.  Every REAL List / Option reconstruction passes a length-1 `levels`, so this branch
      -- is hit only by the would-be degenerate typing — which it now blocks.
      | .childNil, [] =>
        [ { scope := scope, context := context, subject := headChild,
            classifier := universeCodeCell LevelExpr.lzero flag } ]
      -- Π / Σ binder-shape candidate: a second child after the domain.
      | .childCons (shift := secondShift) secondChild tailChildren, levels =>
        match secondShift, tailChildren, levels with
        -- Codomain at shift 1, no further children: a genuine binder-shape spine.
        | 1, .childNil, domainLevel :: codomainLevel :: _ =>
          cumulativeBinderObligations profile context flag headChild secondChild domainLevel codomainLevel
        -- LEVELS EXHAUSTED / too short on a Π / Σ binder spine: FORCE both the domain (ambient) and the
        -- binder-crossing codomain (domain-extended context) to be types at `lzero`, rather than degenerating
        -- to `[]`.  Closes the cumulative free-`levels` escape for the Π / Σ codes: a `piTyCodeCell garbage
        -- garbage` can no longer be typed vacuously.  Real Π / Σ reconstructions pass a length-2 `levels`.
        | 1, .childNil, [] =>
          cumulativeBinderObligations profile context flag headChild secondChild
            LevelExpr.lzero LevelExpr.lzero
        | 1, .childNil, [_] =>
          cumulativeBinderObligations profile context flag headChild secondChild
            LevelExpr.lzero LevelExpr.lzero
        | 1, .childCons _ _, _ => []
        | 0, _, _ => []
        | _ + 2, _, _ => []
    | _ + 1, _ => []

/-- **The union-obligation form of the formation premise**, dispatched by the rule's family — the
pure-data twin of `premiseHolds`.  Base types demand nothing; flat formers demand each child at its
universe code; term-indexed formers demand the carrier at a universe code then each endpoint at the
carrier; cumulative formers demand the domain / element at its universe code and (for Π/Σ) the
binder-crossing codomain at the domain-extended context.  The signature mirrors `premiseHolds` exactly so
the unified arm can carry the same data. -/
def FormationRule.obligations (rule : FormationRule) (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) {binderShifts : List Nat}
    (children : RawTermChildren binderShifts scope) (levels : List LevelExpr)
    (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag) :
    List (ElimObligation profile) :=
  match rule with
  | .baseType _ => []
  | .flat _ => flatFormationObligations profile context flag children levels
  | .cumulative _ => cumulativeFormationObligations profile context flag children levels
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
      | none =>
        match typingRuleDescOf generator with
        | some rule => some (.cumulative rule)
        | none => none

/-- **Reverse extraction (cumulative family).**  A formation table hit tagged `cumulative` re-exposes the
underlying `typingRuleDescOf` cumulative table hit (the four dependent type-code formers
`gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` plus the nullary `gen_unitCode`).
The TYTAB-2 wave-U2 inversion mirroring `formationRuleOf_flat_inv` / `_termIndexed_inv`: the cumulative
family is now the FINAL `formationRuleOf` clause, reached only when the three earlier sub-tables miss, so a
`.cumulative` hit forces a `typingRuleDescOf` hit.  Zero-axiom: nested `Option`/`FormationRule` constructor
analysis, no `simp`/`decide`. -/
theorem formationRuleOf_cumulative_inv {generator : Generator} {rule : TypingRuleDesc}
    (hit : formationRuleOf generator = some (FormationRule.cumulative rule)) :
    typingRuleDescOf generator = some rule := by
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
                | none =>
                  match typingRuleDescOf generator with
                  | some cumulativeRule => some (FormationRule.cumulative cumulativeRule)
                  | none => none) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit
      cases hflat : flatTypingRuleDescOf generator with
      | some flatRule => exfalso; rw [hflat] at hit; injection hit with ctorEq; injection ctorEq
      | none =>
          rw [hflat] at hit
          cases hterm : termIndexedFormerDescOf generator with
          | some termRule => exfalso; rw [hterm] at hit; injection hit with ctorEq; injection ctorEq
          | none =>
              rw [hterm] at hit
              cases hcumulative : typingRuleDescOf generator with
              | some cumulativeRule =>
                  rw [hcumulative] at hit
                  injection hit with ctorEq; injection ctorEq with ruleEq
                  exact congrArg Option.some ruleEq
              | none => exfalso; rw [hcumulative] at hit; injection hit

/-- **Forward extraction (cumulative family, NON-nullary).**  A `typingRuleDescOf` hit at a NON-`gen_unitCode`
generator (i.e. one of the four dependent type-code formers `gen_piTyCode` / `gen_sigmaTyCode` /
`gen_listCode` / `gen_optionCode`) produces the `.cumulative` formation row.  The nullary `gen_unitCode` is
EXCLUDED because it ALSO carries a `baseTypeRuleDescOf` row, which `formationRuleOf` tries FIRST — so
`formationRuleOf .gen_unitCode = some (.baseType …)`, never `.cumulative`.  Each of the four non-unit codes
is absent from the base-type / flat / term-indexed sub-tables, so `formationRuleOf` falls through to the
final cumulative clause: a per-generator `rfl` after the `if`-chain enumeration.  Zero-axiom: `DecidableEq
Generator` nested-`if` pin + per-code `rfl`. -/
theorem formationRuleOf_cumulative {generator : Generator} {rule : TypingRuleDesc}
    (isCumulative : typingRuleDescOf generator = some rule)
    (isNotNullary : generator ≠ Generator.gen_unitCode) :
    formationRuleOf generator = some (FormationRule.cumulative rule) := by
  by_cases isPi : generator = .gen_piTyCode
  · subst isPi
    obtain rfl : rule = { outputType := universeFormerOutput } :=
      Option.some.inj (isCumulative.symm.trans typingRuleDescOf_piTyCode)
    rfl
  · by_cases isSigma : generator = .gen_sigmaTyCode
    · subst isSigma
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        Option.some.inj (isCumulative.symm.trans typingRuleDescOf_sigmaTyCode)
      rfl
    · by_cases isList : generator = .gen_listCode
      · subst isList
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          Option.some.inj (isCumulative.symm.trans typingRuleDescOf_listCode)
        rfl
      · by_cases isOption : generator = .gen_optionCode
        · subst isOption
          obtain rfl : rule = { outputType := universeFormerOutput } :=
            Option.some.inj (isCumulative.symm.trans typingRuleDescOf_optionCode)
          rfl
        · exfalso
          dsimp only [typingRuleDescOf] at isCumulative
          rw [if_neg isPi, if_neg isSigma, if_neg isList, if_neg isOption,
            if_neg isNotNullary] at isCumulative
          contradiction

/-- **A cumulative formation rule is never the variable generator.**  The cumulative-family twin of
`flatFormationRuleImpliesNotVariable`: `typingRuleDescOf .gen_var = none`, so any generator carrying a
cumulative formation rule is non-`gen_var`.  Re-uses the shipped `formationRuleImpliesNotVariable` (which
already discharges this from a `typingRuleDescOf` hit) after `formationRuleOf_cumulative_inv` re-exposes the
underlying table hit. -/
theorem cumulativeFormationRuleImpliesNotVariable {generator : Generator} {rule : TypingRuleDesc}
    (isCumulativeFormation : typingRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var :=
  formationRuleImpliesNotVariable isCumulativeFormation

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
                | none =>
                  match typingRuleDescOf generator with
                  | some cumulativeRule => some (FormationRule.cumulative cumulativeRule)
                  | none => none) := by
        unfold formationRuleOf; rw [hbase]
      rw [reduced] at hit
      cases hflat : flatTypingRuleDescOf generator with
      | some flatRule => rw [hflat] at hit; injection hit with ctorEq; injection ctorEq
      | none =>
          rw [hflat] at hit
          cases hterm : termIndexedFormerDescOf generator with
          | some termRule => rw [hterm] at hit; injection hit with ctorEq; injection ctorEq
          | none =>
              rw [hterm] at hit
              cases hcumulative : typingRuleDescOf generator with
              | some cumulativeRule =>
                  rw [hcumulative] at hit; injection hit with ctorEq; injection ctorEq
              | none => rw [hcumulative] at hit; injection hit

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
                | none =>
                  match typingRuleDescOf generator with
                  | some cumulativeRule => some (FormationRule.cumulative cumulativeRule)
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
          | none =>
              rw [hterm] at hit
              cases hcumulative : typingRuleDescOf generator with
              | some cumulativeRule =>
                  rw [hcumulative] at hit; injection hit with ctorEq; injection ctorEq
              | none => rw [hcumulative] at hit; injection hit

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
                | none =>
                  match typingRuleDescOf generator with
                  | some cumulativeRule => some (FormationRule.cumulative cumulativeRule)
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
          | none =>
              exfalso
              rw [hterm] at hit
              cases hcumulative : typingRuleDescOf generator with
              | some cumulativeRule =>
                  rw [hcumulative] at hit; injection hit with ctorEq; injection ctorEq
              | none => rw [hcumulative] at hit; injection hit

end FX1Poly.Typed
