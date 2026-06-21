import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGeneralElim
import FX1Poly.Typed.Engine.RuleTables.FlatDescTelescopePi
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables
import FX1Poly.Typed.Engine.RuleTables.TypingTableBundle
import FX1Poly.Core.Metatheory.Canonicity.BoolCanonicalFormsCandidate
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep

/-! # FX1Poly/Typed/HasTypeUnion — NATIVE-25: the seed unified judgment + Bridge full adequacy

THE SEQUENCING PIVOT (the ultrathink resequencing, user-approved direction): the judgment-boundary
wall is SYSTEMIC, not a pathElim quirk — recursive data constructors need data-typed arguments, data
eliminators need data-typed scrutinees, pathElim needs Bridge-typed paths, and closed
endpoints/numerals are NOT host-typable (the NATIVE-08 wall).  Every adequacy task in the wave
(NATIVE-29..35) hits the same wall.  So instead of building a throwaway bridge-fragment union here and
the real union at NATIVE-46, this file SEEDS the NATIVE-46 unified judgment now and proves the Bridge
adequacy INTO it.

## TYTAB-1 brick 3: the judgment is GENERIC OVER THE TABLE BUNDLE

The native arms each read a per-generator typing table.  Brick 1 (`TypingTableBundle`) gathered those
tables into one record; brick 3 rebases the judgment to READ that record: the inductive is now
`HasTypeUnionOver (bundle : TypingTableBundle)`, every native arm consulting `bundle.field generator`
in place of the hardcoded `xRuleDescOf generator`.  The shipped kernel is `HasTypeUnion :=
HasTypeUnionOver fxTypingBundle` (an abbrev; the table-driven arms read the bundle's native fields,
the cumulative-formation field stays the `ofGrown` host's domain).  A `ProfileExtension`'s bundle now
gets the whole judgment for free — typing a new former is adding a bundle row, no new arm.  The
constructor aliases below (`HasTypeUnion.ofGrown` …) pin `bundle := fxTypingBundle` so every existing
derivation site and `cases`/`induction` keeps its call convention; the rule premises are definitionally
the shipped tables (`fxTypingBundle_faithful`), so `rfl` still discharges every `isFoo` row obligation.

After the TYTAB-1 arm collapse the inductive has exactly FIVE arms —
`ofGrown · formationRule · intro · elim · conv`.  The former per-family introducer / eliminator arms
became the two uniform table-reading arms `intro` (reading `introRuleOf`) and `elim` (reading
`elimRuleOf`).  After the final TYTAB-1 builder collapse the kernel exposes exactly ONE generic
builder per typing role — `formationRule` / `intro` / `elim` (plus the structural `ofGrown` / `conv`).
Every per-family / per-sub-family smart constructor that once wrapped these arms has been DELETED; a
constructor of any arity is one `IntroRule` / `ElimRule` / `FormationRule` table row, fed to the bare
builder, never its own wrapper.

## The seed design: the grown embedding + the table-driven arms

  * One EMBEDDING arm (`ofGrown`) — its premise is a completed prior inductive, so positivity is
    trivial (no mutual telescope blocks, the banked positivity trap avoided).  It provides the grown
    typing mass.  The base-type / data-intro / flat / term-indexed-former families are now inlined as
    the table-driven `formationRule` arm — the three formation families (base-type / flat /
    term-indexed) share ONE unified `formationRule` arm, reading the bundle fields directly per family
    — no engine indirection.
  * The uniform `intro` / `elim` arms — the NATIVE-23/24 compositional closure that was the walls,
    with premises in the union ITSELF reflected into one `rule.obligations` list per arm (the graded
    binder body and the eliminator branches recurse there).

## What becomes typable for the FIRST TIME (the wall-falls smokes)

  * `endpointRedexNativelyTypedWhole` — the WHOLE endpoint redex `pathApp(pathLam(Type@0), 0)` typed
    in ONE derivation (intro arm + data arm composing inside one judgment; previously the path lived
    in the graded engine and the argument in the data engine with no judgment containing both).
  * `constantIntervalLambdaNativelyTyped` — `λ(x:Bool).0 : Π(x:Bool).Interval`: a λ whose BODY lives
    in the data engine.  Untypable in every prior engine (the host demands a host-typed body; `0` is
    not host-typable).

## ★ The bridge semantics ARE the union's rows (the bespoke engine is RETIRED)

The bespoke `HasTypeDescBridge` engine — interval/bridge formation, endpoints, path intro/elim — has
been deleted (NATIVE-45).  Its six arms were never a separate semantics: each was exactly a row of
this union (intervalFormation→baseType row, endpoints→data rows, bridgeFormation→termIndexed row,
pathIntro→graded intro row, pathElim→general elim row with the RECURSIVE premises discharged by the
arm's own recursion — the judgment boundary dissolves exactly as the NATIVE-04 verdict predicted).
Full adequacy (`HasTypeDescBridge.toNativeUnion` / `toNativeUnionExact`) was proved INTO this union
before retirement (Rung 103) and the compat theorems were removed WITH the engine; the rows below are
now the sole carriers of the bridge semantics.  The one honest divergence the adequacy surfaced
survives in the rows themselves: the native base-type interval-formation row pins `standard`
(the deliberate DI-1b-flagpin determinism discipline) where the bespoke any-flag formation was
flag-AMBIGUOUS — the native strictness is the better semantics, now the only semantics.

## Honest scope

  * The `conv` arm IS present (NATIVE-46, additive — the fifth arm): a union typing at `classifier`
    plus `Conv classifier reclassifier` plus a universe-code derivation for `reclassifier` reclassifies
    the subject, exactly as `HasTypeDescPi.conv` does on the grown engine.  `Conv` is a raw StepStar
    relation never mentioning typing, so the arm is strictly positive and free-subject `cases` over all
    five arms stays propext-clean.
  * The union-wide affine-rejection statement (`pathLam(pair(var 0, var 0))` untypable in the UNION)
    needs a host-engine pathLam-head-untyped lemma not yet in `HasTypeDescPiDataHeadUntyped`; the
    graded-arm rejection is shipped (NATIVE-23); the union-wide form is pinned as wave work.
  * The reverse direction (union restricted to bridge heads → Bridge) is the per-family wave adequacy.

## NATIVE-36 scope note (appended): the new families are table-resident; the embeddings STAY

NATIVE-36 makes the NON-recursive data-eliminator families (boolElim / optionMatch / eitherMatch,
idJ, fst / snd — all via the uniform `elim` arm), the n-ary / recursive data-INTRO families (natSucc /
listCons / optionSome / optionNone / eitherInl / eitherInr / pair / refl — all via the uniform `intro`
arm), and the listElim family (via the `elim` arm, discharging the batch-1 pin "listElim union
residency lands with NATIVE-33") RESIDENT in `HasTypeUnion` as table-driven
arms, with their native twin tables hoisted into the pre-union `UnionRuleTables` (the import-cycle
hazard avoided exactly as NATIVE-32 avoided it).  The scrutinee-embedding arms the data eliminators need
were RETIRED by the NATIVE-42 toNativeRows conversions (every data value now
enters through its native table row).  The base-type / data-intro / flat / term-indexed-former embeddings
have been inlined as the `formationRule` formation arm + the uniform `intro` arm (the three formation
families — base-type / flat / term-indexed — collapsed into the single `formationRule` arm, and the
nullary data constructors typed by the uniform `intro` arm directly);
the remaining `ofGrown` embedding STAYS an embedding for now.  The spike→union transfers
(`DataElimUnionSpike.toNativeUnion`, `DataIntroNaryUnionSpike.toNativeUnion`,
`ListElimUnionSpike.toNativeUnion`) live in separate post-union files (they import both the spike and
this union).

## Zero-axiom

Embeddings are constructor applications; the recursive arms mirror the keystone arms.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

-- The native recursive-eliminator row schema (`NativeRecursiveElimRule` + `nativeRecursiveElimRuleOf`,
-- the natElim / natRec rows) now lives in `UnionRuleTables`, co-located with its sibling
-- `listElimNativeRuleOf` and the other native rule tables, low in the import graph (imported above).
-- The `recursiveElim` arm below references it through the bundle field `bundle.recursiveElim`.

/-- **The seed unified native judgment, GENERIC over the table bundle (the NATIVE-46 miniature, TYTAB-1
brick 3).**  Four engine embeddings (the base typing mass) + the two table-driven keystone arms with
RECURSIVE premises (the compositional closure).  Every native arm reads `bundle.field generator`; the
shipped kernel `HasTypeUnion` pins `bundle := fxTypingBundle`.  A subject typed here is typed BY THE
NATIVE SYSTEM — table rows and their compositions — with no judgment boundary between the families. -/
inductive HasTypeUnionOver (bundle : TypingTableBundle) (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  /-- Embed the host (grown) engine: var / universe / formation / piIntro / piElim / conv. -/
  | ofGrown {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (hostTyped : HasTypeDescPi profile context subject classifier) :
      HasTypeUnionOver bundle profile context subject classifier
  /-- ★ **The unified FORMATION arm (TYTAB-1 arm collapse): base-type + flat + term-indexed in ONE.**
  All three formation families have the SAME `.mkGen generator payload children` subject and a universe /
  type-code output; they differ ONLY in their grown premise (none / `FlatDescTelescopePi` / a
  `TermIndexedFormerTelescope`), which the `FormationRule` carries as data (`premiseHolds` dispatches on
  the family).  Fixed-slot existentials — `levels` (flat), `carrier`+`level` (term-indexed), `flag` (both)
  — are phantom where a family doesn't use them.  A new type-former whose typing is a table row + grown
  telescope is now a `formationRule` spec row, not a typing arm. -/
  | formationRule {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (rule : FormationRule)
      (levels : List LevelExpr) (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
      (isFormationRule : bundle.formationRule generator = some rule)
      (premisesHold : ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
        HasTypeUnionOver bundle profile obligation.context obligation.subject obligation.classifier) :
      HasTypeUnionOver bundle profile context (.mkGen generator payload children)
        (rule.outputType scope levels level flag)
  /-- ★ **The unified INTRODUCER arm (TYTAB-1 arm collapse): all four introducer families in ONE.**
  Nullary constructors / graded binders (lam, pathLam) / recursive constructors (natSucc, listCons) /
  grown constructors (optionSome … refl) share the SAME `rule.memberCell scope args` subject and read the
  SAME uniform `IntroRule` table.  Their premises — child formations, a graded binder's body at a
  binder-shifted scope, formedness — are reflected into ONE `rule.obligations` list (every entry a UNION
  obligation, grown premises homogenized via `ofGrown` exactly as `listElim` did), plus a `sideCondition`
  (the load-bearing usage grade for the graded binders).  The union sits strictly positively under the
  `∀`, as for the `elim` arm.  A new constructor of any arity is one `IntroRule` row, never an arm. -/
  | intro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : IntroRule)
      (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag)
      (isIntro : bundle.intro generator = some rule)
      (sideHolds : rule.sideCondition scope args)
      (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        HasTypeUnionOver bundle profile obligation.context obligation.subject obligation.classifier) :
      HasTypeUnionOver bundle profile context
        (rule.memberCell scope args) (rule.outputType scope args params)
  /-- ★ **The unified ELIMINATOR arm (TYTAB-1 arm collapse): all six eliminator families in ONE.**
  app / pathApp / natElim / natRec / boolElim / optionMatch / eitherMatch / idJ / fst / snd / listElim
  share the SAME subject shape (`rule.memberCell scope args`, the eliminator cell) and read the SAME
  uniform `ElimRule` table.  Their premises — scrutinee + branches, at ANY arity, at base OR
  binder-shifted dependent scopes (natElim's step at `scope + 2`), each at a rule-computed classifier in
  a rule-computed extended context — are reflected into ONE `rule.obligations` list, every entry typed
  RECURSIVELY in the union.  The union sits strictly positively under the `∀` (positivity-checked), so no
  telescope inductive and no mutualization.  A new eliminator of any arity is one `ElimRule` row, never a
  new arm. -/
  | elim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : ElimRule)
      (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag)
      (isElim : bundle.elim generator = some rule)
      (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        HasTypeUnionOver bundle profile obligation.context obligation.subject obligation.classifier) :
      HasTypeUnionOver bundle profile context
        (rule.memberCell scope args) (rule.outputType scope args params)
  /-- The CONVERSION arm (the conv-closure): a union-typed subject reclassifies along a raw
  definitional equality, with the target classifier itself union-typed at a universe code.
  Field-identical to `HasTypeDescPi.conv` — shape parity is what the embedding adequacies need.
  This arm dissolves the no-conv-arm wall: union substitution no longer needs host-typed
  substituent images, and congruence-step subject reduction can absorb the dependent-scrutinee
  classifier drift. -/
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasTypeUnionOver bundle profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasTypeUnionOver bundle profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasTypeUnionOver bundle profile context subject reclassifier
  /-- ★ **The native VARIABLE arm (TYTAB-2 VAR).**  A variable is typed at its looked-up context binding —
  the one irreducible structural leaf previously reachable only through `ofGrown` (host `HasTypeDesc.var`).
  Genuinely structural (not a generator-keyed table row), so it stays a dedicated arm. -/
  | var {scope : Nat} (context : TypingContext profile scope) (index : Fin scope) :
      HasTypeUnionOver bundle profile context (variableCell index) (context.lookup index)
  /-- ★ **The native UNIVERSE-FORMATION arm (TYTAB-2 UNIV).**  `Type@L(flag) : Type@(L+1)(flag)` — the second
  irreducible host-only rule (host `HasTypeDesc.universeFormation`).  It is NOT a formation table row: its
  level-shift output reads the subject's PAYLOAD level `L` (`universeCodeCell L f = .mkGen gen_universeCode
  (L, f) .childNil`), which the table-driven `FormationRule.outputType scope levels level flag` cannot see, so
  a sound table row is inexpressible — it is a structural/leaf rule like `var`, kept as a dedicated arm. -/
  | universeFormation {scope : Nat} (context : TypingContext profile scope)
      (levelExpr : LevelExpr) (flag : UniverseFlag) :
      HasTypeUnionOver bundle profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)

/-! ## The shipped kernel judgment + constructor aliases (TYTAB-1 brick 3)

`HasTypeUnion` is the canonical kernel judgment: `HasTypeUnionOver` pinned to `fxTypingBundle`.  The
native bundle fields are definitionally the shipped tables (`fxTypingBundle_faithful`), so the
abbrev is the SAME relation the kernel always had — only now generic in the bundle.  The constructor
aliases pin `bundle := fxTypingBundle` and re-list each arm's binders so every derivation site keeps its
call convention; `cases` / `induction` route through the abbrev to `HasTypeUnionOver`'s constructors, so
inversion is unchanged. -/

/-- ★ **The shipped kernel unified judgment** — `HasTypeUnionOver` at the canonical FX table bundle. -/
abbrev HasTypeUnion (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  HasTypeUnionOver fxTypingBundle profile context subject classifier

/-- `ofGrown` at the canonical bundle. -/
@[reducible] def HasTypeUnion.ofGrown {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (hostTyped : HasTypeDescPi profile context subject classifier) :
    HasTypeUnion profile context subject classifier :=
  HasTypeUnionOver.ofGrown (bundle := fxTypingBundle) hostTyped

/-- `elim` at the canonical bundle — the unified eliminator builder. -/
@[reducible] def HasTypeUnion.elim {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : ElimRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (isElim : elimRuleOf generator = some rule)
    (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    HasTypeUnion profile context (rule.memberCell scope args) (rule.outputType scope args params) :=
  HasTypeUnionOver.elim (bundle := fxTypingBundle) context generator rule args params level0 level1 flag
    isElim premisesHold

/-- `intro` at the canonical bundle — the unified introducer builder. -/
@[reducible] def HasTypeUnion.intro {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : IntroRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (isIntro : introRuleOf generator = some rule)
    (sideHolds : rule.sideCondition scope args)
    (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    HasTypeUnion profile context (rule.memberCell scope args) (rule.outputType scope args params) :=
  HasTypeUnionOver.intro (bundle := fxTypingBundle) context generator rule args params level0 level1 flag
    isIntro sideHolds premisesHold

/-! ## ★ TYTAB-2: the grown-premise -> union-obligations bridge

The `formationRule` arm now premises UNION obligations (one per child), homogenizing the three formation
families exactly as the `intro` / `elim` arms do.  The bridge below transports the GROWN premise
(`premiseHolds` — the telescope a derivation site supplies) into that union-obligation form, so the smart
constructor's external signature is unchanged: callers still pass a grown telescope, the bridge converts.
Per-family the obligation list and the telescope are zipped one-for-one (the W0 helpers
`flatFormationObligations` / `termIndexedEndpointObligations` mirror the telescope cons structure), so a
`cases hmem` on `List.Mem` walks them in lockstep against an induction on the telescope.  Zero-axiom:
`cases` / structural recursion on the telescope inductives + `cases hmem` + `HasTypeUnion.ofGrown`. -/

/-- **The flat-family bridge.**  A grown flat telescope discharges every flat-family obligation: induct on
the `FlatDescTelescopePi` spine; each `cons head headLevel … headTyped restTyped` supplies
`headTyped : HasTypeDescPi … head (universeCodeCell headLevel flag)`, the matching head obligation, via
`HasTypeUnion.ofGrown`; the tail recurses.  The obligation list (`flatFormationObligations`) and the
telescope are zipped identically, so `cases hmem` walks them together. -/
theorem flatFormationPremiseToObligations {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescopePi profile context flag levels children) :
    ∀ obligation ∈ flatFormationObligations profile context flag children levels,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier :=
  match telescope with
  | .nil => fun obligation hmem => by cases hmem
  | .cons _head _headLevel _restLevels _rest headTyped restTyped =>
      fun obligation hmem => by
        cases hmem with
        | head => exact HasTypeUnion.ofGrown headTyped
        | tail _ hmem =>
            exact flatFormationPremiseToObligations restTyped obligation hmem

/-- **The endpoint-family bridge.**  A grown endpoint telescope discharges every endpoint obligation:
induct on the `TermIndexedEndpoints` spine; each `cons endpoint … endpointTyped restTyped` supplies
`endpointTyped : HasTypeDescPi … endpoint carrier`, the matching endpoint obligation, via
`HasTypeUnion.ofGrown`; the tail recurses. -/
theorem termIndexedEndpointsToObligations {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {carrier : RawTerm scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope}
    (endpoints : TermIndexedEndpoints profile context carrier children) :
    ∀ obligation ∈ termIndexedEndpointObligations profile context carrier children,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier :=
  match endpoints with
  | .nil => fun obligation hmem => by cases hmem
  | .cons _endpoint _rest endpointTyped restTyped =>
      fun obligation hmem => by
        cases hmem with
        | head => exact HasTypeUnion.ofGrown endpointTyped
        | tail _ hmem =>
            exact termIndexedEndpointsToObligations restTyped obligation hmem

/-- **The term-indexed-family bridge.**  A grown term-indexed former telescope discharges every
term-indexed formation obligation.  `cases` on the telescope frees the `children` index to the concrete
`.childCons carrier rest` spine, so the `.termIndexed` arm of `FormationRule.obligations` reduces to the
carrier obligation followed by the endpoint obligations; the carrier discharges via `ofGrown carrierTyped`,
the endpoints forward to `termIndexedEndpointsToObligations`.  Stated over a FREE `shifts`/`children` so the
telescope `cases` does not fight the abstract `generator.binderShifts`. -/
theorem termIndexedFormerTelescopeToObligations {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} (termRule : TermIndexedFormerDesc)
    (premise : TermIndexedFormerTelescope profile context children carrier level flag)
    (levels : List LevelExpr) :
    ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context children
        levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  cases premise with
  | mk _carrier _rest _level _flag carrierTyped endpointsTyped =>
      intro obligation hmem
      cases hmem with
      | head => exact HasTypeUnion.ofGrown carrierTyped
      | tail _ hmem =>
          exact termIndexedEndpointsToObligations endpointsTyped obligation hmem

/-- **The cumulative-family bridge.**  A grown cumulative dependent telescope (`DescTelescopePi`)
discharges every cumulative-family obligation.  `cases` on the telescope frees the children spine; the
binder-shape Π/Σ spine `[0, 1]` exposes the domain typing at the ambient context and the codomain typing
at the domain-extended context (each a `HasTypeDescPi`, lifted to the union via `ofGrown`), matching the
two obligations of `cumulativeFormationObligations`; the element-shape List/Option spine `[0]` exposes the
single element typing; every other spine yields an empty obligation list (the `∀` is vacuous).  The
telescope's cumulative-context-extension IS the binder-crossing the codomain obligation needs, so the two
walk in lockstep against `cases hmem`. -/
theorem cumulativeFormationPremiseToObligations {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : DescTelescopePi profile (currentDepth := 0) context levels flag children) :
    ∀ obligation ∈ cumulativeFormationObligations profile context flag children levels,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  cases telescope with
  | nil _context _flag =>
      intro obligation hmem
      cases hmem
  | cons _context domain domainLevel restLevels _flag rest domainTyped restTyped =>
      -- First child at shift 0 (domain or element).  Split the tail spine to tell Π/Σ from List/Option.
      cases rest with
      | childNil =>
          -- List / Option element-shape spine `[0]`.
          intro obligation hmem
          cases hmem with
          | head => exact HasTypeUnion.ofGrown domainTyped
          | tail _ tailMember => cases tailMember
      | childCons codomain deeperRest =>
          rename_i codomainShift _deeperShifts
          cases codomainShift with
          | succ priorShift =>
              cases priorShift with
              | zero =>
                  -- Codomain at shift 1: a genuine Π/Σ binder-shape spine.  Expose the codomain typing
                  -- from the depth-1 telescope tail.
                  cases deeperRest with
                  | childNil =>
                      cases restTyped with
                      | cons _context _codomain _codomainLevel _restLevels2 _flag _rest2
                          codomainTyped _restTyped2 =>
                          intro obligation hmem
                          cases hmem with
                          | head => exact HasTypeUnion.ofGrown domainTyped
                          | tail _ tailMember =>
                              cases tailMember with
                              | head => exact HasTypeUnion.ofGrown codomainTyped
                              | tail _ deeperMember => cases deeperMember
                  | childCons _deeper2 _deeper3 =>
                      intro obligation hmem
                      cases hmem
              | succ _ =>
                  intro obligation hmem
                  cases hmem
          | zero =>
              intro obligation hmem
              cases hmem

/-- ★ **The grown-premise -> union-obligations bridge (the TYTAB-2 crux).**  Transports a grown formation
premise (`premiseHolds`) into the union-obligation form the swapped `formationRule` arm now demands.
`cases rule` dispatches the four families: `baseType` has the empty obligation list (the `∀` is
vacuous); `flat` forwards to `flatFormationPremiseToObligations` over its `FlatDescTelescopePi`;
`termIndexed` forwards to `termIndexedFormerTelescopeToObligations` (carrier obligation + endpoints);
`cumulative` forwards to `cumulativeFormationPremiseToObligations` (domain / element + binder-crossing
codomain) over its `DescTelescopePi`.  Zero-axiom: `cases` on the telescope inductives + `cases hmem` +
`HasTypeUnion.ofGrown`. -/
theorem formationPremiseToObligations {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator}
    {children : RawTermChildren generator.binderShifts scope}
    {rule : FormationRule} {levels : List LevelExpr} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (premise : rule.premiseHolds profile context children levels carrier level flag) :
    ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  cases rule with
  | baseType _baseRule =>
      intro obligation hmem
      cases hmem
  | flat _flatRule =>
      exact flatFormationPremiseToObligations premise
  | cumulative _cumulativeRule =>
      exact cumulativeFormationPremiseToObligations premise
  | termIndexed termRule =>
      exact termIndexedFormerTelescopeToObligations termRule premise levels

/-- `formationRule` at the canonical bundle — the unified formation builder.  Its external signature is
UNCHANGED (still takes the grown `premise`); the body now bridges that premise into the swapped arm's
union-obligation form via `formationPremiseToObligations`, so every existing derivation site compiles
without change. -/
@[reducible] def HasTypeUnion.formationRule {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (payload : generator.payload scope) (children : RawTermChildren generator.binderShifts scope)
    (rule : FormationRule)
    (levels : List LevelExpr) (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (isFormationRule : formationRuleOf generator = some rule)
    (premise : rule.premiseHolds profile context children levels carrier level flag) :
    HasTypeUnion profile context (.mkGen generator payload children)
      (rule.outputType scope levels level flag) :=
  HasTypeUnionOver.formationRule (bundle := fxTypingBundle) context generator payload children
    rule levels carrier level flag isFormationRule (formationPremiseToObligations premise)

/-- `conv` at the canonical bundle. -/
@[reducible] def HasTypeUnion.conv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (typed : HasTypeUnion profile context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped : HasTypeUnion profile context reclassifier
      (universeCodeCell levelExpr flag)) :
    HasTypeUnion profile context subject reclassifier :=
  HasTypeUnionOver.conv (bundle := fxTypingBundle) levelExpr flag typed converts reclassifierTyped

/-- `var` at the canonical bundle — the native variable leaf. -/
@[reducible] def HasTypeUnion.var {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    HasTypeUnion profile context (variableCell index) (context.lookup index) :=
  HasTypeUnionOver.var (bundle := fxTypingBundle) context index

/-- `universeFormation` at the canonical bundle — the native universe leaf (`Type@L : Type@(L+1)`). -/
@[reducible] def HasTypeUnion.universeFormation {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeUnion profile context (universeCodeCell levelExpr flag)
      (universeCodeCell levelExpr.lsucc flag) :=
  HasTypeUnionOver.universeFormation (bundle := fxTypingBundle) context levelExpr flag

/-! ## ★ The wall-falls smokes — typable for the FIRST time -/

/-- **★ The WHOLE endpoint redex in ONE derivation.**  `pathApp(pathLam(Type@0), 0) : Type@1` — the
path through the graded intro arm, the endpoint argument through the data embedding, composed by the
recursive elim arm.  No prior judgment contained both premises. -/
theorem endpointRedexNativelyTypedWhole {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeUnion.elim TypingContext.empty .gen_pathApp pathAppElimRule
    (.childCons (pathLamCell (universeCodeCell LevelExpr.lzero flag))
      (.childCons intervalZeroCell .childNil))
    (.childCons (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (.childCons (universeCodeCell LevelExpr.lzero flag)
        (.childCons (universeCodeCell LevelExpr.lzero flag) .childNil)))
    (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) LevelExpr.lzero flag rfl
    (fun obligation hmem => by
      cases hmem with
      | head =>
        refine HasTypeUnion.intro TypingContext.empty .gen_pathLam pathLamIntroRule
          (.childCons (universeCodeCell LevelExpr.lzero flag) .childNil)
          (.childCons (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) .childNil)
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl (Nat.zero_le 1) ?_
        intro obligation hmem
        cases hmem with
        | head =>
          exact HasTypeUnion.ofGrown
            (HasTypeDescPi.ofFormation
              (HasTypeDesc.universeFormation
                (TypingContext.empty.cons intervalTypeCell) LevelExpr.lzero flag))
        | tail _ hmem => cases hmem
      | tail _ hmem => cases hmem with
        | head =>
          refine HasTypeUnion.intro TypingContext.empty .gen_interval0 interval0IntroRule
            .childNil .childNil LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          intro obligation hmem; cases hmem
        | tail _ hmem =>
          cases hmem with
          | head =>
            -- The NEW result-formedness obligation: carrierCode `Type@1` is a type, by self-typing
            -- (`Type@1 : Type@2`), at the pinned `level0 = lsucc (lsucc lzero)`, `flag`.
            exact HasTypeUnion.ofGrown
              (HasTypeDescPi.ofFormation
                (HasTypeDesc.universeFormation TypingContext.empty
                  (LevelExpr.lsucc LevelExpr.lzero) flag))
          | tail _ hmem => cases hmem)

/-- **★ The λ-over-data wall falls.**  `λ(x:Bool).0 : Π(x:Bool).Interval` — a λ whose BODY (`0`) is
typed by the DATA embedding, with the domain/classifier formation premises through the base-type
embedding.  Untypable in every prior engine: the host `piIntro` demands a host-typed body and the
interval endpoint is not host-typable (`intervalZeroGrownUntypable`, the NATIVE-08 wall). -/
theorem constantIntervalLambdaNativelyTyped {profile : PolyProfile} :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (lamCell boolTypeCell intervalZeroCell)
      (piTyCodeCell boolTypeCell intervalTypeCell) := by
  refine HasTypeUnion.intro TypingContext.empty .gen_lam lamIntroRule
    (.childCons boolTypeCell (.childCons intervalZeroCell .childNil))
    (.childCons intervalTypeCell .childNil)
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
  intro obligation hmem
  cases hmem with
  | head =>
    exact HasTypeUnion.formationRule TypingContext.empty .gen_boolCode () .childNil
      (.baseType { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard })
      [] intervalTypeCell LevelExpr.lzero UniverseFlag.standard rfl trivial
  | tail _ hmem => cases hmem with
    | head =>
      exact HasTypeUnion.formationRule (TypingContext.empty.cons boolTypeCell)
        .gen_intervalCode () .childNil
        (.baseType { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard })
        [] intervalTypeCell LevelExpr.lzero UniverseFlag.standard rfl trivial
    | tail _ hmem => cases hmem with
      | head =>
        refine HasTypeUnion.intro (TypingContext.empty.cons boolTypeCell) .gen_interval0
          interval0IntroRule .childNil .childNil LevelExpr.lzero LevelExpr.lzero
          UniverseFlag.standard rfl trivial ?_
        intro obligation hmem; cases hmem
      | tail _ hmem => cases hmem

/-! ## The coverage gate -/

/-- **The NATIVE-25 coverage record.**  Each field is a distinct live property of the seed union; an
inhabitant certifies the union is exercised (both wall-falls compositions).  The two bridge-adequacy
fields were removed with the bespoke `HasTypeDescBridge` engine (NATIVE-45): the bridge semantics are
now carried directly by the union's rows, so there is no longer a separate engine to translate FROM. -/
structure NativeUnionCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The whole endpoint redex types in one derivation. -/
  wholeRedexTyped : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
    (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
  /-- The λ-over-data composition types. -/
  lambdaOverDataTyped : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
    (lamCell boolTypeCell intervalZeroCell)
    (piTyCodeCell boolTypeCell intervalTypeCell)

/-- **★ The NATIVE-25 coverage gate** — inhabited by the shipped witnesses. -/
theorem nativeUnionCoverageWitness {profile : PolyProfile} (flag : UniverseFlag) :
    NativeUnionCoverage profile flag where
  wholeRedexTyped := endpointRedexNativelyTypedWhole flag
  lambdaOverDataTyped := constantIntervalLambdaNativelyTyped

/-! ## ★ NATIVE-36 headline smokes — the new families exercised IN THE UNION

Cheap restatements through the new arms: the recursive `natSucc` row applied twice (the numeral tower
the host engine could not state), one boolElim ι reduct typed through the two-branch match arm, and the
listElim nil-ι typed through the listElim arm. -/

/-- **★ The numeral `2` types IN THE UNION through the recursive `natSucc` arm applied twice.**
`2 = natSucc(natSucc(natZero)) : Nat` through `recursiveUnaryIntro` twice, the `natZero` base reached
via the native natZero data-intro row.  Exactly the statement a host-premise schema could not make — the
numeral tower closes purely through the union's own recursive intro arm. -/
theorem numeralTwoTypedThroughUnionRecursiveIntroTwice {profile : PolyProfile} :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (natSuccCell (natSuccCell natZeroCell)) natTypeCell :=
  HasTypeUnion.intro TypingContext.empty .gen_natSucc natSuccIntroRule
    (.childCons (natSuccCell natZeroCell) .childNil) .childNil
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial
    (fun obligation hmem => by
      cases hmem with
      | head =>
        exact HasTypeUnion.intro TypingContext.empty .gen_natSucc natSuccIntroRule
          (.childCons natZeroCell .childNil) .childNil
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial
          (fun obligation hmem => by
            cases hmem with
            | head =>
              refine HasTypeUnion.intro TypingContext.empty .gen_natZero natZeroIntroRule
                .childNil .childNil LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl
                trivial ?_
              intro obligation hmem; cases hmem
            | tail _ hmem => cases hmem)
      | tail _ hmem => cases hmem)

/-- **★ One boolElim ι reduct types IN THE UNION through the two-branch match arm.**  A union-typed
`boolElim` on `boolTrue` (both branches union-typed at the result `C`) ι-reduces to the THEN branch
(`IotaHeadStep.iotaBoolTrue.toStep`), union-typed at `C`.  The redex and the reduct both type in the union. -/
theorem boolElimTrueIotaUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (thenBranch elseBranch resultType : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (resultTypeFormed : HasTypeUnion profile context resultType
      (universeCodeCell resultLevel resultFlag))
    (thenBranchTyped : HasTypeUnion profile context thenBranch resultType)
    (elseBranchTyped : HasTypeUnion profile context elseBranch resultType) :
    HasTypeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeUnion profile context thenBranch resultType :=
  ⟨HasTypeUnion.elim context .gen_boolElim boolElimRule
      (.childCons motive (.childCons boolTrueCell (.childCons thenBranch
        (.childCons elseBranch .childNil))))
      (.childCons boolTrueCell (.childCons boolTrueCell (.childCons resultType .childNil)))
      resultLevel resultLevel resultFlag rfl
      (fun obligation hmem => by
        cases hmem with
        | head =>
          refine HasTypeUnion.intro context .gen_boolTrue boolTrueIntroRule
            .childNil .childNil LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          intro obligation hmem; cases hmem
        | tail _ hmem => cases hmem with
          | head => exact thenBranchTyped
          | tail _ hmem => cases hmem with
            | head => exact elseBranchTyped
            | tail _ hmem => cases hmem with
              | head => exact resultTypeFormed
              | tail _ hmem => cases hmem),
    IotaHeadStep.iotaBoolTrue.toStep,
    thenBranchTyped⟩

/-- **★ The listElim nil-ι selects the nil branch, typed IN THE UNION.**  A union-typed `listElim` on
`nil` ι-steps to the nil branch (`IotaHeadStep.iotaListElimNil.toStep`), the eliminator typed by the union's own
`listElim` arm (scrutinee `nil` union-typed through the native listNil nullary-free-type row), and the
nil branch host-typed. -/
theorem listElimNilIotaUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (nilBranch consBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (elementTypeFormed :
      HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag))
    (resultTypeFormed :
      HasTypeDescPi profile context resultType (universeCodeCell resultLevel resultFlag))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    HasTypeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) resultType ∧
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    HasTypeDescPi profile context nilBranch resultType :=
  ⟨HasTypeUnion.elim context .gen_listElim listElimRule
      (.childCons motive (.childCons listNilCell (.childCons nilBranch
        (.childCons consBranch .childNil))))
      (.childCons elementType (.childCons resultType .childNil))
      resultLevel resultLevel resultFlag rfl
      (fun obligation hmem => by
        cases hmem with
        | head =>
          exact HasTypeUnion.intro context .gen_listNil listNilIntroRule
            .childNil (.childCons elementType .childNil)
            elementLevel elementLevel flag rfl trivial
            (fun obligation hmem => by
              cases hmem with
              | head => exact HasTypeUnion.ofGrown elementTypeFormed
              | tail _ hmem => cases hmem)
        | tail _ hmem => cases hmem with
          | head => exact HasTypeUnion.ofGrown nilBranchTyped
          | tail _ hmem => cases hmem with
            | head => exact HasTypeUnion.ofGrown consBranchTyped
            | tail _ hmem => cases hmem with
              | head => exact HasTypeUnion.ofGrown resultTypeFormed
              | tail _ hmem => cases hmem),
    IotaHeadStep.iotaListElimNil.toStep, nilBranchTyped⟩

/-! ## ★ The NATIVE-36 union-residency coverage gate -/

/-- **The NATIVE-36 union-residency coverage record.**  Each field is a distinct live property of the
new families landed IN the real union: the recursive data-intro tower composes, a non-recursive
eliminator ι reduct types through the match arm, and the listElim nil-ι types through the listElim arm.
An inhabitant certifies the new arms are live (constructed, not just declared). -/
structure NativeFamiliesUnionResidencyCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The numeral `2` types through the recursive `natSucc` intro arm applied twice. -/
  numeralTowerComposesInUnion : HasTypeUnion profile
    (TypingContext.empty : TypingContext profile 0)
    (natSuccCell (natSuccCell natZeroCell)) natTypeCell
  /-- A boolElim ι reduct types through the two-branch match arm. -/
  boolElimIotaInUnion : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch resultType : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
    HasTypeUnion profile context resultType (universeCodeCell resultLevel resultFlag) →
    HasTypeUnion profile context thenBranch resultType →
    HasTypeUnion profile context elseBranch resultType →
    HasTypeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeUnion profile context thenBranch resultType
  /-- The listElim nil-ι types through the listElim arm. -/
  listElimNilIotaInUnion : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (nilBranch consBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
    HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag) →
    HasTypeDescPi profile context resultType (universeCodeCell resultLevel resultFlag) →
    HasTypeDescPi profile context nilBranch resultType →
    HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType) →
    HasTypeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) resultType ∧
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    HasTypeDescPi profile context nilBranch resultType

/-- **★ The NATIVE-36 union-residency gate** — inhabited by the shipped witnesses. -/
theorem nativeFamiliesUnionResidencyWitness {profile : PolyProfile} (flag : UniverseFlag) :
    NativeFamiliesUnionResidencyCoverage profile flag where
  numeralTowerComposesInUnion := numeralTwoTypedThroughUnionRecursiveIntroTwice
  boolElimIotaInUnion := fun context motive thenBranch elseBranch resultType
    resultLevel resultFlag resultTypeFormed thenBranchTyped elseBranchTyped =>
    boolElimTrueIotaUnionTyped context motive thenBranch elseBranch resultType
      resultLevel resultFlag resultTypeFormed thenBranchTyped elseBranchTyped
  listElimNilIotaInUnion := fun context motive nilBranch consBranch elementType resultType
    elementLevel flag resultLevel resultFlag elementTypeFormed resultTypeFormed
    nilBranchTyped consBranchTyped =>
    listElimNilIotaUnionTyped context motive nilBranch consBranch elementType resultType
      elementLevel flag resultLevel resultFlag elementTypeFormed resultTypeFormed
      nilBranchTyped consBranchTyped

end FX1Poly.Typed
