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
`elimRuleOf`); the smart constructors below (`gradedBinderIntro` / `generalElim` / `twoBranchMatchElim`
/ …) are now builders OVER those two arms, not arms themselves.

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
have been inlined as the `formationRule` / `dataIntroNullary` table arms (the three formation families —
base-type / flat / term-indexed — collapsed into the single `formationRule` arm);
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
      (premise : rule.premiseHolds profile context children levels carrier level flag) :
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
      (isElim : bundle.elim generator = some rule)
      (premisesHold : ∀ obligation ∈ rule.obligations scope context args params,
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
    (isElim : elimRuleOf generator = some rule)
    (premisesHold : ∀ obligation ∈ rule.obligations scope context args params,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    HasTypeUnion profile context (rule.memberCell scope args) (rule.outputType scope args params) :=
  HasTypeUnionOver.elim (bundle := fxTypingBundle) context generator rule args params isElim premisesHold

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

/-- `formationRule` at the canonical bundle — the unified formation builder. -/
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
    rule levels carrier level flag isFormationRule premise

/-- `dataIntroNullary` at the canonical bundle. -/
@[reducible] def HasTypeUnion.dataIntroNullary {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (payload : generator.payload scope) (children : RawTermChildren generator.binderShifts scope)
    (rule : DataIntroNullaryRuleDesc) (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
    HasTypeUnion profile context (.mkGen generator payload children) (rule.outputTypeCode scope) := by
  rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
    isTrue | isFalse | isUnit | isInterval0 | isInterval1 | isNatZero
  · -- boolTrue : Bool
    subst isTrue
    obtain rfl : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_boolTrue)
    cases payload; cases children
    refine HasTypeUnion.intro context .gen_boolTrue boolTrueIntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    intro obligation hmem; cases hmem
  · -- boolFalse : Bool
    subst isFalse
    obtain rfl : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_boolFalse)
    cases payload; cases children
    refine HasTypeUnion.intro context .gen_boolFalse boolFalseIntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    intro obligation hmem; cases hmem
  · -- unit : Unit
    subst isUnit
    obtain rfl : rule = { outputTypeCode := fun _ => unitTypeCell } :=
      Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_unit)
    cases payload; cases children
    refine HasTypeUnion.intro context .gen_unit unitIntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    intro obligation hmem; cases hmem
  · -- interval0 : Interval
    subst isInterval0
    obtain rfl : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_interval0)
    cases payload; cases children
    refine HasTypeUnion.intro context .gen_interval0 interval0IntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    intro obligation hmem; cases hmem
  · -- interval1 : Interval
    subst isInterval1
    obtain rfl : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_interval1)
    cases payload; cases children
    refine HasTypeUnion.intro context .gen_interval1 interval1IntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    intro obligation hmem; cases hmem
  · -- natZero : Nat
    subst isNatZero
    obtain rfl : rule = { outputTypeCode := fun _ => natTypeCell } :=
      Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_natZero)
    cases payload; cases children
    refine HasTypeUnion.intro context .gen_natZero natZeroIntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    intro obligation hmem; cases hmem

/-- `gradedBinderIntro` at the canonical bundle. -/
@[reducible] def HasTypeUnion.gradedBinderIntro {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : GradedIntroRule)
    (typeParamA : RawTerm scope) (typeParamB : RawTerm (scope + 1)) (body : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (isIntro : gradedIntroRuleOf generator = some rule)
    (binderGraded : gradedBinderChecks rule.binderUsage body)
    (domainFormed : rule.demandsDomainFormation = true →
      HasTypeUnion profile context (rule.domainCell scope typeParamA)
        (universeCodeCell domainLevel flag))
    (classifierFormed : rule.demandsClassifierFormation = true →
      HasTypeUnion profile (context.cons (rule.domainCell scope typeParamA))
        (rule.bodyClassifier scope typeParamA typeParamB) (universeCodeCell codomainLevel flag))
    (bodyTyped : HasTypeUnion profile (context.cons (rule.domainCell scope typeParamA))
      body (rule.bodyClassifier scope typeParamA typeParamB)) :
    HasTypeUnion profile context (rule.memberCell scope typeParamA body)
      (rule.outputType scope typeParamA typeParamB body) := by
  rcases gradedIntroRuleOf_isLamOrPathLam isIntro with isLam | isPathLam
  · -- λ: domain + codomain formation premises, body typed under the domain, unrestricted grade.
    subst isLam
    obtain rfl : rule = lamGradedIntroRule :=
      Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
    refine HasTypeUnion.intro context .gen_lam lamIntroRule
      (.childCons typeParamA (.childCons body .childNil)) (.childCons typeParamB .childNil)
      domainLevel codomainLevel flag rfl binderGraded ?_
    intro obligation hmem
    cases hmem with
    | head => exact domainFormed rfl
    | tail _ hmem => cases hmem with
      | head => exact classifierFormed rfl
      | tail _ hmem => cases hmem with
        | head => exact bodyTyped
        | tail _ hmem => cases hmem
  · -- pathLam: no formation premises, body typed under the interval, affine grade.
    subst isPathLam
    obtain rfl : rule = pathLamGradedIntroRule :=
      Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
    refine HasTypeUnion.intro context .gen_pathLam pathLamIntroRule
      (.childCons body .childNil) (.childCons typeParamA .childNil)
      domainLevel codomainLevel flag rfl binderGraded ?_
    intro obligation hmem
    cases hmem with
    | head => exact bodyTyped
    | tail _ hmem => cases hmem

/-- `generalElim` at the canonical bundle. -/
@[reducible] def HasTypeUnion.generalElim {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : GeneralElimRule)
    (typeParamA : RawTerm scope) (typeParamB : RawTerm (scope + 1)) (typeParamC typeParamD : RawTerm scope)
    (eliminated argument : RawTerm scope) (isElim : generalElimRuleOf generator = some rule)
    (eliminatedTyped : HasTypeUnion profile context eliminated
      (rule.eliminatedType scope typeParamA typeParamB typeParamC typeParamD))
    (argumentTyped : HasTypeUnion profile context argument (rule.argumentType scope typeParamA)) :
    HasTypeUnion profile context (rule.memberCell scope eliminated argument)
      (rule.outputType scope typeParamA typeParamB argument) :=
  by
  by_cases isApp : generator = .gen_app
  · subst isApp
    obtain rfl : rule = appGeneralElimRule := by
      rw [generalElimRuleOf_app] at isElim; exact (Option.some.inj isElim).symm
    refine HasTypeUnion.elim context .gen_app appElimRule
      (.childCons eliminated (.childCons argument .childNil))
      (.childCons typeParamA (.childCons typeParamB .childNil)) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact eliminatedTyped
    | tail _ hmem => cases hmem with
      | head => exact argumentTyped
      | tail _ hmem => cases hmem
  · obtain rfl : generator = .gen_pathApp := by
      rcases generalElimRuleOf_isAppOrPathApp isElim with hgen | hgen
      · exact absurd hgen isApp
      · exact hgen
    obtain rfl : rule = pathAppGeneralElimRule := by
      rw [generalElimRuleOf_pathApp] at isElim; exact (Option.some.inj isElim).symm
    refine HasTypeUnion.elim context .gen_pathApp pathAppElimRule
      (.childCons eliminated (.childCons argument .childNil))
      (.childCons typeParamA (.childCons typeParamC (.childCons typeParamD .childNil))) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact eliminatedTyped
    | tail _ hmem => cases hmem with
      | head => exact argumentTyped
      | tail _ hmem => cases hmem

/-- `recursiveElim` at the canonical bundle. -/
@[reducible] def HasTypeUnion.recursiveElim {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : NativeRecursiveElimRule)
    (motive : RawTerm (scope + 1)) (baseBranch : RawTerm scope) (stepBranch : RawTerm (scope + 2))
    (scrutinee : RawTerm scope) (resultType : RawTerm scope)
    (isRecursiveElim : nativeRecursiveElimRuleOf generator = some rule)
    (scrutineeTyped : HasTypeUnion profile context scrutinee (rule.scrutineeType scope))
    (baseBranchTyped : HasTypeUnion profile context baseBranch resultType)
    (stepBranchTyped : HasTypeUnion profile
      ((context.cons (rule.scrutineeType scope)).cons
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken resultType))
      stepBranch
      (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken resultType))) :
    HasTypeUnion profile context
      (rule.memberCell scope motive baseBranch stepBranch scrutinee) resultType :=
  by
  by_cases isNatElim : generator = .gen_natElim
  · subst isNatElim
    obtain rfl : rule = natElimNativeRecursiveRule := by
      rw [nativeRecursiveElimRuleOf_natElim] at isRecursiveElim
      exact (Option.some.inj isRecursiveElim).symm
    refine HasTypeUnion.elim context .gen_natElim natElimRule
      (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
      (.childCons resultType .childNil) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact scrutineeTyped
    | tail _ hmem => cases hmem with
      | head => exact baseBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact stepBranchTyped
        | tail _ hmem => cases hmem
  · by_cases isNatRec : generator = .gen_natRec
    · subst isNatRec
      obtain rfl : rule = natRecNativeRecursiveRule := by
        rw [nativeRecursiveElimRuleOf_natRec] at isRecursiveElim
        exact (Option.some.inj isRecursiveElim).symm
      refine HasTypeUnion.elim context .gen_natRec natRecElimRule
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
        (.childCons resultType .childNil) rfl ?_
      intro obligation hmem
      cases hmem with
      | head => exact scrutineeTyped
      | tail _ hmem => cases hmem with
        | head => exact baseBranchTyped
        | tail _ hmem => cases hmem with
          | head => exact stepBranchTyped
          | tail _ hmem => cases hmem
    · exfalso
      unfold nativeRecursiveElimRuleOf at isRecursiveElim
      rw [if_neg isNatElim, if_neg isNatRec] at isRecursiveElim
      exact absurd isRecursiveElim (by intro hit; cases hit)

/-- `twoBranchMatchElim` at the canonical bundle. -/
@[reducible] def HasTypeUnion.twoBranchMatchElim {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (rule : NativeTwoBranchMatchElimRule) (motive : RawTerm (scope + 1))
    (firstBranch secondBranch scrutinee : RawTerm scope)
    (typeParamA typeParamB resultType : RawTerm scope)
    (isTwoBranchMatch : nativeTwoBranchMatchRuleOf generator = some rule)
    (scrutineeTyped : HasTypeUnion profile context scrutinee
      (rule.scrutineeType scope typeParamA typeParamB))
    (firstBranchTyped : HasTypeUnion profile context firstBranch
      (rule.firstBranchType scope typeParamA typeParamB resultType))
    (secondBranchTyped : HasTypeUnion profile context secondBranch
      (rule.secondBranchType scope typeParamA typeParamB resultType)) :
    HasTypeUnion profile context
      (rule.memberCell scope motive firstBranch secondBranch scrutinee) resultType :=
  by
  rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine HasTypeUnion.elim context .gen_boolElim boolElimRule
      (.childCons motive (.childCons scrutinee (.childCons firstBranch (.childCons secondBranch .childNil))))
      (.childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil))) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact scrutineeTyped
    | tail _ hmem => cases hmem with
      | head => exact firstBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact secondBranchTyped
        | tail _ hmem => cases hmem
  · refine HasTypeUnion.elim context .gen_optionMatch optionMatchElimRule
      (.childCons motive (.childCons firstBranch (.childCons secondBranch (.childCons scrutinee .childNil))))
      (.childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil))) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact scrutineeTyped
    | tail _ hmem => cases hmem with
      | head => exact firstBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact secondBranchTyped
        | tail _ hmem => cases hmem
  · refine HasTypeUnion.elim context .gen_eitherMatch eitherMatchElimRule
      (.childCons motive (.childCons firstBranch (.childCons secondBranch (.childCons scrutinee .childNil))))
      (.childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil))) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact scrutineeTyped
    | tail _ hmem => cases hmem with
      | head => exact firstBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact secondBranchTyped
        | tail _ hmem => cases hmem

/-- `pathInductionElim` at the canonical bundle. -/
@[reducible] def HasTypeUnion.pathInductionElim {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (rule : NativePathInductionElimRule) (motive : RawTerm (scope + 2))
    (baseCase witness : RawTerm scope) (typeCode endpoint resultType : RawTerm scope)
    (isPathInduction : nativePathInductionRuleOf generator = some rule)
    (witnessTyped : HasTypeUnion profile context witness (rule.witnessType scope typeCode endpoint))
    (baseCaseTyped : HasTypeUnion profile context baseCase resultType) :
    HasTypeUnion profile context (rule.memberCell scope motive baseCase witness) resultType :=
  by
  obtain ⟨rfl, rfl⟩ := nativePathInductionRuleOf_cases isPathInduction
  refine HasTypeUnion.elim context .gen_idJ idJElimRule
    (.childCons motive (.childCons baseCase (.childCons witness .childNil)))
    (.childCons typeCode (.childCons endpoint (.childCons resultType .childNil))) rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact witnessTyped
  | tail _ hmem => cases hmem with
    | head => exact baseCaseTyped
    | tail _ hmem => cases hmem

/-- `projectionElim` at the canonical bundle. -/
@[reducible] def HasTypeUnion.projectionElim {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : NativeProjectionElimRule)
    (pairTerm firstType secondType : RawTerm scope)
    (isProjection : nativeProjectionRuleOf generator = some rule)
    (pairTyped : HasTypeUnion profile context pairTerm (productTypeCell firstType secondType)) :
    HasTypeUnion profile context (rule.memberCell scope pairTerm)
      (rule.projectedType scope firstType secondType) :=
  by
  rcases nativeProjectionRuleOf_cases isProjection with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine HasTypeUnion.elim context .gen_fst fstElimRule
      (.childCons pairTerm .childNil)
      (.childCons firstType (.childCons secondType .childNil)) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact pairTyped
    | tail _ hmem => cases hmem
  · refine HasTypeUnion.elim context .gen_snd sndElimRule
      (.childCons pairTerm .childNil)
      (.childCons firstType (.childCons secondType .childNil)) rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact pairTyped
    | tail _ hmem => cases hmem

/-- `recursiveDataIntro` at the canonical bundle — the unified recursive data-intro builder. -/
@[reducible] def HasTypeUnion.recursiveDataIntro {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (spec : RecursiveDataIntroSpec)
    (head recursiveChild elementType : RawTerm scope)
    (isRecursiveDataIntro : recursiveDataIntroSpecOf generator = some spec)
    (headTyped : spec.hasGrownHead = true → HasTypeDescPi profile context head elementType)
    (recursiveChildTyped : HasTypeUnion profile context recursiveChild
      (spec.recursiveChildType scope elementType)) :
    HasTypeUnion profile context
      (spec.memberCell scope head recursiveChild) (spec.outputType scope elementType) :=
  by
  rcases recursiveDataIntroSpecOf_cases isRecursiveDataIntro with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine HasTypeUnion.intro context .gen_natSucc natSuccIntroRule
      (.childCons recursiveChild .childNil) .childNil LevelExpr.lzero LevelExpr.lzero
      UniverseFlag.standard rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact recursiveChildTyped
    | tail _ hmem => cases hmem
  · refine HasTypeUnion.intro context .gen_listCons listConsIntroRule
      (.childCons head (.childCons recursiveChild .childNil)) (.childCons elementType .childNil)
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (headTyped rfl)
    | tail _ hmem => cases hmem with
      | head => exact recursiveChildTyped
      | tail _ hmem => cases hmem

/-- **Backward-compat smart constructor: `natSucc`-style recursive-unary intro.**  The pre-collapse
`recursiveUnaryIntro` call convention, now building the unified `recursiveDataIntro` arm with the
`natSucc` spec — so every build site (the numeral smoke, the spike conversions) is unchanged.  The
`natSucc` row has no grown head, so the phantom head/element-type are filled with `child`. -/
@[reducible] def HasTypeUnion.recursiveUnaryIntro {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (rule : NativeRecursiveUnaryDataIntroRule) (child : RawTerm scope)
    (isRecursiveUnary : nativeRecursiveUnaryDataIntroRuleOf generator = some rule)
    (childTyped : HasTypeUnion profile context child (rule.childType scope)) :
    HasTypeUnion profile context (rule.memberCell scope child) (rule.outputType scope) := by
  obtain ⟨generatorEq, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
  subst generatorEq; subst ruleEq
  exact HasTypeUnion.recursiveDataIntro context .gen_natSucc natSuccRecursiveDataIntroSpec
    child child child rfl (fun gateHolds => Bool.noConfusion gateHolds) childTyped

/-- `grownDataIntro` at the canonical bundle — the unified grown data-intro builder. -/
@[reducible] def HasTypeUnion.grownDataIntro {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (spec : GrownDataIntroSpec)
    (child0 child1 typeParam0 typeParam1 : RawTerm scope)
    (formednessLevel : LevelExpr) (formednessFlag : UniverseFlag)
    (isGrownDataIntro : grownDataIntroSpecOf generator = some spec)
    (child0Typed : spec.hasChild0 = true →
      HasTypeDescPi profile context child0 (spec.child0Type scope typeParam0 typeParam1))
    (child1Typed : spec.hasChild1 = true →
      HasTypeDescPi profile context child1 (spec.child1Type scope typeParam0 typeParam1))
    (formednessTyped : spec.hasFormedness = true →
      HasTypeDescPi profile context (spec.formednessTarget scope typeParam0 typeParam1)
        (universeCodeCell formednessLevel formednessFlag)) :
    HasTypeUnion profile context (spec.memberCell scope child0 child1)
      (spec.outputType scope child0 child1 typeParam0 typeParam1) := by
  rcases grownDataIntroSpecOf_cases isGrownDataIntro with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- optionSome: one grown value child at typeParam0.
    refine HasTypeUnion.intro context .gen_optionSome optionSomeIntroRule
      (.childCons child0 .childNil) (.childCons typeParam0 .childNil)
      formednessLevel formednessLevel formednessFlag rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (child0Typed rfl)
    | tail _ hmem => cases hmem
  · -- optionNone: a grown-formedness premise on the free typeParam0.
    refine HasTypeUnion.intro context .gen_optionNone optionNoneIntroRule
      .childNil (.childCons typeParam0 .childNil)
      formednessLevel formednessLevel formednessFlag rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (formednessTyped rfl)
    | tail _ hmem => cases hmem
  · -- listNil: the optionNone twin with the list container.
    refine HasTypeUnion.intro context .gen_listNil listNilIntroRule
      .childNil (.childCons typeParam0 .childNil)
      formednessLevel formednessLevel formednessFlag rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (formednessTyped rfl)
    | tail _ hmem => cases hmem
  · -- eitherInl: a grown value at typeParam0 + a formedness premise on the free typeParam1.
    refine HasTypeUnion.intro context .gen_eitherInl eitherInlIntroRule
      (.childCons child0 .childNil) (.childCons typeParam0 (.childCons typeParam1 .childNil))
      formednessLevel formednessLevel formednessFlag rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (child0Typed rfl)
    | tail _ hmem => cases hmem with
      | head => exact HasTypeUnion.ofGrown (formednessTyped rfl)
      | tail _ hmem => cases hmem
  · -- eitherInr: a grown value at typeParam0 + a formedness premise on the free typeParam1.
    refine HasTypeUnion.intro context .gen_eitherInr eitherInrIntroRule
      (.childCons child0 .childNil) (.childCons typeParam0 (.childCons typeParam1 .childNil))
      formednessLevel formednessLevel formednessFlag rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (child0Typed rfl)
    | tail _ hmem => cases hmem with
      | head => exact HasTypeUnion.ofGrown (formednessTyped rfl)
      | tail _ hmem => cases hmem
  · -- pair: two grown children at the two independent type params.
    refine HasTypeUnion.intro context .gen_pair pairIntroRule
      (.childCons child0 (.childCons child1 .childNil))
      (.childCons typeParam0 (.childCons typeParam1 .childNil))
      formednessLevel formednessLevel formednessFlag rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (child0Typed rfl)
    | tail _ hmem => cases hmem with
      | head => exact HasTypeUnion.ofGrown (child1Typed rfl)
      | tail _ hmem => cases hmem
  · -- refl: a grown witness at typeParam0, output reads the witness.
    refine HasTypeUnion.intro context .gen_refl reflIntroRule
      (.childCons child0 .childNil) (.childCons typeParam0 .childNil)
      formednessLevel formednessLevel formednessFlag rfl trivial ?_
    intro obligation hmem
    cases hmem with
    | head => exact HasTypeUnion.ofGrown (child0Typed rfl)
    | tail _ hmem => cases hmem

/-- **Backward-compat smart constructor: `optionNone` / `listNil`-style nullary-free-type intro.** -/
@[reducible] def HasTypeUnion.nullaryFreeTypeIntro {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (rule : NativeNullaryFreeTypeDataIntroRule) (elementType : RawTerm scope) (elementLevel : LevelExpr)
    (flag : UniverseFlag) (isNullaryFreeType : nativeNullaryFreeTypeDataIntroRuleOf generator = some rule)
    (elementTypeFormed : HasTypeDescPi profile context elementType
      (universeCodeCell elementLevel flag)) :
    HasTypeUnion profile context (rule.memberCell scope) (rule.outputType scope elementType) := by
  rcases nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType with
      ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩
  · subst generatorEq; subst ruleEq
    exact HasTypeUnion.grownDataIntro context .gen_optionNone optionNoneGrownSpec elementType
      elementType elementType elementType elementLevel flag rfl
      (fun gateHolds => Bool.noConfusion gateHolds) (fun gateHolds => Bool.noConfusion gateHolds)
      (fun _ => elementTypeFormed)
  · subst generatorEq; subst ruleEq
    exact HasTypeUnion.grownDataIntro context .gen_listNil listNilGrownSpec elementType
      elementType elementType elementType elementLevel flag rfl
      (fun gateHolds => Bool.noConfusion gateHolds) (fun gateHolds => Bool.noConfusion gateHolds)
      (fun _ => elementTypeFormed)

/-- **Backward-compat smart constructor: `refl`-style reflexive intro.** -/
@[reducible] def HasTypeUnion.reflexiveIntro {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : NativeReflexiveDataIntroRule)
    (witness witnessType : RawTerm scope)
    (isReflexive : nativeReflexiveDataIntroRuleOf generator = some rule)
    (witnessTyped : HasTypeDescPi profile context witness witnessType) :
    HasTypeUnion profile context (rule.memberCell scope witness)
      (rule.outputType scope witnessType witness) := by
  obtain ⟨generatorEq, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
  subst generatorEq; subst ruleEq
  exact HasTypeUnion.grownDataIntro context .gen_refl reflGrownSpec witness witness
    witnessType witnessType LevelExpr.lzero UniverseFlag.standard rfl
    (fun _ => witnessTyped) (fun gateHolds => Bool.noConfusion gateHolds)
    (fun gateHolds => Bool.noConfusion gateHolds)

/-- `listElim` at the canonical bundle. -/
@[reducible] def HasTypeUnion.listElim {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : NativeListElimRule)
    (motive : RawTerm (scope + 1)) (scrutinee nilBranch consBranch elementType resultType : RawTerm scope)
    (isListElim : listElimNativeRuleOf generator = some rule)
    (scrutineeTyped : HasTypeUnion profile context scrutinee (listTypeCell elementType))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    HasTypeUnion profile context
      (rule.memberCell scope motive scrutinee nilBranch consBranch) resultType :=
  by
  obtain ⟨rfl, rfl⟩ := listElimNativeRuleOf_cases isListElim
  refine HasTypeUnion.elim context .gen_listElim listElimRule
    (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))))
    (.childCons elementType (.childCons resultType .childNil)) rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact HasTypeUnion.ofGrown nilBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact HasTypeUnion.ofGrown consBranchTyped
      | tail _ hmem => cases hmem

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

/-! ## ★ The wall-falls smokes — typable for the FIRST time -/

/-- **★ The WHOLE endpoint redex in ONE derivation.**  `pathApp(pathLam(Type@0), 0) : Type@1` — the
path through the graded intro arm, the endpoint argument through the data embedding, composed by the
recursive elim arm.  No prior judgment contained both premises. -/
theorem endpointRedexNativelyTypedWhole {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeUnion.generalElim TypingContext.empty .gen_pathApp pathAppGeneralElimRule
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (RawTerm.weaken (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell rfl
    (HasTypeUnion.gradedBinderIntro TypingContext.empty .gen_pathLam pathLamGradedIntroRule
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (RawTerm.weaken (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
      (universeCodeCell LevelExpr.lzero flag)
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl (Nat.zero_le 1)
      (fun gateHolds => Bool.noConfusion gateHolds)
      (fun gateHolds => Bool.noConfusion gateHolds)
      (HasTypeUnion.ofGrown
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation
            (TypingContext.empty.cons intervalTypeCell) LevelExpr.lzero flag))))
    (HasTypeUnion.dataIntroNullary TypingContext.empty .gen_interval0 () .childNil
      { outputTypeCode := fun _ => intervalTypeCell } rfl)

/-- **★ The λ-over-data wall falls.**  `λ(x:Bool).0 : Π(x:Bool).Interval` — a λ whose BODY (`0`) is
typed by the DATA embedding, with the domain/classifier formation premises through the base-type
embedding.  Untypable in every prior engine: the host `piIntro` demands a host-typed body and the
interval endpoint is not host-typable (`intervalZeroGrownUntypable`, the NATIVE-08 wall). -/
theorem constantIntervalLambdaNativelyTyped {profile : PolyProfile} :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (lamCell boolTypeCell intervalZeroCell)
      (piTyCodeCell boolTypeCell intervalTypeCell) :=
  HasTypeUnion.gradedBinderIntro TypingContext.empty .gen_lam lamGradedIntroRule
    boolTypeCell intervalTypeCell intervalZeroCell
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial
    (fun _ => HasTypeUnion.formationRule TypingContext.empty .gen_boolCode () .childNil
      (.baseType { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard })
      [] intervalTypeCell LevelExpr.lzero UniverseFlag.standard rfl trivial)
    (fun _ => HasTypeUnion.formationRule (TypingContext.empty.cons boolTypeCell)
      .gen_intervalCode () .childNil
      (.baseType { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard })
      [] intervalTypeCell LevelExpr.lzero UniverseFlag.standard rfl trivial)
    (HasTypeUnion.dataIntroNullary (TypingContext.empty.cons boolTypeCell)
      .gen_interval0 () .childNil { outputTypeCode := fun _ => intervalTypeCell } rfl)

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
  HasTypeUnion.recursiveUnaryIntro TypingContext.empty .gen_natSucc
    natSuccNativeRecursiveUnaryRule (natSuccCell natZeroCell) rfl
    (HasTypeUnion.recursiveUnaryIntro TypingContext.empty .gen_natSucc
      natSuccNativeRecursiveUnaryRule natZeroCell rfl
      (HasTypeUnion.dataIntroNullary TypingContext.empty .gen_natZero () .childNil
        { outputTypeCode := fun _ => natTypeCell } rfl))

/-- **★ One boolElim ι reduct types IN THE UNION through the two-branch match arm.**  A union-typed
`boolElim` on `boolTrue` (both branches union-typed at the result `C`) ι-reduces to the THEN branch
(`IotaHeadStep.iotaBoolTrue.toStep`), union-typed at `C`.  The redex and the reduct both type in the union. -/
theorem boolElimTrueIotaUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (thenBranch elseBranch resultType : RawTerm scope)
    (thenBranchTyped : HasTypeUnion profile context thenBranch resultType)
    (elseBranchTyped : HasTypeUnion profile context elseBranch resultType) :
    HasTypeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeUnion profile context thenBranch resultType :=
  ⟨HasTypeUnion.twoBranchMatchElim context .gen_boolElim boolElimNativeMatchRule
      motive thenBranch elseBranch boolTrueCell boolTrueCell boolTrueCell resultType rfl
      (HasTypeUnion.dataIntroNullary context .gen_boolTrue () .childNil
        { outputTypeCode := fun _ => boolTypeCell } rfl)
      thenBranchTyped elseBranchTyped,
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
    (elementTypeFormed :
      HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    HasTypeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) resultType ∧
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    HasTypeDescPi profile context nilBranch resultType :=
  ⟨HasTypeUnion.listElim context .gen_listElim listElimNativeRule
      motive listNilCell nilBranch consBranch elementType resultType rfl
      (HasTypeUnion.nullaryFreeTypeIntro context .gen_listNil
        listNilNativeNullaryFreeTypeRule elementType elementLevel flag rfl elementTypeFormed)
      nilBranchTyped consBranchTyped,
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
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch resultType : RawTerm scope),
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
    (elementLevel : LevelExpr) (flag : UniverseFlag),
    HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag) →
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
    thenBranchTyped elseBranchTyped =>
    boolElimTrueIotaUnionTyped context motive thenBranch elseBranch resultType
      thenBranchTyped elseBranchTyped
  listElimNilIotaInUnion := fun context motive nilBranch consBranch elementType resultType
    elementLevel flag elementTypeFormed nilBranchTyped consBranchTyped =>
    listElimNilIotaUnionTyped context motive nilBranch consBranch elementType resultType
      elementLevel flag elementTypeFormed nilBranchTyped consBranchTyped

end FX1Poly.Typed
