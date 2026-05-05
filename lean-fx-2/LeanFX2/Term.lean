import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.Context

/-! # Term — Layer 1 raw-aware typed term inductive.

The kernel's load-bearing inductive.  Every Term value carries its
raw form as a **type-level index**:

```lean
Term : ∀ {mode level scope}, Ctx mode level scope → Ty level scope → RawTerm scope → Type
```

Each constructor pins the raw form structurally, so `Term.toRaw t = raw`
is `rfl` (the projection IS the index — see `Term/ToRaw.lean`).

## Mode placement

Per CLAUDE.md commitment + README "mode-place reasoning" (Option B):
mode lives on Ctx; Term inherits it via `{context : Ctx mode level scope}`.
Each ctor names `{mode : Mode} {level scope : Nat} {context : Ctx mode level scope}`
in implicits — Lean infers all four from context's type at use sites.

## Subst-typed result indices

Three ctors have result types involving `Ty.subst0` (joint Ty + raw
substitution):

* `appPi` — codomain substituted with argument: `cod.subst0 dom argRaw`
* `pair` — second component's type substituted with first: `second.subst0 first firstRaw`
* `snd` — second component returned with first-projection substituted:
  `second.subst0 first (RawTerm.fst pairRaw)`

These intentionally use `Ty.subst0`'s unified flavor (which embeds
`RawTermSubst.singleton argRaw`, NOT `dropNewest`).  This is what
makes the typed↔raw bridge `rfl`-driven for refl-bearing β-redexes
later in Layer 4.

## Constructor list (29 total)

Foundational + dependent + Identity + Modal:
* `var, unit` — base
* `lam, app` — non-dep arrow
* `lamPi, appPi` — dep Π
* `pair, fst, snd` — Σ
* `boolTrue, boolFalse, boolElim`
* `natZero, natSucc, natElim, natRec`
* `listNil, listCons, listElim`
* `optionNone, optionSome, optionMatch`
* `eitherInl, eitherInr, eitherMatch`
* `refl, idJ` — Identity
* `modIntro, modElim, subsume` — Modal (Layer 6 references; ship raw-side from day 1)

## D1.9 typed Term ctors — per-need addition

The 27 raw ctors added in D1.6 (cubical/HOTT/refine/record/codata/session/
effect/strict) deliberately do NOT land as one bulk typed-Term refactor.
They are mirrored at the typed layer only when a specific reduction rule
needs them.  The first such mirror is the typed cubical path fragment:
`interval0`, `interval1`, `pathLam`, and `pathApp`.

A bulk addition of 27 typed ctors would cascade ~6000 lines of mechanical
extensions through Term/{Rename,Subst,Pointwise,HEqCongr,Inversion,
SubjectReduction,Bridge}, and Algo/{Check,Infer,WHNF}.  Each Term.subst
match grows past simp's heartbeat budget at ~30+ arms.  Better strategy:
add typed ctors one-at-a-time as specific reduction rules need them,
co-located with their Step.* introduction.

This matches the "scaffold at raw, lift to typed only when needed"
discipline that the existing modIntro/modElim/subsume ctors illustrate
— typed scaffolding without semantic content was added preemptively
and now sits unused.

## DecidableEq deferred

Manual instance lands when needed.  For Phase 1.C, just shipping the
inductive zero-axiom is the critical milestone.
-/

namespace LeanFX2

/-- Raw-aware typed term.  Each ctor's signature pins the raw form
structurally; `Term.toRaw t = raw` is `rfl`. -/
inductive Term : ∀ {mode : Mode} {level scope : Nat},
    Ctx mode level scope → Ty level scope → RawTerm scope → Type
  -- Variable lookup
  | var {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (position : Fin scope) :
      Term context (varType context position) (RawTerm.var position)
  -- Unit
  | unit {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      Term context Ty.unit RawTerm.unit
  -- Non-dep arrow intro/elim
  | lam {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {bodyRaw : RawTerm (scope + 1)}
      (body : Term (Ctx.cons context domainType) codomainType.weaken bodyRaw) :
      Term context (Ty.arrow domainType codomainType) (RawTerm.lam bodyRaw)
  | app {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {functionRaw argumentRaw : RawTerm scope}
      (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
      (argumentTerm : Term context domainType argumentRaw) :
      Term context codomainType (RawTerm.app functionRaw argumentRaw)
  -- Dep Π intro/elim
  | lamPi {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {bodyRaw : RawTerm (scope + 1)}
      (body : Term (Ctx.cons context domainType) codomainType bodyRaw) :
      Term context (Ty.piTy domainType codomainType) (RawTerm.lam bodyRaw)
  | appPi {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {functionRaw argumentRaw : RawTerm scope}
      (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
      (argumentTerm : Term context domainType argumentRaw) :
      Term context (codomainType.subst0 domainType argumentRaw)
                   (RawTerm.app functionRaw argumentRaw)
  -- Σ intro/elim
  | pair {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRaw secondRaw : RawTerm scope}
      (firstValue : Term context firstType firstRaw)
      (secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw) :
      Term context (Ty.sigmaTy firstType secondType)
                   (RawTerm.pair firstRaw secondRaw)
  | fst {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRaw : RawTerm scope}
      (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
      Term context firstType (RawTerm.fst pairRaw)
  | snd {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRaw : RawTerm scope}
      (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
      Term context (secondType.subst0 firstType (RawTerm.fst pairRaw))
                   (RawTerm.snd pairRaw)
  -- Booleans
  | boolTrue {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      Term context Ty.bool RawTerm.boolTrue
  | boolFalse {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      Term context Ty.bool RawTerm.boolFalse
  | boolElim {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw thenRaw elseRaw : RawTerm scope}
      (scrutinee : Term context Ty.bool scrutineeRaw)
      (thenBranch : Term context motiveType thenRaw)
      (elseBranch : Term context motiveType elseRaw) :
      Term context motiveType (RawTerm.boolElim scrutineeRaw thenRaw elseRaw)
  -- Naturals
  | natZero {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      Term context Ty.nat RawTerm.natZero
  | natSucc {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {predecessorRaw : RawTerm scope}
      (predecessor : Term context Ty.nat predecessorRaw) :
      Term context Ty.nat (RawTerm.natSucc predecessorRaw)
  | natElim {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRaw succRaw : RawTerm scope}
      (scrutinee : Term context Ty.nat scrutineeRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
      Term context motiveType (RawTerm.natElim scrutineeRaw zeroRaw succRaw)
  | natRec {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRaw succRaw : RawTerm scope}
      (scrutinee : Term context Ty.nat scrutineeRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch : Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
      Term context motiveType (RawTerm.natRec scrutineeRaw zeroRaw succRaw)
  -- Lists
  | listNil {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      Term context (Ty.listType elementType) RawTerm.listNil
  | listCons {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {headRaw tailRaw : RawTerm scope}
      (headTerm : Term context elementType headRaw)
      (tailTerm : Term context (Ty.listType elementType) tailRaw) :
      Term context (Ty.listType elementType) (RawTerm.listCons headRaw tailRaw)
  | listElim {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw nilRaw consRaw : RawTerm scope}
      (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
      (nilBranch : Term context motiveType nilRaw)
      (consBranch : Term context (Ty.arrow elementType
                                    (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
      Term context motiveType (RawTerm.listElim scrutineeRaw nilRaw consRaw)
  -- Options
  | optionNone {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      Term context (Ty.optionType elementType) RawTerm.optionNone
  | optionSome {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {valueRaw : RawTerm scope}
      (valueTerm : Term context elementType valueRaw) :
      Term context (Ty.optionType elementType) (RawTerm.optionSome valueRaw)
  | optionMatch {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw noneRaw someRaw : RawTerm scope}
      (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
      (noneBranch : Term context motiveType noneRaw)
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
      Term context motiveType (RawTerm.optionMatch scrutineeRaw noneRaw someRaw)
  -- Eithers
  | eitherInl {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueRaw : RawTerm scope}
      (valueTerm : Term context leftType valueRaw) :
      Term context (Ty.eitherType leftType rightType) (RawTerm.eitherInl valueRaw)
  | eitherInr {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueRaw : RawTerm scope}
      (valueTerm : Term context rightType valueRaw) :
      Term context (Ty.eitherType leftType rightType) (RawTerm.eitherInr valueRaw)
  | eitherMatch {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineeRaw leftRaw rightRaw : RawTerm scope}
      (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
      (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
      (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
      Term context motiveType (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw)
  -- Identity types
  | refl {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      Term context (Ty.id carrier rawWitness rawWitness) (RawTerm.refl rawWitness)
  | idJ {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRaw witnessRaw : RawTerm scope}
      (baseCase : Term context motiveType baseRaw)
      (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
      Term context motiveType (RawTerm.idJ baseRaw witnessRaw)
  -- Strict identity mirrors identity at the typed layer but lives in
  -- `Ty.idStrict`, keeping definitional identity separate from HoTT `Ty.id`.
  | idStrictRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      Term context
        (Ty.idStrict carrier rawWitness rawWitness)
        (RawTerm.idStrictRefl rawWitness)
  | idStrictRec {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRaw witnessRaw : RawTerm scope}
      (baseCase : Term context motiveType baseRaw)
      (witness :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw) :
      Term context motiveType (RawTerm.idStrictRec baseRaw witnessRaw)
  -- Modal — Layer 1 ships RAW-SIDE SCAFFOLDING ONLY.  In Phase 1,
  -- innerType is preserved (no Ty.modal applied) because Ty.modal +
  -- Modality 1-cells are Layer 6 work.  When Layer 6 lands, these
  -- three ctor signatures will be refactored to take a Modality and
  -- produce `Ty.modal modality innerType`.  Localized backward-incompat
  -- change (3 ctor signatures); other Term ctors unaffected.
  | modIntro {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {innerType : Ty level scope} {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw) :
      Term context innerType (RawTerm.modIntro innerRaw)
  | modElim {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {innerType : Ty level scope} {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw) :
      Term context innerType (RawTerm.modElim innerRaw)
  | subsume {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {innerType : Ty level scope} {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw) :
      Term context innerType (RawTerm.subsume innerRaw)
  -- Cubical path fragment — typed mirror of the raw D2.5 path β rule.
  | interval0 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      Term context Ty.interval RawTerm.interval0
  | interval1 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      Term context Ty.interval RawTerm.interval1
  | intervalOpp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerRaw : RawTerm scope}
      (innerValue : Term context Ty.interval innerRaw) :
      Term context Ty.interval (RawTerm.intervalOpp innerRaw)
  | intervalMeet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftRaw rightRaw : RawTerm scope}
      (leftValue : Term context Ty.interval leftRaw)
      (rightValue : Term context Ty.interval rightRaw) :
      Term context Ty.interval (RawTerm.intervalMeet leftRaw rightRaw)
  | intervalJoin {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftRaw rightRaw : RawTerm scope}
      (leftValue : Term context Ty.interval leftRaw)
      (rightValue : Term context Ty.interval rightRaw) :
      Term context Ty.interval (RawTerm.intervalJoin leftRaw rightRaw)
  | pathLam {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrierType : Ty level scope)
      (leftEndpoint rightEndpoint : RawTerm scope)
      {bodyRaw : RawTerm (scope + 1)}
      (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw) :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        (RawTerm.pathLam bodyRaw)
  | pathApp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {pathRaw intervalRaw : RawTerm scope}
      (pathTerm : Term context
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
      (intervalTerm : Term context Ty.interval intervalRaw) :
      Term context carrierType (RawTerm.pathApp pathRaw intervalRaw)
  -- Cubical Glue fragment — typed mirror of the raw D2.5 Glue β rule.
  | glueIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (baseType : Ty level scope)
      (boundaryWitness : RawTerm scope)
      {baseRaw partialRaw : RawTerm scope}
      (baseValue : Term context baseType baseRaw)
      (partialValue : Term context baseType partialRaw) :
      Term context (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw)
  | glueElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness gluedRaw : RawTerm scope}
      (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw) :
      Term context baseType (RawTerm.glueElim gluedRaw)
  /-- Cubical transport fragment over a schematic universe path.

      This mirrors the current raw two-argument `RawTerm.transp path source`
      without pretending to implement the full type-family transport rules.
      The raw endpoints are the universe-level codes connected by
      `typePath`; `sourceType` and `targetType` are the typed carriers used
      by the source and result.  The relation between the schematic raw codes
      and these `Ty` values is intentionally explicit data, matching the
      existing heterogeneous-univalence constructors. -/
  | transp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType targetType : Ty level scope)
      (sourceTypeRaw targetTypeRaw : RawTerm scope)
      {pathRaw sourceRaw : RawTerm scope}
      (typePath :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRaw)
      (sourceValue : Term context sourceType sourceRaw) :
      Term context targetType (RawTerm.transp pathRaw sourceRaw)
  /-- Homogeneous cubical composition fragment.

      Current raw `hcomp` has only sides and cap payloads.  The typed mirror
      therefore keeps both payloads in one carrier and adds congruence only;
      computational hcomp boundary rules remain future work. -/
  | hcomp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {sidesRaw capRaw : RawTerm scope}
      (sidesValue : Term context carrierType sidesRaw)
      (capValue : Term context carrierType capRaw) :
      Term context carrierType (RawTerm.hcomp sidesRaw capRaw)
  /-- Single-field record introduction.  Multi-field surface records elaborate
      to nested single-field records until the schema layer lands. -/
  | recordIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstRaw : RawTerm scope}
      (firstField : Term context singleFieldType firstRaw) :
      Term context (Ty.record singleFieldType) (RawTerm.recordIntro firstRaw)
  /-- Single-field record projection. -/
  | recordProj {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {recordRaw : RawTerm scope}
      (recordValue : Term context (Ty.record singleFieldType) recordRaw) :
      Term context singleFieldType (RawTerm.recordProj recordRaw)
  /-- Universe-code at inner level `innerLevel`, typed at outer level
      `≥ outerLevel.toNat + 1` (sitting inside `Ty.universe outerLevel`).
      The cumulativity witness `cumulOk : innerLevel.toNat ≤ outerLevel.toNat`
      makes the same raw `RawTerm.universeCode innerLevel.toNat`
      inhabit `Ty.universe outerLevel` for any compatible outer level
      (used by `Conv.cumul`).  Per Phase 12.A.B1.1, the propositional
      inequality `levelLe : outerLevel.toNat + 1 ≤ level` replaced the
      old `levelEq : level = outerLevel.toNat + 1` to make
      cumulativity intrinsic: a universe-code at outer level
      `outerLevel` inhabits any `level ≥ outerLevel.toNat + 1`. -/
  | universeCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel outerLevel : UniverseLevel)
      (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
      (levelLe : outerLevel.toNat + 1 ≤ level) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.universeCode innerLevel.toNat)
  /-- **REAL CROSS-LEVEL CUMULATIVITY** at the typed Term level —
      Phase CUMUL-2.6 Design D.

      Promotes a Term inhabiting `Ty.universe lowerLevel` to one
      inhabiting `Ty.universe higherLevel`, packaging the source
      term as a payload field.  The output's static type lives at a
      different outer universe-level than the input — this is the
      cumulativity rule `u ≤ v ⊢ u : Type → u : Type[v]` made REAL
      at the term level.

      ## Phase CUMUL-2.6 Design D — single ctx + cumulUpMarker raw output

      Earlier designs (B1, B1.4, etc.) parameterized cumulUp over a
      decoupled lower scope/level/ctx, with the output raw being the
      same `RawTerm.universeCode innerLevel.toNat` as the input —
      breaking the propext-leak floor for inversion lemmas.

      Design D simplifies AND fixes the floor:

      * SINGLE `context` and SINGLE `scope` — same throughout the
        promotion (one outer universe context).
      * `codeRaw` is SCHEMATIC — any raw inhabiting the lower
        universe, not just `RawTerm.universeCode`.  Per CUMUL-2.4,
        the typed `Term` layer at `Ty.universe _` covers
        universeCode, arrowCode, piTyCode, sigmaTyCode, productCode,
        sumCode, listCode, optionCode, eitherCode, idCode,
        equivCode — so `cumulUp` lifts ALL of them uniformly.
      * Output raw is `RawTerm.cumulUpMarker codeRaw` — structurally
        distinct from every other RawTerm ctor, so cases on a typed
        `Term ctx ty .unit` (or .universeCode, .arrowCode, ...)
        excludes the cumulUp branch via raw-ctor mismatch.
        This is the architectural answer to 15 prior CUMUL-2.6
        retreats.

      ## Field meaning
      * `lowerLevel`, `higherLevel` — outer universe levels
      * `cumulMonotone` — cumulativity witness `lowerLevel ≤ higherLevel`
      * `levelLeLow`, `levelLeHigh` — outer-level pinning witnesses
      * `codeRaw` — raw form of the source code (any code-shaped raw)
      * `typeCode` — the REAL TYPED SOURCE Term we're promoting -/
  | cumulUp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codeRaw : RawTerm scope}
      (typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw) :
      Term context (Ty.universe higherLevel levelLeHigh)
                   (RawTerm.cumulUpMarker codeRaw)
  /-- **The canonical identity equivalence `A ≃ A`.**  Inhabitant of
      `Ty.equiv carrier carrier`, raw form is `RawTerm.equivIntro id id`
      where `id = RawTerm.lam (RawTerm.var 0)` is the syntactic
      identity function.  This term is the reduction TARGET of
      `Step.eqType` (the rfl-fragment of Univalence): when an
      identity proof of `Ty.id carrier raw raw` (which can only be
      `Term.refl carrier raw`) reduces under Univalence, it becomes
      this canonical equivalence.
      Phase 12.A.B8.1 (CUMUL-8.1 prerequisite). -/
  | equivReflId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) :
      Term context (Ty.equiv carrier carrier)
                   (RawTerm.equivIntro
                     (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                     (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
  /-- **The canonical pointwise-refl funext witness.**  Inhabitant of
      `Ty.piTy domainTy (Ty.id codomainTy.weaken applyRaw applyRaw)`
      where `applyRaw : RawTerm (scope+1)` is a free raw payload
      (semantically "f x" under the binder, but kept as a fresh
      schematic field to keep rename/subst arms structural).  Raw
      form: `RawTerm.lam (RawTerm.refl applyRaw)`.  This is the
      reduction TARGET of `Step.eqArrow` (the rfl-fragment of
      funext): the Step rule constructs a `funextRefl` whose
      `applyRaw` is concretely `RawTerm.app rawWitness.weaken
      (RawTerm.var 0)`, witnessing "fun x => refl (f x)".  By
      keeping `applyRaw` schematic in the ctor, structural rename
      / subst arms thread it through without fighting weakening
      commute lemmas.
      Phase 12.A.B8.2 (CUMUL-8.2 prerequisite). -/
  | funextRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType : Ty level scope) (codomainType : Ty level scope)
      (applyRaw : RawTerm (scope + 1)) :
      Term context
        (Ty.piTy domainType
          (Ty.id codomainType.weaken applyRaw applyRaw))
        (RawTerm.lam (RawTerm.refl applyRaw))
  /-- **The canonical Id-typed identity-equivalence proof at the universe.**
      Inhabitant of `Ty.id (Ty.universe lvl) carrierRaw carrierRaw` — that
      is, a proof that `carrierRaw = carrierRaw` at the universe level.
      The raw form is the SAME as `Term.equivReflId`'s raw form
      (`RawTerm.equivIntro id id`), making `Step.eqType` a type-only
      reduction at the raw level.  This ctor is the SOURCE of
      `Step.eqType`: it inhabits the universe-level identity type and
      reduces (under Univalence) to `Term.equivReflId carrier`, which
      inhabits `Ty.equiv carrier carrier`.
      ## Why this isn't `Term.refl (Ty.universe lvl) carrierRaw`
      `Term.refl ...` has raw form `RawTerm.refl carrierRaw`.  For
      `Step.eqType` to bridge cleanly through `Step.par.toRawBridge`,
      source and target raw forms must coincide.  This ctor provides
      a canonical witness in `Ty.id (Ty.universe lvl) carrierRaw
      carrierRaw` whose raw is pre-aligned with `Term.equivReflId`'s
      raw form.  Univalence's content is precisely this alignment:
      identity at the universe IS the identity equivalence.
      Phase 12.A.B8.1. -/
  | equivReflIdAtId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      (carrier : Ty level scope)
      (carrierRaw : RawTerm scope) :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw)
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
  /-- **The canonical Id-typed funext witness at arrow types.**
      Inhabitant of `Ty.id (Ty.arrow domainType codomainType) someFnRaw
      someFnRaw` — that is, a reflexive proof that some function equals
      itself.  The raw form is the SAME as `Term.funextRefl`'s raw form
      (`RawTerm.lam (RawTerm.refl applyRaw)`), making `Step.eqArrow` a
      type-only reduction at the raw level.  This ctor is the SOURCE
      of `Step.eqArrow`.
      ## Why this isn't `Term.refl (Ty.arrow ...) someFnRaw`
      `Term.refl ...` has raw form `RawTerm.refl someFnRaw`.  The
      bridge through `Step.par.toRawBridge` requires source and target
      raw forms to match.  This ctor supplies a canonical witness in
      `Ty.id (Ty.arrow domainType codomainType) someFnRaw someFnRaw`
      whose raw is pre-aligned with `Term.funextRefl`'s raw form.
      Funext's content is precisely the alignment: equality of
      functions IS pointwise equality (at the rfl-fragment).
      Phase 12.A.B8.2. -/
  | funextReflAtId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType : Ty level scope) (codomainType : Ty level scope)
      (applyRaw : RawTerm (scope + 1)) :
      Term context
        (Ty.id (Ty.arrow domainType codomainType)
               (RawTerm.lam (RawTerm.refl applyRaw))
               (RawTerm.lam (RawTerm.refl applyRaw)))
        (RawTerm.lam (RawTerm.refl applyRaw))
  /-- **Heterogeneous-carrier equivalence introduction.**
      Inhabitant of `Ty.equiv carrierA carrierB` for arbitrary
      carriers A, B at the same universe level.  Packages a forward
      function `carrierA → carrierB` and a backward function
      `carrierB → carrierA`; the raw form is `RawTerm.equivIntro
      forwardRaw backwardRaw`.

      ## Why this generalizes `Term.equivReflId`

      `Term.equivReflId carrier` ships the canonical identity
      equivalence at `Ty.equiv carrier carrier` — the rfl-fragment
      of Univalence.  Heterogeneous Univalence (`(A B : Type) →
      (A = B) ≃ (A ≃ B)` for ARBITRARY A ≠ B) needs a Term ctor that
      carries arbitrary forward + backward witnesses; this ctor
      provides exactly that.

      ## Cascade contract

      The two subterms (`forward`, `backward`) propagate through
      `Term.rename`, `Term.subst`, `Term.substHet`, `Term.pointwise`,
      and the Allais arm of `ConvCumul.subst_compatible` via two-
      subterm cong infrastructure (mirror of `pairCong` /
      `listConsCong`).  No new Step β/ι rule fires from this ctor
      (it is a value); only `Step.par.equivIntroHetCong` allows
      parallel reduction inside its subterms.

      Phase 12.A.B8.5 (heterogeneous Univalence prerequisite). -/
  | equivIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {forwardRaw backwardRaw : RawTerm scope}
      (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
      (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw) :
      Term context (Ty.equiv carrierA carrierB)
                   (RawTerm.equivIntro forwardRaw backwardRaw)
  /-- Apply a packaged equivalence to an argument.  This mirrors the raw
      `RawTerm.equivApp` constructor and provides the typed target needed
      for Day 2 raw/typed reduction parity.  No β-rule is introduced here:
      the current raw layer only exposes congruence for `equivApp`. -/
  | equivApp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivRaw argumentRaw : RawTerm scope}
      (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
      (argumentTerm : Term context carrierA argumentRaw) :
      Term context carrierB (RawTerm.equivApp equivRaw argumentRaw)
  /-- **Heterogeneous-carrier path-from-equivalence (univalence introduction).**
      Inhabitant of `Ty.id (Ty.universe innerLevel innerLevelLt)
      carrierARaw carrierBRaw` — i.e. a path proof at the universe between
      two arbitrary type-codes — built from a packaged equivalence
      `equivWitness : Term context (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw)`.

      Generalizes `Term.equivReflIdAtId` (rfl-fragment / homogeneous
      carriers only) so that heterogeneous Univalence can produce an
      identity proof at the universe from ANY equivalence between two
      distinct type-codes.

      ## Why the same raw as the equivalence

      The raw form is the SAME `RawTerm.equivIntro forwardRaw backwardRaw`
      as the underlying `equivWitness`.  This pre-aligns the projected
      raw form for the eventual `Step.eqTypeHet` reduction (heterogeneous
      Univalence): the source `Term.uaIntroHet ...` and the target
      `Term.equivIntroHet forward backward` will share the same raw
      projection, so the `Step.par.toRawBridge` arm collapses to
      `RawStep.par.refl _` (the same architectural trick as
      `Step.eqType` / `Step.eqArrow` and `Step.cumulUpInner`).

      ## Carrier representation

      `carrierA, carrierB : Ty level scope` at the OUTER level — the
      universe-of-types level.  The schematic `carrierARaw, carrierBRaw
      : RawTerm scope` are the per-position raw representations of the
      carriers (their universe-codes), kept as fresh schematic fields
      to avoid weakening commute issues during rename/subst (mirror of
      `equivReflIdAtId` and `funextReflAtId`).

      ## Cascade contract

      The single subterm (`equivWitness`) propagates through
      `Term.rename`, `Term.subst`, `Term.substHet`, `Term.pointwise`,
      and the Allais arm of `ConvCumul.subst_compatible` via single-
      subterm cong infrastructure (mirror of `optionSomeCong` /
      `natSuccCong`).  No new Step β/ι rule fires from this ctor as
      a redex source yet (the univalence reduction `Step.eqTypeHet`
      will fire from it later).  Only `Step.par.uaIntroHetCong`
      allows parallel reduction inside its subterm.

      Phase 12.A.B8.5b (heterogeneous Univalence prerequisite, second
      half — pairs with `Term.equivIntroHet` from B8.5). -/
  | uaIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardRaw backwardRaw : RawTerm scope}
      (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw)) :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) carrierARaw carrierBRaw)
        (RawTerm.equivIntro forwardRaw backwardRaw)
  /-- **Heterogeneous-carrier funext-introduction at Id-of-arrow.**
      Inhabitant of `Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam
      applyARaw) (RawTerm.lam applyBRaw)` — that is, a path between two
      DISTINCT lambda-shaped raw functions at the arrow type.  The raw
      form is `RawTerm.lam (RawTerm.refl applyARaw)` (same shape as
      `funextRefl` / `funextReflAtId`, pre-aligned for a future
      `Step.eqArrowHet` reduction).

      ## Why this generalizes `Term.funextReflAtId`

      `Term.funextReflAtId domainType codomainType applyRaw` ships the
      reflexive case: `applyARaw = applyBRaw = applyRaw`, witnessing
      `f = f`.  Heterogeneous funext (`f x = g x for all x ⇒ f = g`
      for ARBITRARY f, g) needs a Term ctor that carries TWO distinct
      apply-payloads `applyARaw, applyBRaw`; this ctor provides exactly
      that.

      ## Why no cast in the type signature

      The result type is `Ty.id (Ty.arrow ...) ... ...` — a non-binder
      `Ty.arrow` carrier inside `Ty.id`.  No `weaken_substHet_commute`
      cast appears in the type signature itself; the substHet/rename/
      subst arms thread `applyARaw, applyBRaw` through `sigma.forRaw.lift`
      structurally, just like `funextReflAtId`.  This is the same
      architectural trick uaIntroHet uses (avoiding the `weaken_subst_
      commute` cast that bogs down `lam` / `funextRefl` arms): keep
      the type carrier `Ty.id (Ty.arrow ...) ...` flat at the OUTER
      scope, push the per-position raw payloads `applyARaw, applyBRaw`
      schematic at scope+1.

      ## Cascade contract

      The four schematic fields (`domainType`, `codomainType`, `applyARaw`,
      `applyBRaw`) propagate through `Term.rename`, `Term.subst`,
      `Term.substHet`, `Term.pointwise`, and the Allais arm of
      `ConvCumul.subst_compatible`.  Like `funextReflAtId`, this is a
      VALUE — its substHet arm depends only on `sigma` (no per-position
      TermSubstHet differences), so the Allais arm collapses to
      `ConvCumul.refl _` (no cast wall).  No new Step β/ι rule fires
      from this ctor as a redex source yet (the future `Step.eqArrowHet`
      reduction will fire FROM `funextIntroHet ... ⇒ funextRefl-style
      witness`, deferred to the next phase).

      Phase 12.A.B8.8 (heterogeneous funext prerequisite, pairs with
      `Term.uaIntroHet` from B8.5b for the full HoTT path-via-equivalence
      / path-via-pointwise duality). -/
  | funextIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType : Ty level scope) (codomainType : Ty level scope)
      (applyARaw applyBRaw : RawTerm (scope + 1)) :
      Term context
        (Ty.id (Ty.arrow domainType codomainType)
               (RawTerm.lam applyARaw)
               (RawTerm.lam applyBRaw))
        (RawTerm.lam (RawTerm.refl applyARaw))
  /-- **Type code for `Ty.arrow`** (non-dependent function type code).
      Inhabitant of `Ty.universe outerLevel levelLe`, raw form is
      `RawTerm.arrowCode domainCodeRaw codomainCodeRaw`.

      ## Why VALUE-shaped (schematic raw payloads)

      Mirroring the `funextIntroHet` / `equivReflIdAtId` precedent
      (Phase 12.A.B8.x), this ctor carries the two subterm raws as
      SCHEMATIC fields rather than recursive Term children.  This
      keeps the cascade machinery (`Term.subst`, `Term.substHet`,
      `Term.pointwise`, `ConvCumul.subst_compatible_*_allais`)
      structural and refl-discharging, avoiding the need for new
      `*Cong` rules in `ConvCumul` (which would cascade through
      every ConvCumul induction).

      A future CUMUL-2.5 may upgrade this ctor to recursive Term
      subterms once the cong infrastructure is in place; for
      CUMUL-2.4 we ship the schematic-payload variant to keep
      cascade arms zero-axiom and atomic.

      Phase 12.A.B-CUMUL-2.4 (typed type-code constructors). -/
  | arrowCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw codomainCodeRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)
  /-- **Type code for `Ty.piTy`** (dependent function type code).
      Codomain raw lives at `scope + 1` (under the Π binder).  Same
      VALUE-shaped (schematic raw) discipline as `arrowCode`. -/
  | piTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw : RawTerm scope)
      (codomainCodeRaw : RawTerm (scope + 1)) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)
  /-- **Type code for `Ty.sigmaTy`** (dependent pair type code).
      Codomain raw lives at `scope + 1` (the second component's type
      may depend on the first).  Same VALUE-shaped (schematic raw)
      discipline as `arrowCode`. -/
  | sigmaTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw : RawTerm scope)
      (codomainCodeRaw : RawTerm (scope + 1)) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw)
  /-- **Type code for `Ty.product`** (non-dependent pair type code).
      Schematic raw payloads (firstCodeRaw, secondCodeRaw).  VALUE-
      shaped per CUMUL-2.4 discipline. -/
  | productCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (firstCodeRaw secondCodeRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.productCode firstCodeRaw secondCodeRaw)
  /-- **Type code for `Ty.sum`** (binary sum type code).  Schematic
      raw payloads (leftCodeRaw, rightCodeRaw).  VALUE-shaped per
      CUMUL-2.4 discipline. -/
  | sumCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodeRaw rightCodeRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.sumCode leftCodeRaw rightCodeRaw)
  /-- **Type code for `Ty.listType`**.  Single schematic raw payload
      (elementCodeRaw).  VALUE-shaped per CUMUL-2.4 discipline. -/
  | listCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodeRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.listCode elementCodeRaw)
  /-- **Type code for `Ty.optionType`**.  Single schematic raw payload
      (elementCodeRaw).  VALUE-shaped per CUMUL-2.4 discipline. -/
  | optionCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodeRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.optionCode elementCodeRaw)
  /-- **Type code for `Ty.eitherType`**.  Schematic raw payloads
      (leftCodeRaw, rightCodeRaw).  VALUE-shaped per CUMUL-2.4
      discipline. -/
  | eitherCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodeRaw rightCodeRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.eitherCode leftCodeRaw rightCodeRaw)
  /-- **Type code for `Ty.id`** (identity type code).  Three schematic
      raw payloads (typeCodeRaw, leftRaw, rightRaw).  VALUE-shaped
      per CUMUL-2.4 discipline. -/
  | idCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.idCode typeCodeRaw leftRaw rightRaw)
  /-- **Type code for `Ty.equiv`** (equivalence type code).  Schematic
      raw payloads (leftTypeCodeRaw, rightTypeCodeRaw).  VALUE-shaped
      per CUMUL-2.4 discipline. -/
  | equivCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
      Term context (Ty.universe outerLevel levelLe)
                   (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw)

end LeanFX2
