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

## D1.9 typed Term ctors — DEFERRED to per-need addition

The 27 raw ctors added in D1.6 (cubical/HOTT/refine/record/codata/session/
effect/strict) deliberately do NOT have typed Term mirrors yet.  The
math work for D2.5–D2.7 (cubical β, HOTT OEq, modal/refine/etc. β) lives
at the RAW level (RawTerm.cd, Step.par); typed reduction lifts via the
rfl bridge once the raw rules ship.

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
  /-- **REAL CROSS-LEVEL CUMULATIVITY** at the typed Term level.
      Promotes a closed (scope = 0) Term inhabiting `Ty.universe lowerLevel`
      to one inhabiting `Ty.universe higherLevel`, packaging the source
      term as a payload field.  The output's static type lives at a
      different outer universe-level than the input — this is the
      cumulativity rule `u ≤ v ⊢ u : Type → u : Type[v]` made REAL at
      the term level.

      ## Decoupled lower scope (Phase 12.A.B1.4 — drop scope=0 restriction)
      The P-4 cumul-Subst-mismatch wall (`feedback_lean_cumul_subst_mismatch`)
      forbids freely substituting through a level-mismatched payload.
      Phase 12.A.B1.4 sidesteps the wall by DECOUPLING `scopeLow` from
      the outer `scope`: `ctxLow` lives at its own scope `scopeLow`, and
      `Term.subst`'s arm leaves `scopeLow` (and hence `lowerTerm`)
      UNCHANGED.  The lower-side substitution is opaque to the outer
      Subst — the user can independently substitute the lower side via
      `Term.cumulUp_subst_lower` (a separate operation).

      Previous architecture (scope = 0 only): closed lower term required.
      New architecture (arbitrary scopeLow): local lower term permitted,
      but its substitution is independent of the outer Subst.

      ## How cumulUp uses its source
      `lowerTerm` is a real field of the constructor.  Term.subst's
      arm for cumulUp passes `lowerTerm` through unchanged (its scope
      `scopeLow` is independent of the outer `scope` being substituted),
      reconstructing the output via `Term.cumulUp` at the new target
      scope.  The output structure literally contains the input term
      as a payload — that is REAL packaging, not witness synthesis.

      ## Field meaning
      * `lowerLevel`, `higherLevel` — outer universe levels
      * `cumulOk` — the cumulativity witness `lowerLevel ≤ higherLevel`
      * `scopeLow` — the lower-side scope (decoupled from outer `scope`)
      * `ctxLow` — context at the lower outer level (at `scopeLow`)
      * `ctxHigh` — arbitrary outer context at the higher level
      * `innerRaw` — raw form of the lower term (at `scopeLow`)
      * `lowerTerm` — the REAL TYPED SOURCE Term we're promoting -/
  | cumulUp {mode : Mode} {levelLow level scopeLow scope : Nat}
      (innerLevel lowerLevel higherLevel : UniverseLevel)
      (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
      (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ levelLow)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {ctxLow : Ctx mode levelLow scopeLow}
      {ctxHigh : Ctx mode level scope}
      (lowerTerm :
        Term ctxLow (Ty.universe lowerLevel levelLeLow)
                    (RawTerm.universeCode innerLevel.toNat)) :
      Term ctxHigh (Ty.universe higherLevel levelLeHigh)
           (RawTerm.universeCode innerLevel.toNat)
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

end LeanFX2
