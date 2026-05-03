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
      `outerLevel.toNat + 1` (sitting inside `Ty.universe outerLevel`).
      The cumulativity witness `cumulOk : innerLevel.toNat ≤ outerLevel.toNat`
      makes the same raw `RawTerm.universeCode innerLevel.toNat`
      inhabit `Ty.universe outerLevel` for any compatible outer level
      (used by `Conv.cumul`).  The propositional `levelEq` parameter
      threads through `Ty.universe` per the P-3 universe-constructor-
      blocker workaround. -/
  | universeCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel outerLevel : UniverseLevel)
      (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
      (levelEq : level = outerLevel.toNat + 1) :
      Term context (Ty.universe outerLevel levelEq)
                   (RawTerm.universeCode innerLevel.toNat)

end LeanFX2
