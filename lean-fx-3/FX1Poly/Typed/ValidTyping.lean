import FX1Poly.Typed.FundamentalLevelIndexed
import FX1Poly.Typed.ClosedLevelIndexed

/-! # FX1Poly/Typed/ValidTyping
    — the level-annotated typing (Abel validity-derivation-indexed relation): the recursor, var/universe/conv/Π core

The level-indexed fundamental theorem has all its per-constructor ARMS shipped as standalone lemmas
(`FundamentalLevelIndexed.lean`), but the RECURSOR that assembles them was blocked: a single level-free motive
cannot serve both `var` (concludes at its env-fixed level `contextLevels index`) and `conv` (needs the
reclassifier reducible one level ABOVE the subject) — the documented var/conv coordination wall.

The Abel/Adjedj resolution (arXiv:2310.06376) is to index the relation by a VALIDITY DERIVATION carrying each
node's level.  `ValidTyping` realizes this directly: it is the formation typing with the level annotated INTO
the inductive, so the coordination holds BY CONSTRUCTION —

* `var` concludes at `contextLevels index` (its env level);
* `conv`'s `reclassifierTyped` is at `subjectLevel + 1` (one level up, exactly what `tarskiDecode` + the
  conv-transport need);
* `universeFormation` is level-polymorphic (any `predLevel + 1`);
* `piIntro` checks domain & codomain codes at `predLevel + 1 + 1` (their universe sits one above the function's
  level) and the body at `predLevel + 1` under `levelCons (predLevel + 1)` (the bound variable's env level);
* `piElim` keeps function, argument, and application at one shared `subjectLevel`.

With the levels pinned by the constructor, the fundamental theorem `ValidTyping.fundamental` is a CLEAN single
induction (`ValidTyping.rec`): each arm is discharged verbatim by the shipped level-indexed arm
(`fundamentalVarLevelIndexed` / `…UniverseFormation…` / `…Conv…` / `…PiIntro…` / `…PiElim…`), with `conv`
threading its two IHs and `piIntro` its three (under the extended env) at the coordinated levels.  This is the
assembled recursor on the dependent-FT lane — the var/conv wall broken, now extended through the COMPUTATIONAL
core (λ-introduction + application, where β-redexes live).

## Honest scope

This covers `var` / `universeFormation` / `conv` / `piIntro` / `piElim` — the leaf+conv core PLUS the
function/application computational core.  The closed identity `λx.x : Π(_ : U). U` is SN through this recursor
(`validTyping_identity_stronglyNormalizing`), the first dependent-FT SN witness whose subject carries a binder
and a bound-variable occurrence.  Two pieces remain to land full SN-for-well-typed: (1) the `genFormation` /
`sigma` arms — remaining type formers, threading the shipped `fundamentalGenFormationFormerLevelIndexed` through
a level-annotated `DescTelescope`; (2) the LEVELING bridge `HasTypeDescPi → ValidTyping` (every level-free
derivation admits a consistent leveling — `var` at the context's recorded level, `conv`'s reclassifier re-leveled
one up since universe-code members are level-polymorphic).  This file establishes that, once levels are
annotated, the recursor assembles through the binder arms — the design that was the open crux.

## Zero-axiom verification

The inductive is strictly positive (mentions `Conv` and itself only positively; index signature is
non-self-referential).  `fundamental` is `ValidTyping.rec` (propext-free recursor) + the shipped arms;
`closedStronglyNormalizing` composes it with the closed-SN handoff.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Level-annotated formation typing** (the Abel validity-derivation-indexed relation, leaf+conv core).  The
levels are part of the inductive, so the var/conv level coordination that blocks the level-free recursor holds
by construction. -/
inductive ValidTyping (profile : PolyProfile) :
    {scope : Nat} → (Fin scope → Nat) → Nat → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | var {scope : Nat} (contextLevels : Fin scope → Nat)
      (context : TypingContext profile scope) (index : Fin scope) :
      ValidTyping profile contextLevels (contextLevels index) context
        (variableCell index) (context.lookup index)
  | universeFormation {scope : Nat} (contextLevels : Fin scope → Nat) (predLevel : Nat)
      (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
      ValidTyping profile contextLevels (predLevel + 1) context
        (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag)
  | conv {scope : Nat} (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
      {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      {levelExpr : LevelExpr} {flag : UniverseFlag}
      (typed : ValidTyping profile contextLevels subjectLevel context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped : ValidTyping profile contextLevels (subjectLevel + 1) context
        reclassifier (universeCodeCell levelExpr flag)) :
      ValidTyping profile contextLevels subjectLevel context subject reclassifier
  | piIntro {scope : Nat} (contextLevels : Fin scope → Nat) (predLevel : Nat)
      {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
      {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
      (domainTyped : ValidTyping profile contextLevels (predLevel + 1 + 1) context
        domainCode (universeCodeCell domainLevel flag))
      (codomainTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
        (predLevel + 1 + 1) (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag))
      (bodyTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
        (predLevel + 1) (context.cons domainCode) body codomainCode) :
      ValidTyping profile contextLevels (predLevel + 1) context
        (lamCell body) (piTyCodeCell domainCode codomainCode)
  | piElim {scope : Nat} (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
      {context : TypingContext profile scope}
      {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      (functionTyped : ValidTyping profile contextLevels subjectLevel context functionTerm
        (piTyCodeCell domainCode codomainCode))
      (argumentTyped : ValidTyping profile contextLevels subjectLevel context argument domainCode) :
      ValidTyping profile contextLevels subjectLevel context
        (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument)

/-- **The fundamental theorem over `ValidTyping`** — the assembled recursor for the var/universe/conv/Π core.  A
clean single induction (`ValidTyping.rec`): each arm is discharged verbatim by the shipped level-indexed arm
(`fundamentalVarLevelIndexed` / `…UniverseFormation…` / `…Conv…` / `…PiIntro…` / `…PiElim…`).  `conv` threads its
two IHs (subject at `subjectLevel`, reclassifier at `subjectLevel + 1`); `piIntro` threads three (domain &
codomain codes at `predLevel + 1 + 1`, body at `predLevel + 1`, under the extended `levelCons` environment);
`piElim` threads function & argument at the same level.  Because the inductive carries the per-arm level
environments as genuine indices, `induction` binds `contextLevels` as a named arm variable in every arm (it is
threaded explicitly to each shipped lemma, not inferred). -/
theorem ValidTyping.fundamental {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {subjectLevel : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier) :
    FundamentalConclusionLevelIndexed contextLevels subjectLevel context subject classifier := by
  induction typed with
  | var contextLevels context index =>
      exact fundamentalVarLevelIndexed contextLevels context index
  | universeFormation contextLevels predLevel context levelExpr flag =>
      exact fundamentalUniverseFormationLevelIndexed contextLevels predLevel context levelExpr flag
  | conv contextLevels subjectLevel _typed converts _reclassifierTyped typedIH reclassifierIH =>
      exact fundamentalConvLevelIndexed contextLevels subjectLevel typedIH reclassifierIH converts
  | piIntro contextLevels predLevel _domainTyped _codomainTyped _bodyTyped domainIH codomainIH bodyIH =>
      exact fundamentalPiIntroLevelIndexed contextLevels predLevel domainIH codomainIH bodyIH
  | piElim contextLevels subjectLevel _functionTyped _argumentTyped functionIH argumentIH =>
      exact fundamentalPiElimLevelIndexed contextLevels subjectLevel functionIH argumentIH

/-- **Closed strong normalization from `ValidTyping`** — the recursor's payoff for this fragment: a closed
`ValidTyping` derivation at a positive level is UNCONDITIONALLY strongly normalizing (FT + the empty-context
closed-SN handoff).  This is SN-for-well-typed for the leaf+conv core, assembled through the recursor. -/
theorem ValidTyping.closedStronglyNormalizing {profile : PolyProfile} (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : ValidTyping profile emptyLevelVector (predLevel + 1)
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsStronglyNormalizing subject :=
  closedSubjectStronglyNormalizingFromLevelIndexed predLevel typed.fundamental

/-- **Smoke: the recursor path lands SN end-to-end.**  A closed universe code is `ValidTyping`-derivable (the
`universeFormation` arm at the empty context), and `closedStronglyNormalizing` discharges it to plain SN
through the assembled fundamental theorem — demonstrating the recursor is non-vacuous (it produces genuine SN,
not just a vacuous conclusion). -/
theorem validTyping_universeCode_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (universeCodeCell levelExpr flag : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.universeFormation emptyLevelVector 0
      (TypingContext.empty : TypingContext profile 0) levelExpr flag)

/-- **Smoke: the closed identity `λx.x` is SN through the recursor's `piIntro` arm.**  This exercises the
computational core: the lambda binds a real variable (`bodyTyped` is the `var` arm at the extended context), so
`piIntro` is applied non-vacuously — the recursor threads `var` under a binder and `closedStronglyNormalizing`
discharges the whole lambda to plain SN.  The function has type `Π(_ : U). U` (universe-to-universe identity).
This is the first SN witness on the dependent-FT lane whose subject contains a binder AND a bound-variable
occurrence — the shape where β-redexes live. -/
theorem validTyping_identity_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.piIntro emptyLevelVector 0
      (domainLevel := levelExpr.lsucc) (codomainLevel := levelExpr.lsucc) (flag := flag)
      (ValidTyping.universeFormation emptyLevelVector 1
        (TypingContext.empty : TypingContext profile 0) levelExpr flag)
      (ValidTyping.universeFormation (levelCons 1 emptyLevelVector) 1
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        levelExpr flag)
      (ValidTyping.var (levelCons 1 emptyLevelVector)
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

end FX1Poly.Typed
