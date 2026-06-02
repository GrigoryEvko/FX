import FX1Poly.Typed.FundamentalLevelIndexed
import FX1Poly.Typed.ClosedLevelIndexed

/-! # FX1Poly/Typed/ValidTyping
    — the level-annotated typing (Abel validity-derivation-indexed relation): the recursor, leaf+conv core

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
* `universeFormation` is level-polymorphic (any `predLevel + 1`).

With the levels pinned by the constructor, the fundamental theorem `ValidTyping.fundamental` is a CLEAN single
induction (`ValidTyping.rec`): each arm is discharged verbatim by the shipped level-indexed arm
(`fundamentalVarLevelIndexed` / `fundamentalUniverseFormationLevelIndexed` / `fundamentalConvLevelIndexed`),
with `conv` threading its two IHs at the two coordinated levels.  This is the FIRST assembled recursor on the
dependent-FT lane — the var/conv wall broken for the leaf+conv core.

## Honest scope

This is the `var` / `universeFormation` / `conv` CORE of the formation engine.  Two pieces remain to land full
SN-for-well-typed: (1) the `genFormation` arm — Π/Σ type formers, threading the shipped
`fundamentalGenFormationFormerLevelIndexed` through a level-annotated `DescTelescope`; (2) the LEVELING bridge
`HasTypeDesc → ValidTyping` (every level-free formation derivation admits a consistent leveling — `var` at the
context's recorded level, `conv`'s reclassifier re-leveled one up since universe-code members are
level-polymorphic).  This file establishes that, once levels are annotated, the recursor assembles — the design
that was the open crux.

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

/-- **The fundamental theorem over `ValidTyping`** — the assembled recursor for the leaf+conv core.  A clean
single induction (`ValidTyping.rec`): each arm is the shipped level-indexed arm; `conv` threads its two IHs
(subject at `subjectLevel`, reclassifier at `subjectLevel + 1`) through `fundamentalConvLevelIndexed`.  The
`contextLevels` index is pre-generalized by `induction`, so it is inferred (`_`) at each arm rather than
re-bound. -/
theorem ValidTyping.fundamental {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {subjectLevel : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier) :
    FundamentalConclusionLevelIndexed contextLevels subjectLevel context subject classifier := by
  induction typed with
  | var context index =>
      exact fundamentalVarLevelIndexed _ context index
  | universeFormation predLevel context levelExpr flag =>
      exact fundamentalUniverseFormationLevelIndexed _ predLevel context levelExpr flag
  | conv subjectLevel _typed converts _reclassifierTyped typedIH reclassifierIH =>
      exact fundamentalConvLevelIndexed _ subjectLevel typedIH reclassifierIH converts

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

end FX1Poly.Typed
