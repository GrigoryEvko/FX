import FX1Poly.Typed.ValidTypingLevelFlexible
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/ValidTypingRefinedMotive
    — the refined-motive total-bridge conclusion (SN-027, #655)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027, the only remaining gap to
SN-043 now that the ValidTyping fundamental theorem is proved) is an induction on `HasTypeDescPi`.  Its residual
difficulty is per-arm LEVEL coordination: the `conv` / `piElim` arms need their sub-derivations at a SHARED
`contextLevels` and at ALIGNED levels, which a bare `∃ subjectLevel` conclusion (one existential per derivation)
cannot force.

This file defines the REFINED MOTIVE that does force it: under a shared `contextLevels`, every subject is valid
at SOME single level, AND a TYPE-CODE-classified subject (classifier a universe code) is additionally
LEVEL-FLEXIBLE — valid at every positive level.  The level-flexible witnesses are produced by the formers
(`ValidTypingLevelFlexible.lean`'s `universeFormation_isLevelFlexible` / `pi`/`sigmaFormation_isLevelFlexible`);
this file wires them into the motive (`ofLevelFlexible`) and exposes the two projections the arms consume.

## What is proved

* `RefinedTotalBridgeConclusion` — the refined motive: single-level validity ∧ (universe-classifier ⟹
  level-flexible).
* `RefinedTotalBridgeConclusion.singleLevel` — projects the bare `∃ subjectLevel` validity (the total-bridge
  target's shape).
* `RefinedTotalBridgeConclusion.flexibleOfUniverseClassifier` — projects the level-flexibility of a
  universe-classified subject.
* `RefinedTotalBridgeConclusion.ofLevelFlexible` — **the producer**: a level-flexible type code satisfies the
  refined motive (single level at fuel 0; the all-level form via `universeCodeCell_inj`).  This is how the
  former arms (`*_isLevelFlexible`) feed the induction.

## Zero-axiom verification

The projections are field accesses; `ofLevelFlexible` is an anonymous constructor plus `universeCodeCell_inj`
(propext-free `cases` injectivity).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The refined-motive total-bridge conclusion.**  The subject is valid at SOME single level under its
classifier, AND if the classifier is a universe code the subject is a LEVEL-FLEXIBLE type code (valid at every
positive level).  The second conjunct lets the `conv` / `piElim` arms align levels — a type-code subject carries
its all-level form, which the bare `∃` shape cannot supply. -/
def RefinedTotalBridgeConclusion (profile : PolyProfile) {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  (∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier) ∧
  (∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
    classifier = universeCodeCell levelExpr flag →
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag)

/-- Project the single-level validity (the bare existential the total-bridge target consumes). -/
theorem RefinedTotalBridgeConclusion.singleLevel {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (conclusion : RefinedTotalBridgeConclusion profile contextLevels context subject classifier) :
    ∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier :=
  conclusion.1

/-- Project the level-flexibility of a universe-classified (type-code) subject. -/
theorem RefinedTotalBridgeConclusion.flexibleOfUniverseClassifier {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    {subject : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (conclusion : RefinedTotalBridgeConclusion profile contextLevels context subject
      (universeCodeCell levelExpr flag)) :
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag :=
  conclusion.2 levelExpr flag rfl

/-- **A level-flexible type code satisfies the refined motive** (the producer side).  The formers
(`universeFormation` / `piFormation` / `sigmaFormation`, via `*_isLevelFlexible`) build
`IsLevelFlexibleTypeCode`, which gives both conjuncts: single-level validity by instantiating at fuel 0, and the
all-level form via universe-code injectivity (`universeCodeCell_inj`). -/
theorem RefinedTotalBridgeConclusion.ofLevelFlexible {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    {subject : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (flexible : IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag) :
    RefinedTotalBridgeConclusion profile contextLevels context subject
      (universeCodeCell levelExpr flag) :=
  ⟨⟨0 + 1, flexible 0⟩, fun _le _fl eq => by
    obtain ⟨rfl, rfl⟩ := universeCodeCell_inj eq
    exact flexible⟩

/-! ## The REVISED motive — the var-arm fix (SN-027/#662 assembly)

`RefinedTotalBridgeConclusion`'s conjunct-2 demanded `IsLevelFlexibleTypeCode` for EVERY universe-classified
subject, which a TYPE VARIABLE (`var j : Type@e`, pinned to `contextLevels j` by `ValidTyping.var`) provably
cannot satisfy — so its var arm was the standing wall.  The revised motive adds the guard
`(∀ index, subject ≠ variableCell index)`, EXCLUDING variable subjects from the level-flexibility demand.  This
is exactly the right exclusion: a variable's reclassifier role is handled by `validTypingBridgeConvPinnedReclassifier`
(via the leveling equation), not by all-level flexibility, so the motive should not demand flexibility OF a
variable subject.  With the guard, the `var` arm discharges conjunct-2 VACUOUSLY (the subject IS a variable),
and the non-variable type-code arms (`universeFormation` here; Π/Σ/gen formers later) supply flexibility as
before.  The `RawTerm.isVariableOrNot` dichotomy routes the conv arm onto this guard. -/

/-- **The revised total-bridge conclusion.**  Single-level validity, plus level-flexibility for a
universe-classified subject that is NOT a variable.  Two refinements over `RefinedTotalBridgeConclusion`:
(1) the non-variable guard `(∀ index, subject ≠ variableCell index)` on conjunct-2 — the var-arm fix
(the unguarded conjunct-2 is unsatisfiable for a type variable, pinned by `ValidTyping.var`);
(2) conjunct-2 is guarded by CONVERTIBILITY `Conv classifier (universeCodeCell …)` rather than syntactic
equality, so it propagates through the `conv` arm by `Conv.trans` (a conv changes a subject's classifier to a
CONVERTIBLE one, not a syntactically-equal one; the syntactic guard would not survive).  The leaf
`universeFormation` arm meets the convertibility guard via `universeCodeCell_inj_of_conv`. -/
def RevisedBridgeConclusion (profile : PolyProfile) {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  (∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier) ∧
  (∀ (levelExpr : LevelExpr) (flag : UniverseFlag), Conv classifier (universeCodeCell levelExpr flag) →
    (∀ index : Fin scope, subject ≠ variableCell index) →
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag)

/-- **The var arm of the revised motive.**  Conjunct-1 by `ValidTyping.var` (at the variable's pinned env level
`contextLevels index`); conjunct-2 VACUOUS — the subject is `variableCell index`, so the non-variable guard
`∀ j, variableCell index ≠ variableCell j` is contradictory at `j := index`.  This is the arm that the refined
motive could not discharge for a type variable. -/
theorem RevisedBridgeConclusion.var {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) (index : Fin scope) :
    RevisedBridgeConclusion profile contextLevels context
      (variableCell index) (context.lookup index) :=
  ⟨⟨contextLevels index, ValidTyping.var contextLevels context index⟩,
   fun _levelExpr _flag _classifierConv subjectNotVariable =>
     absurd rfl (subjectNotVariable index)⟩

/-- **The universeFormation arm of the revised motive.**  Conjunct-1 by `ValidTyping.universeFormation`;
conjunct-2 by `universeFormation_isLevelFlexible` (a universe code is a non-variable type code).  The
convertibility guard `Conv (Type@(lsucc levelExpr)) (Type@outLevel outFlag)` is met via
`universeCodeCell_inj_of_conv` — convertible universe codes have equal level/flag, so `outLevel = lsucc levelExpr`
and `outFlag = flag`, reducing to the shipped former-level-polymorphism. -/
theorem RevisedBridgeConclusion.universeFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RevisedBridgeConclusion profile contextLevels context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  ⟨⟨0 + 1, ValidTyping.universeFormation contextLevels 0 context levelExpr flag⟩,
   fun _outLevel _outFlag classifierConv _subjectNotVariable => by
     obtain ⟨rfl, rfl⟩ := universeCodeCell_inj_of_conv classifierConv
     exact universeFormation_isLevelFlexible contextLevels context levelExpr flag⟩

/-- **The conv arm of the revised motive (non-variable reclassifier).**  Reclassifying the subject's type from
`classifier` to a NON-VARIABLE `reclassifier` (typed at `universeCodeCell levelExpr flag`) preserves the revised
motive.  Conjunct-1: the reclassifier, being a non-variable universe-classified type code, is LEVEL-FLEXIBLE (its
own conjunct-2 at `Conv.refl`), so `ValidTyping.convWithLevelFlexibleReclassifier` reclassifies the subject.
Conjunct-2: the subject is UNCHANGED, and a convertibility-to-universe-code witness for the NEW classifier
(`reclassifier`) composes with the conv (`Conv.trans`) into one for the OLD classifier, which the subject's own
conjunct-2 consumes — the propagation the convertibility guard was designed for.  The VARIABLE-reclassifier case
(`reclassifier = variableCell j`, a pinned neutral type code) is handled separately via
`validTypingBridgeConvPinnedReclassifier` and the leveling equation; `RawTerm.isVariableOrNot` routes between the
two in the assembly. -/
theorem RevisedBridgeConclusion.convNonVariableReclassifier {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectTyped : RevisedBridgeConclusion profile contextLevels context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped :
      RevisedBridgeConclusion profile contextLevels context reclassifier (universeCodeCell levelExpr flag))
    (reclassifierNotVariable : ∀ index : Fin scope, reclassifier ≠ variableCell index) :
    RevisedBridgeConclusion profile contextLevels context subject reclassifier := by
  obtain ⟨⟨subjectLevel, subjectValid⟩, subjectFlexible⟩ := subjectTyped
  refine ⟨?_, ?_⟩
  · have reclassifierFlexible :=
      reclassifierTyped.2 levelExpr flag (Conv.refl _) reclassifierNotVariable
    exact ValidTyping.convWithLevelFlexibleReclassifier contextLevels subjectLevel subjectValid converts
      reclassifierFlexible
  · intro outLevel outFlag reclassifierConvUniverse subjectNotVariable
    exact subjectFlexible outLevel outFlag (Conv.trans converts reclassifierConvUniverse) subjectNotVariable

end FX1Poly.Typed
