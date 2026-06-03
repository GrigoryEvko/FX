import FX1Poly.Typed.ValidTypingLevelFlexible
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/ValidTypingRefinedMotive
    — the total-bridge induction motive `TotalBridgeConclusion` (SN-027, #655)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027, the only remaining gap to
SN-043 now that the ValidTyping fundamental theorem is proved) is an induction on `HasTypeDescPi`.  Its residual
difficulty is per-arm LEVEL coordination: the `conv` / `piElim` arms need their sub-derivations at a SHARED
`contextLevels` and at ALIGNED levels, which a bare `∃ subjectLevel` conclusion (one existential per derivation)
cannot force.

`TotalBridgeConclusion` is the induction motive that does force it: under a shared `contextLevels`, every subject
is valid at SOME single level, AND a NON-VARIABLE subject whose classifier is CONVERTIBLE to a universe code is
additionally LEVEL-FLEXIBLE — valid at every positive level.  Two design points carry the induction:

* **the non-variable guard** `(∀ index, subject ≠ variableCell index)` on the flexibility conjunct.  A type
  VARIABLE (`var j : Type@e`) is PINNED to `contextLevels j` by `ValidTyping.var` — it provably cannot be
  level-flexible — so the motive must not demand flexibility OF a variable subject.  A variable's reclassifier
  role is instead handled by `validTypingBridgeConvPinnedReclassifier` (via the leveling equation).
* **the convertibility guard** `Conv classifier (universeCodeCell …)` (rather than syntactic equality) on the
  flexibility conjunct, so it propagates through the `conv` arm by `Conv.trans` (a conv changes a subject's
  classifier to a CONVERTIBLE one, not a syntactically-equal one; a syntactic guard would not survive).

The level-flexible witnesses are produced by the formers (`ValidTypingLevelFlexible.lean`'s
`universeFormation_isLevelFlexible` / `pi`/`sigmaFormation_isLevelFlexible`); this file wires them into the motive.

## What is proved

* `TotalBridgeConclusion` — the motive: single-level validity ∧ (non-variable convertible-to-universe-classifier
  ⟹ level-flexible).
* `TotalBridgeConclusion.var` — the variable arm (conjunct-2 vacuous: the subject IS a variable).
* `TotalBridgeConclusion.universeFormation` — the universe-code arm (flexibility via `universeFormation_isLevelFlexible`).
* `TotalBridgeConclusion.convNonVariableReclassifier` — the conv arm for a non-variable reclassifier (the
  variable-reclassifier case routes through `validTypingBridgeConvPinnedReclassifier`, `ValidTypingConvArm.lean`).
* `TotalBridgeConclusion.ofTermValidity` — the term wrapper: a subject whose classifier is not convertible to any
  universe code satisfies the motive (conjunct-2 vacuous).

## Zero-axiom verification

Field accesses + anonymous constructors + `universeCodeCell_inj_of_conv` (propext-free `cases` injectivity) +
`Conv.trans`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The total-bridge induction motive.**  Single-level validity, plus level-flexibility for a
universe-classified subject that is NOT a variable.  Two design points: (1) the non-variable guard
`(∀ index, subject ≠ variableCell index)` on the flexibility conjunct — the unguarded conjunct is unsatisfiable
for a type variable, pinned by `ValidTyping.var`; (2) the flexibility conjunct is guarded by CONVERTIBILITY
`Conv classifier (universeCodeCell …)` rather than syntactic equality, so it propagates through the `conv` arm by
`Conv.trans`.  The leaf `universeFormation` arm meets the convertibility guard via `universeCodeCell_inj_of_conv`. -/
def TotalBridgeConclusion (profile : PolyProfile) {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  (∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier) ∧
  (∀ (levelExpr : LevelExpr) (flag : UniverseFlag), Conv classifier (universeCodeCell levelExpr flag) →
    (∀ index : Fin scope, subject ≠ variableCell index) →
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag)

/-- **The var arm of the motive.**  Conjunct-1 by `ValidTyping.var` (at the variable's pinned env level
`contextLevels index`); conjunct-2 VACUOUS — the subject is `variableCell index`, so the non-variable guard
`∀ j, variableCell index ≠ variableCell j` is contradictory at `j := index`.  The arm a type variable's pinned
level makes sound (the over-demanding earlier motive could not discharge it). -/
theorem TotalBridgeConclusion.var {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) (index : Fin scope) :
    TotalBridgeConclusion profile contextLevels context
      (variableCell index) (context.lookup index) :=
  ⟨⟨contextLevels index, ValidTyping.var contextLevels context index⟩,
   fun _levelExpr _flag _classifierConv subjectNotVariable =>
     absurd rfl (subjectNotVariable index)⟩

/-- **The universeFormation arm of the motive.**  Conjunct-1 by `ValidTyping.universeFormation`; conjunct-2 by
`universeFormation_isLevelFlexible` (a universe code is a non-variable type code).  The convertibility guard
`Conv (Type@(lsucc levelExpr)) (Type@outLevel outFlag)` is met via `universeCodeCell_inj_of_conv` — convertible
universe codes have equal level/flag, so `outLevel = lsucc levelExpr` and `outFlag = flag`, reducing to the
shipped former-level-polymorphism. -/
theorem TotalBridgeConclusion.universeFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    TotalBridgeConclusion profile contextLevels context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  ⟨⟨0 + 1, ValidTyping.universeFormation contextLevels 0 context levelExpr flag⟩,
   fun _outLevel _outFlag classifierConv _subjectNotVariable => by
     obtain ⟨rfl, rfl⟩ := universeCodeCell_inj_of_conv classifierConv
     exact universeFormation_isLevelFlexible contextLevels context levelExpr flag⟩

/-- **The conv arm of the motive (non-variable reclassifier).**  Reclassifying the subject's type from
`classifier` to a NON-VARIABLE `reclassifier` (typed at `universeCodeCell levelExpr flag`) preserves the motive.
Conjunct-1: the reclassifier, being a non-variable universe-classified type code, is LEVEL-FLEXIBLE (its own
conjunct-2 at `Conv.refl`), so `ValidTyping.convWithLevelFlexibleReclassifier` reclassifies the subject.
Conjunct-2: the subject is UNCHANGED, and a convertibility-to-universe-code witness for the NEW classifier
(`reclassifier`) composes with the conv (`Conv.trans`) into one for the OLD classifier, which the subject's own
conjunct-2 consumes — the propagation the convertibility guard was designed for.  The VARIABLE-reclassifier case
(`reclassifier = variableCell j`, a pinned neutral type code) is handled separately via
`validTypingBridgeConvPinnedReclassifier` and the leveling equation; `RawTerm.isVariableOrNot` routes between the
two in the assembly. -/
theorem TotalBridgeConclusion.convNonVariableReclassifier {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectTyped : TotalBridgeConclusion profile contextLevels context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped :
      TotalBridgeConclusion profile contextLevels context reclassifier (universeCodeCell levelExpr flag))
    (reclassifierNotVariable : ∀ index : Fin scope, reclassifier ≠ variableCell index) :
    TotalBridgeConclusion profile contextLevels context subject reclassifier := by
  obtain ⟨⟨subjectLevel, subjectValid⟩, subjectFlexible⟩ := subjectTyped
  refine ⟨?_, ?_⟩
  · have reclassifierFlexible :=
      reclassifierTyped.2 levelExpr flag (Conv.refl _) reclassifierNotVariable
    exact ValidTyping.convWithLevelFlexibleReclassifier contextLevels subjectLevel subjectValid converts
      reclassifierFlexible
  · intro outLevel outFlag reclassifierConvUniverse subjectNotVariable
    exact subjectFlexible outLevel outFlag (Conv.trans converts reclassifierConvUniverse) subjectNotVariable

/-- **The term-subject wrapper.**  A subject valid at one level whose classifier is NOT convertible to ANY
universe code satisfies the motive: conjunct-1 is the supplied validity, conjunct-2 is vacuous (its convertibility
guard `Conv classifier (universeCodeCell …)` is unsatisfiable).  The binder and elimination TERM-output arms
consume this with the shipped `Conv.piTyCode_not_universeCode` / `Conv.sigmaTyCode_not_universeCode` no-confusion
facts (a Π/Σ code is never convertible to a universe code). -/
theorem TotalBridgeConclusion.ofTermValidity {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {subjectLevel : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (classifierNotConvUniverse : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv classifier (universeCodeCell levelExpr flag)) :
    TotalBridgeConclusion profile contextLevels context subject classifier :=
  ⟨⟨subjectLevel, typed⟩,
   fun levelExpr flag classifierConv _subjectNotVariable =>
     absurd classifierConv (classifierNotConvUniverse levelExpr flag)⟩

end FX1Poly.Typed
