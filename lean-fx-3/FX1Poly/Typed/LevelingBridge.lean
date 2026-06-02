import FX1Poly.Typed.ValidTyping

/-! # FX1Poly/Typed/LevelingBridge
    — the leveling bridge `HasTypeDescPi → ValidTyping`, var/conv/universeFormation arms (SN-022)

`HasTypeDescPi` is LEVEL-FREE (no explicit universe-level annotations); `ValidTyping` is LEVEL-ANNOTATED
(per-binder `contextLevels : Fin scope → Nat` + a `subjectLevel : Nat`).  The leveling bridge synthesizes the
levels: `HasTypeDescPi profile context subject classifier → ∃ contextLevels subjectLevel,
ValidTyping profile contextLevels subjectLevel context subject classifier`, by induction on the derivation.
Composed with the PROVEN `ValidTyping.fundamental`, the bridge yields unconditional dependent reducibility /
SN — the route `ValidTyping`'s own docstring names as the second of its two remaining pieces (the first,
the generic `genFormationPi` arm, landed in SN-021).

This file lands the per-arm building blocks for the var / conv / universeFormation cases (SN-022); the
binder / former arms (piIntro / piElim / Π-&Σ-formation / genFormationPi) are SN-023, and the full
inductive assembly — which threads a CONSISTENT `contextLevels` across the derivation and supplies the conv
arm's coordinated sub-derivations — is the later composition step (SN-027).

## Why the var and universeFormation arms are unconditional leaves

* **var (the off-by-one dodge, SN-024).**  A variable cell with its looked-up type is `ValidTyping`-derivable
  with NO hypothesis at all: `ValidTyping.var` concludes at exactly `subjectLevel := contextLevels index` —
  the variable's own context level — so `validTypingBridgeVar` is a direct constructor application.  This is
  precisely the coordination the uniform-level recursor route (`ScratchFT/FundamentalTheoremRec.lean`'s
  blocked `ofFormation` var case) could NOT achieve: it demanded `envLevels index = predLevel + 1` for
  independently-quantified `envLevels`/`predLevel`.  Baking `subjectLevel := contextLevels index` dissolves
  the wall.

* **universeFormation (any positive level).**  A universe code `Type@e` bridges to
  `ValidTyping.universeFormation` at any `predLevel + 1` (here `predLevel := 0`), with classifier the `lsucc`
  code — again a direct constructor application, no hypothesis.

## The conv arm carries its coordinated inputs

`validTypingBridgeConv` is the conv building block: GIVEN the subject valid at `subjectLevel` and the
reclassifier valid at `subjectLevel + 1` (the tarskiDecode `+1`) under the SAME `contextLevels`, it produces
the reclassified validity.  The real work of COORDINATING the two sub-derivation bridges to a shared
`contextLevels` and to the `subjectLevel`/`subjectLevel + 1` levels is the induction step's responsibility
(deferred to the assembly, SN-027); this lemma fixes the arm's target shape.

## Zero-axiom verification

Three direct `ValidTyping` constructor applications wrapped in existentials; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Leveling-bridge var arm.**  A variable cell bridges to `ValidTyping` at its OWN context level
(`subjectLevel := contextLevels index`), unconditionally — the off-by-one-free var leg (SN-024). -/
theorem validTypingBridgeVar {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) (index : Fin scope) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (variableCell index) (context.lookup index) :=
  ⟨_, ValidTyping.var contextLevels context index⟩

/-- **Leveling-bridge universeFormation arm.**  A universe code bridges to `ValidTyping.universeFormation`
at a positive level (here `predLevel := 0`, so `subjectLevel := 1`), with the `lsucc` classifier,
unconditionally. -/
theorem validTypingBridgeUniverseFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  ⟨_, ValidTyping.universeFormation contextLevels 0 context levelExpr flag⟩

/-- **Leveling-bridge conv arm (coordinated inputs).**  Given the subject valid at `subjectLevel` and the
reclassifier valid at `subjectLevel + 1` (the tarskiDecode `+1`) under the SAME `contextLevels`, the
reclassified subject is valid (at `subjectLevel`).  The cross-sub-derivation coordination that produces these
inputs at a shared `contextLevels` is the inductive assembly's job (SN-027); this fixes the conv arm's
target shape. -/
theorem validTypingBridgeConv {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped : ValidTyping profile contextLevels (subjectLevel + 1) context
      reclassifier (universeCodeCell levelExpr flag)) :
    ∃ resultLevel : Nat,
      ValidTyping profile contextLevels resultLevel context subject reclassifier :=
  ⟨_, ValidTyping.conv contextLevels subjectLevel typed converts reclassifierTyped⟩

end FX1Poly.Typed
