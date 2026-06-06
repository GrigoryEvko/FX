import FX1Poly.Typed.HasTypeDescUniqueness
import FX1Poly.Typed.WfContextDescLookup

/-! # FX1Poly/Typed/WfContextDescUniqueness — uniqueness of typing (P7) over WfContextDesc (HasType-free)

`HasTypeDesc.uniqueness` (`HasTypeDescUniqueness.lean`) proves P7 — any two classifiers a cell receives are
convertible — but its `genFormation` leaf bottoms out in `DescTelescope.uniquenessAgree`, which settles each
head child's level/flag through the verified bespoke `HasType.uniqueness` oracle (because, as a STANDALONE
non-mutual recursion, it cannot call the intrinsic uniqueness it precedes) AND extends the context via
`WfContext.cons`, demanding a bespoke `IsType` binding (`HasTypeDesc.toHasType` of the head typing).  Both are
`HasType` couplings, inherent to that leaf being standalone + `WfContext`-threaded.

This file ships the HasType-FREE twin over the `WfContextDesc` substrate, as a genuine MUTUAL recursion
`uniquenessNative` / `uniquenessAgreeNative` (the `toHasType` / `toHasTypeTelescope` shape): the head child
recurses into `uniquenessNative` itself (no `HasType.uniqueness` oracle), and the rest-telescope recursion
extends the context via `WfContextDesc.cons`, whose `IsTypeDesc` binding IS the head typing directly (no
`HasTypeDesc.toHasType`).  The arms invert the second derivation with the formation inversions, now param-free
(HT-A2-inv-drop dropped their vacuous `WfContext`).  So the whole mutual pair contains no `HasType`.  The
migration TARGET that supersedes `HasTypeDesc.uniqueness` once consumers thread `WfContextDesc`; canonical after
the bespoke engine is deleted (HT-C).

## Mutual structure (the `toHasType` shape)

  * `uniquenessNative` — recursion on the FIRST derivation: `var` / `universeFormation` invert the second
    derivation with `inversionVariable` / `inversionUniverseCode` and `.sym`; `conv` recurses via the
    unconditional raw `Conv.trans`; `genFormation` inverts the second via `inversionFormerWithConvGeneric`,
    forces telescope agreement via `uniquenessAgreeNative`, and the classifiers reduce to the same canonical
    universe code.
  * `uniquenessAgreeNative` — STANDALONE-shaped recursion on the first telescope, but MUTUAL with
    `uniquenessNative`: each head child's level/flag is settled by `uniquenessNative` (the head child is a
    structural sub-derivation), and the rest extends via `WfContextDesc.cons` with the head typing as the
    `IsTypeDesc` binding.  Equation-`match` form so the mutual recursion is recognised structural.

## Zero-axiom verification

Term-mode mutual recursion + the param-free propext-free inversions + `injection` /
`RawTermChildren.noConfusion` + the unconditional raw `Conv.trans` + `levelFlag_eq_of_conv_universeCodeCell` +
`WfContextDesc.cons` (the `IsTypeDesc` binding is the head typing itself).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

mutual

/-- **Uniqueness of typing (P7) over `WfContextDesc`, HasType-free.**  Any two classifiers a description-engine
cell receives are convertible.  Recursion on the FIRST derivation; the `genFormation` head children are settled
by `uniquenessNative` itself (mutual with `uniquenessAgreeNative`), so there is no `HasType.uniqueness` oracle.
The migration target superseding `HasTypeDesc.uniqueness` once consumers thread `WfContextDesc`. -/
theorem HasTypeDesc.uniquenessNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject firstClassifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject firstClassifier)
    (wellFormed : WfContextDesc context) :
    ∀ {secondClassifier : RawTerm scope},
      HasTypeDesc profile context subject secondClassifier →
        Conv firstClassifier secondClassifier :=
  match derivation with
  | .var _context _index => fun secondDerivation =>
      (HasTypeDesc.inversionVariable secondDerivation).sym
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      fun secondDerivation =>
        Conv.trans converts.sym
          (HasTypeDesc.uniquenessNative typedPremise wellFormed secondDerivation)
  | .universeFormation _context _levelExpr _flag => fun secondDerivation =>
      (HasTypeDesc.inversionUniverseCode secondDerivation).sym
  | .genFormation _context generator _payload _children levels flag rule
      isFormation premises => fun secondDerivation => by
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        formationRuleIsUniverseFormer isFormation
      obtain ⟨secondLevels, secondFlag, secondTelescope, secondConv⟩ :=
        HasTypeDesc.inversionFormerWithConvGeneric secondDerivation isFormation rfl
      obtain ⟨levelsEq, flagImplication⟩ :=
        DescTelescope.uniquenessAgreeNative premises secondTelescope wellFormed rfl
      have levelsNonEmpty : levels ≠ [] :=
        DescTelescope.levels_ne_nil_of_isFormation isFormation premises
      have flagEq : flag = secondFlag := flagImplication levelsNonEmpty
      rw [levelsEq, flagEq]
      exact secondConv.sym

/-- Two formation telescopes over CONVERTIBLY-EQUAL children agree on `levels`, and — when non-empty — on
`flag`, over `WfContextDesc`, HasType-free.  STANDALONE-shaped recursion on the first telescope but MUTUAL with
`uniquenessNative`: each head child's level/flag is settled by `uniquenessNative` (the head child is a structural
sub-derivation), replacing the bespoke `HasType.uniqueness` oracle; the rest extends via `WfContextDesc.cons`
whose `IsTypeDesc` binding is the head typing itself (no `HasTypeDesc.toHasType`). -/
theorem DescTelescope.uniquenessAgreeNative {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels1 levels2 : List LevelExpr} {flag1 flag2 : UniverseFlag}
    {children1 children2 : RawTermChildren binderShifts baseScope}
    (telescope1 : DescTelescope profile context levels1 flag1 children1)
    (telescope2 : DescTelescope profile context levels2 flag2 children2)
    (wellFormed : WfContextDesc context) :
    children1 = children2 → levels1 = levels2 ∧ (levels1 ≠ [] → flag1 = flag2) :=
  match telescope1, telescope2 with
  | .nil _ _, .nil _ _ => fun _ =>
      ⟨rfl, fun emptyContradiction => absurd rfl emptyContradiction⟩
  | .cons _ head1 headLevel1 restLevels1 flag1 rest1 headTyped1 restTyped1,
    .cons _ head2 headLevel2 restLevels2 flag2 rest2 headTyped2 restTyped2 =>
      fun childrenEq => by
        injection childrenEq with _headScopeEq _headDepthEq _restShiftsEq headTermEq restTermEq
        subst headTermEq
        subst restTermEq
        have headConv :
            Conv (universeCodeCell headLevel1 flag1) (universeCodeCell headLevel2 flag2) :=
          HasTypeDesc.uniquenessNative headTyped1 wellFormed headTyped2
        obtain ⟨headLevelEq, flagEq⟩ :=
          levelFlag_eq_of_conv_universeCodeCell (context := context) headConv
        obtain ⟨restLevelsEq, _restFlagImplication⟩ :=
          DescTelescope.uniquenessAgreeNative restTyped1 restTyped2
            (WfContextDesc.cons wellFormed ⟨headLevel1, flag1, headTyped1⟩) rfl
        exact ⟨by rw [headLevelEq, restLevelsEq], fun _ => flagEq⟩

end

end FX1Poly.Typed
