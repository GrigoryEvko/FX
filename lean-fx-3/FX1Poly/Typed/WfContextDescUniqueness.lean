import FX1Poly.Typed.HasTypeDescUniqueness
import FX1Poly.Typed.WfContextDescLookup
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/WfContextDescUniqueness — uniqueness of typing (P7) over WfContextDesc

Uniqueness of typing (P7 — any two classifiers a cell receives are convertible) over the `WfContextDesc`
substrate, as a genuine MUTUAL recursion `uniquenessNative` / `uniquenessAgreeNative`: the head child recurses
into `uniquenessNative` itself, and the rest-telescope recursion extends the context via `WfContextDesc.cons`,
whose `IsTypeDesc` binding IS the head typing directly.  The arms invert the second derivation with the
formation inversions, param-free.  The canonical uniqueness, threaded by consumers over `WfContextDesc`.

## Mutual structure (`uniquenessNative` / `uniquenessAgreeNative`)

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
`RawTermChildren.noConfusion` + the unconditional raw `Conv.trans` + `universeCodeCell_inj_of_conv` +
`WfContextDesc.cons` (the `IsTypeDesc` binding is the head typing itself).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

mutual

/-- **Uniqueness of typing (P7) over `WfContextDesc`.**  Any two classifiers a description-engine
cell receives are convertible.  Recursion on the FIRST derivation; the `genFormation` head children are settled
by `uniquenessNative` itself (mutual with `uniquenessAgreeNative`).  The canonical uniqueness, threaded by
consumers over `WfContextDesc`. -/
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
      by_cases isNullary : generator = Generator.gen_unitCode
      · -- the nullary row: uniqueness by output CONSTANCY — the telescope anchors no flag, but
        -- every classification of the cell reaches the one pinned output
        subst isNullary
        rw [typingRuleDescOf_unitCode_outputConstant isFormation]
        exact (HasTypeDesc.inversionFormerClassifierPinned secondDerivation isFormation
          (typingRuleDescOf_unitCode_outputConstant isFormation _) rfl).sym
      · -- the >=1-child rows: uniqueness by telescope flag-anchoring at the head child
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          formationRuleIsUniverseFormer isFormation isNullary
        obtain ⟨secondLevels, secondFlag, secondTelescope, secondConv⟩ :=
          HasTypeDesc.inversionFormerWithConvGeneric secondDerivation isFormation rfl
        obtain ⟨levelsEq, flagImplication⟩ :=
          DescTelescope.uniquenessAgreeNative premises secondTelescope wellFormed rfl
        have levelsNonEmpty : levels ≠ [] :=
          DescTelescope.levels_ne_nil_of_isFormation isFormation isNullary premises
        have flagEq : flag = secondFlag := flagImplication levelsNonEmpty
        rw [levelsEq, flagEq]
        exact secondConv.sym

/-- Two formation telescopes over CONVERTIBLY-EQUAL children agree on `levels`, and — when non-empty — on
`flag`, over `WfContextDesc`.  STANDALONE-shaped recursion on the first telescope but MUTUAL with
`uniquenessNative`: each head child's level/flag is settled by `uniquenessNative` (the head child is a structural
sub-derivation); the rest extends via `WfContextDesc.cons` whose `IsTypeDesc` binding is the head typing
itself. -/
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
          universeCodeCell_inj_of_conv headConv
        obtain ⟨restLevelsEq, _restFlagImplication⟩ :=
          DescTelescope.uniquenessAgreeNative restTyped1 restTyped2
            (WfContextDesc.cons wellFormed ⟨headLevel1, flag1, headTyped1⟩) rfl
        exact ⟨by rw [headLevelEq, restLevelsEq], fun _ => flagEq⟩

end

end FX1Poly.Typed
