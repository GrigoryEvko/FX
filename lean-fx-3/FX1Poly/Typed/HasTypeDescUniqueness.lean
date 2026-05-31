import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.HasTypeInversion

/-! # FX1Poly/Typed/HasTypeDescUniqueness — uniqueness of typing (P7) for the
    description engine.

polycell.md §11.8.5 P7 ("uniqueness of typing"): any two classifiers a cell receives
are convertible.  P7 disciplines the design (it makes `infer` well-defined) and is
consumed by the typechecker's conv-check and by canonicity.

## Intrinsic spine, bespoke leaf (honest scope)

`HasTypeDesc.uniqueness` is a recursion on `HasTypeDesc` ITSELF (the propext-free
term-mode `match`).  ALL FOUR arms now reason through the description engine's own
structure:

* `var` / `universeFormation` invert the SECOND derivation with the INTRINSIC leaf
  inversions and `.sym`;
* `conv` recurses INTRINSICALLY through `Conv.trans_of_typedMiddle`;
* `genFormation` inverts the SECOND derivation with the INTRINSIC
  `inversion{Pi,Sigma}CodeWithConvGeneral`, then forces the two formation telescopes to
  agree on `levels`/`flag` via `DescTelescope.uniquenessAgree`, after which both
  classifiers reduce to the SAME canonical universe code.

The remaining coupling is ONE LEAF: `uniquenessAgree` settles each HEAD CHILD's
universe level/flag through the verified bespoke `HasType.uniqueness` (via
`HasTypeDesc.toHasType`), because as a STANDALONE (non-mutual) recursion it cannot call
the intrinsic uniqueness it precedes.  The fully intrinsic version makes the two a
MUTUAL recursion (the `HasTypeDesc.toHasType`/`DescTelescope.toHasTypeTelescope` shape)
so head children recurse into the intrinsic uniqueness; that mutual block is the
decouple's last step (its termination needs the careful scope-index phrasing of the
soundness pair).  The formation SPINE — inversion + telescope agreement — is now
intrinsic; only the per-child leaf is bespoke.

## `uniquenessAgree`: separate children + a threaded equality

The earlier blocker was deconstructing the SECOND telescope when its children index was
UNIFIED with the first's (forced `childCons head rest`), which makes `cases`/`rcases`
field alignment unpredictable.  The fix is the equation-motive recipe: give the two
telescopes SEPARATE free children (`children1`, `children2`) and thread an explicit
`children1 = children2`.  Each telescope then matches cleanly (free children, like
`DescTelescope.toHasTypeTelescope`), and the equality connects them via `injection`
(cons/cons) / `RawTermChildren.noConfusion` (the impossible nil/cons cross-cases).

## The `levels1 ≠ []` flag guard

A `nil` telescope leaves its `flag` unconstrained, so `flag1 = flag2` is FALSE for two
empty telescopes with distinct flags; the flag is pinned only by the HEAD child.  So
`uniquenessAgree` concludes `levels1 = levels2 ∧ (levels1 ≠ [] → flag1 = flag2)` —
nil-safe, and `genFormation` discharges the guard since formation children are
non-empty.

## Zero-axiom

Term-mode recursion + the shipped propext-free inversions + `injection` /
`RawTermChildren.noConfusion` + the verified `Conv.trans_of_typedMiddle` /
`HasType.uniqueness` / `levelFlag_eq_of_conv_universeCodeCell`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Two formation telescopes over CONVERTIBLY-EQUAL children agree on `levels`, and —
when non-empty — on `flag`.  STANDALONE recursion on the first telescope; the two
telescopes carry SEPARATE free children joined by `childrenEq`, so each matches cleanly
(no forced-index `cases` misalignment).  Each head child's level/flag is settled by the
verified bespoke `HasType.uniqueness` (the one remaining leaf coupling). -/
theorem DescTelescope.uniquenessAgree {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels1 levels2 : List LevelExpr} {flag1 flag2 : UniverseFlag}
    {children1 children2 : RawTermChildren binderShifts baseScope}
    (telescope1 : DescTelescope profile context levels1 flag1 children1)
    (telescope2 : DescTelescope profile context levels2 flag2 children2)
    (wellFormed : WfContext context) :
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
            Conv (universeCodeCell headLevel1 flag1)
              (universeCodeCell headLevel2 flag2) :=
          HasType.uniqueness wellFormed
            (HasTypeDesc.toHasType headTyped1) (HasTypeDesc.toHasType headTyped2)
        obtain ⟨headLevelEq, flagEq⟩ :=
          levelFlag_eq_of_conv_universeCodeCell (context := context) headConv
        obtain ⟨restLevelsEq, _restFlagImplication⟩ :=
          DescTelescope.uniquenessAgree restTyped1 restTyped2
            (WfContext.cons wellFormed
              ⟨headLevel1, flag1, HasTypeDesc.toHasType headTyped1⟩) rfl
        exact ⟨by rw [headLevelEq, restLevelsEq], fun _ => flagEq⟩

/-- **Uniqueness of typing (P7).**  Any two classifiers a description-engine cell
receives are convertible.  Recursion on the FIRST derivation; every arm reasons through
the description engine's own structure (the head children of `genFormation` are settled
by the bespoke `HasType.uniqueness` via `uniquenessAgree` — the one remaining leaf
coupling; see the module docstring). -/
theorem HasTypeDesc.uniqueness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject firstClassifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject firstClassifier)
    (wellFormed : WfContext context) :
    ∀ {secondClassifier : RawTerm scope},
      HasTypeDesc profile context subject secondClassifier →
        Conv firstClassifier secondClassifier :=
  match derivation with
  | .var _context _index => fun secondDerivation =>
      (HasTypeDesc.inversionVariable secondDerivation wellFormed).sym
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      fun secondDerivation =>
        Conv.trans_of_typedMiddle
          (HasType.classifierIsType wellFormed (HasTypeDesc.toHasType typedPremise))
          converts.sym
          (HasTypeDesc.uniqueness typedPremise wellFormed secondDerivation)
  | .universeFormation _context _levelExpr _flag => fun secondDerivation =>
      (HasTypeDesc.inversionUniverseCode secondDerivation wellFormed).sym
  | .genFormation _context generator _payload _children levels flag rule
      isFormation premises => fun secondDerivation => by
      by_cases hPi : generator = .gen_piTyCode
      · subst hPi
        have hRule : rule = { outputType := universeFormerOutput } :=
          Option.some.inj isFormation.symm
        subst hRule
        obtain ⟨secondLevels, secondFlag, secondTelescope, secondConv⟩ :=
          HasTypeDesc.inversionPiCodeWithConvGeneral secondDerivation wellFormed rfl
        obtain ⟨levelsEq, flagImplication⟩ :=
          DescTelescope.uniquenessAgree premises secondTelescope wellFormed rfl
        have levelsNonEmpty : levels ≠ [] := by
          cases premises; exact List.cons_ne_nil _ _
        have flagEq : flag = secondFlag := flagImplication levelsNonEmpty
        rw [levelsEq, flagEq]
        exact secondConv.sym
      · by_cases hSigma : generator = .gen_sigmaTyCode
        · subst hSigma
          have hRule : rule = { outputType := universeFormerOutput } :=
            Option.some.inj isFormation.symm
          subst hRule
          obtain ⟨secondLevels, secondFlag, secondTelescope, secondConv⟩ :=
            HasTypeDesc.inversionSigmaCodeWithConvGeneral secondDerivation wellFormed rfl
          obtain ⟨levelsEq, flagImplication⟩ :=
            DescTelescope.uniquenessAgree premises secondTelescope wellFormed rfl
          have levelsNonEmpty : levels ≠ [] := by
            cases premises; exact List.cons_ne_nil _ _
          have flagEq : flag = secondFlag := flagImplication levelsNonEmpty
          rw [levelsEq, flagEq]
          exact secondConv.sym
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg hPi, if_neg hSigma] at isFormation
          contradiction

end FX1Poly.Typed
