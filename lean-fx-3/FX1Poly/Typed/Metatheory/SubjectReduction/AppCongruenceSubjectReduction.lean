import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence
import FX1Poly.Typed.Engine.Union.HasTypeUnionAppInversion
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/AppCongruenceSubjectReduction
    — the `app` eliminator congruence subject reduction (the first arm of gate 2, TYTAB-2-FT-SR #1740)

The native eliminator-congruence subject reduction (`UnionElimCongruenceClosesToEmptyType`, gate 2 of the
consistency leg #1697) re-types an eliminator cell when one of its children steps.  The standalone gate has
NO induction hypothesis, so the principled vehicle is the GENERAL congruence closer proven by induction over
the typing derivation: its `ihPremises` supply the single-step subject reduction for each obligation's
subject — the per-child IH the elim arm consumes.  This file ships that arm for the MOST IMPORTANT
eliminator, `gen_app` (function application), as the two standalone child-congruence lemmas the eventual
induction feeds with its IH.

For an `appCell functionTerm argument` typed at `classifier`, the two child positions are the function and
the argument.  Each lemma takes:

  * `wellFormed` — the context well-formedness presupposition (threaded by the eventual congruence induction,
    exactly as `congruenceClosesToEmptyTypeAux` threads `WfContextDescPi`); needed to reclassify the stepped
    child back through validity;
  * `typed` — the `app` cell's typing;
  * the child step (`functionStep` / `argumentStep`);
  * `childSubjectReduction` — the single-step subject reduction for the stepped child (the IH).

The proof is uniform: invert the `app` typing (`invertAtAppHead`) to recover the function at its Π code, the
argument at the domain code, and the classifier convertible to the dependent output `subst0 codomainCode
argument`; re-type the stepped child by the IH; reclassify it back to its original (convertible) classifier
through validity (`classifierIsType` + `reclassifyToType`); rebuild the `app` cell (`unionAppCellTyped`); and
land the output `Conv`.

  * **function step** — the function does NOT occur in the output type `subst0 codomainCode argument`, so the
    output is literally unchanged: `pinned = subst0 codomainCode argument`, `Conv classifier pinned` is the
    inversion's conversion leg directly.
  * **argument step** — the argument DOES occur in the output, so the output drifts to `subst0 codomainCode
    argumentReduct`; the drift is `Conv`-bridged by `subst0_isConvStableUnderArgumentStep` (ElimOutput-
    TypeCongruence, ingredient (2)) and composed with the inversion's conversion leg by `Conv.trans`.

## Zero-axiom verification

`invertAtAppHead` / `classifierIsType` / `reclassifyToType` / `unionAppCellTyped` /
`subst0_isConvStableUnderArgumentStep` (all shipped, zero-axiom) composed with `Conv.trans` / `Conv.sym`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The `app` congruence subject reduction at the FUNCTION position.**  When the function child of a typed
`appCell` steps, the reformed cell re-types at the SAME classifier-convertible output: the function does not
occur in the dependent output type `subst0 codomainCode argument`, so the inversion's conversion leg
discharges the result `Conv` unchanged.  The stepped function is re-typed by the IH
(`childSubjectReduction`) and reclassified back to its Π code through validity. -/
theorem HasTypeUnion.appFunctionCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm functionReduct argument classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (appCell functionTerm argument) classifier)
    (functionStep : Step functionTerm functionReduct)
    (childSubjectReduction : ∀ {subterm reduct subtermType : RawTerm scope},
      HasTypeUnion profile context subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm scope,
          HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (appCell functionReduct argument) pinned ∧
      Conv classifier pinned := by
  obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, classifierConv⟩ :=
    HasTypeUnion.invertAtAppHead typed rfl
  obtain ⟨functionReductType, functionReductTyped, functionTypeConv⟩ :=
    childSubjectReduction functionTyped functionStep
  have piIsType : UnionClassifierIsType profile context (piTyCodeCell domainCode codomainCode) :=
    HasTypeUnion.classifierIsType functionTyped wellFormed
  have functionReductAtPi :
      HasTypeUnion profile context functionReduct (piTyCodeCell domainCode codomainCode) :=
    HasTypeUnion.reclassifyToType functionReductTyped functionTypeConv.sym piIsType
  exact ⟨RawTerm.subst0 codomainCode argument,
    unionAppCellTyped functionReduct argument domainCode codomainCode functionReductAtPi argumentTyped,
    classifierConv⟩

/-- **The `app` congruence subject reduction at the ARGUMENT position.**  When the argument child of a typed
`appCell` steps, the reformed cell re-types at a classifier-convertible output: the argument occurs in the
dependent output `subst0 codomainCode argument`, so the output drifts to `subst0 codomainCode argumentReduct`;
the drift is `Conv`-bridged by `subst0_isConvStableUnderArgumentStep` and composed with the inversion's
conversion leg.  The stepped argument is re-typed by the IH (`childSubjectReduction`) and reclassified back to
the domain code through validity. -/
theorem HasTypeUnion.appArgumentCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument argumentReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (appCell functionTerm argument) classifier)
    (argumentStep : Step argument argumentReduct)
    (childSubjectReduction : ∀ {subterm reduct subtermType : RawTerm scope},
      HasTypeUnion profile context subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm scope,
          HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (appCell functionTerm argumentReduct) pinned ∧
      Conv classifier pinned := by
  obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, classifierConv⟩ :=
    HasTypeUnion.invertAtAppHead typed rfl
  obtain ⟨argumentReductType, argumentReductTyped, argumentTypeConv⟩ :=
    childSubjectReduction argumentTyped argumentStep
  have domainIsType : UnionClassifierIsType profile context domainCode :=
    HasTypeUnion.classifierIsType argumentTyped wellFormed
  have argumentReductAtDomain :
      HasTypeUnion profile context argumentReduct domainCode :=
    HasTypeUnion.reclassifyToType argumentReductTyped argumentTypeConv.sym domainIsType
  have outputConv :
      Conv (RawTerm.subst0 codomainCode argument) (RawTerm.subst0 codomainCode argumentReduct) :=
    subst0_isConvStableUnderArgumentStep codomainCode argumentStep
  exact ⟨RawTerm.subst0 codomainCode argumentReduct,
    unionAppCellTyped functionTerm argumentReduct domainCode codomainCode functionTyped
      argumentReductAtDomain,
    Conv.trans classifierConv outputConv⟩

end FX1Poly.Typed
