import FX1Poly.Typed.StandaloneEngineCanonicity
import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.GrownFormerClassifierConv
import FX1Poly.Typed.EmptyTypeValueInversion
import FX1Poly.Typed.ConvBoolCodeRigidity

/-! # FX1Poly/Typed/CombinedBoolCanonicalForms — closed-NORMAL bool canonical forms over ALL THREE
    typing engines (CANON-1 #1048: the grown disjunct ruled out, unconditionally).

`StandaloneEngineCanonicity.standaloneBoolCanonicalForms` (#1063) settled the two STANDALONE engines: a
closed term typed at `boolTypeCell` by `HasTypeDescDataIntro` (data values) or `HasTypeDescBaseType` (base
type codes) is `boolTrueCell` / `boolFalseCell`.  The remaining CANON-1 residual was the GROWN engine
`HasTypeDescPi`: could it type some closed term at `boolTypeCell` that ISN'T a Boolean value?

This file answers NO — for NORMAL subjects, **unconditionally** (no GCC-5 #842, no §5 candidate bridge
#768).  The grown engine is formation-only for data: it never introduces `boolTrue` / `boolFalse`
(`HasTypeDescPi.boolTrueCellHasNoTyping`), and its closed-normal canonical forms
(`closedNormalSubjectHead`) are exactly the SIX heads `gen_lam` / `gen_piTyCode` / `gen_sigmaTyCode` /
`gen_universeCode` / `gen_listCode` / `gen_optionCode`.  At the `boolTypeCell` classifier:

  * a λ's classifier is `Conv` a Π-code (`invertLam`), and `boolTypeCell` is not `Conv` a Π-code
    (`Conv.boolTypeCell_not_piTyCode`);
  * every type FORMER's classifier is `Conv` a universe code (the former inversions /
    `formerClassifierConvUniverseGeneric`), and `boolTypeCell` is not `Conv` a universe code
    (`Conv.boolTypeCell_not_universeCode`).

So NO closed-normal grown term inhabits `boolTypeCell` — the grown disjunct is vacuous.  Why
unconditional: the classifier is read only at an ALREADY-normal subject (we invert the typing of a normal
term; we never TYPE a reduction step), so no subject reduction — hence no grown context-conversion
`piElim` arm (#842) — is invoked.  This mirrors `noClosedNormalTermAtEmptyType` (the SN-050 normal-form
half), the empty-type twin of this bool-type rule-out.

  * **`HasTypeDescPi.{lambda,piFormer,sigmaFormer,universeCode,listFormer,optionFormer}NotTypedAtBoolType`**
    — the six per-head refutations (the `boolTypeCell` analogues of the `*NotTypedAtEmptyType` family).
  * **`HasTypeDescPi.noClosedNormalTermAtBoolType` (★)** — no closed-normal grown term is typed at
    `boolTypeCell`, by cases on `closedNormalSubjectHead`.
  * **`closedNormalBoolCanonicalForms` (★)** — combined: a closed-NORMAL term typed at `boolTypeCell` by
    ANY of the three engines is `boolTrueCell` / `boolFalseCell`.  The grown disjunct is ruled out; the two
    standalone disjuncts delegate to `standaloneBoolCanonicalForms`.

## The residual after this

The ONLY gap remaining for full closed canonicity (every closed `t : boolCode` is a Boolean value, not
just every NORMAL one) is reducing an arbitrary closed `t` to its normal form WHILE preserving the
`boolTypeCell` classifier — i.e. grown SN (`SN-043`, shipped) plus the master subject-reduction dispatcher
(`SN-055` / `#842`, the GCC-5-gated blocker).  This file precisely localizes that dependency: canonicity
for NORMAL subjects is unconditional; only the "reduce-to-normal" step needs SR.

## Zero-axiom

The six refutations mirror the `*NotTypedAtEmptyType` family (one grown inversion + a `Conv` rigidity
lemma); the headline cases `closedNormalSubjectHead` (the shipped grown closed-canonical-forms recursor) and
dispatches; the combined theorem reuses `standaloneBoolCanonicalForms` + `Generator.noConfusion`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A λ is never typed at `boolCode`.**  `invertLam` exposes the λ's classifier as `Conv` a Π-code;
`Conv.boolTypeCell_not_piTyCode` refutes that against `boolTypeCell`.  The `boolType` analogue of
`lambdaNotTypedAtEmptyType` (context-free — the λ inversion needs no well-formedness). -/
theorem HasTypeDescPi.lambdaNotTypedAtBoolType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    (typed : HasTypeDescPi profile context (lamCell body) (boolTypeCell : RawTerm scope)) :
    False := by
  obtain ⟨_domainCode, _codomainCode, _domainLevel, _codomainLevel, _flag,
      convToPiCode, _domainTyped, _codomainTyped, _bodyTyped⟩ := HasTypeDescPi.invertLam typed
  exact Conv.boolTypeCell_not_piTyCode convToPiCode

/-- **A Π-type former is never typed at `boolCode`.**  `invertPiTyCode` exposes the former's classifier as
`Conv` a universe code; `Conv.boolTypeCell_not_universeCode` refutes that against `boolTypeCell`.  The
`boolType` analogue of `piFormerNotTypedAtEmptyType`. -/
theorem HasTypeDescPi.piFormerNotTypedAtBoolType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
        (boolTypeCell : RawTerm scope)) :
    False := by
  obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped, convToUniverseCode⟩ :=
    HasTypeDescPi.invertPiTyCode typed
  exact Conv.boolTypeCell_not_universeCode convToUniverseCode

/-- **A Σ-type former is never typed at `boolCode`** — the Σ dual of `piFormerNotTypedAtBoolType`. -/
theorem HasTypeDescPi.sigmaFormerNotTypedAtBoolType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode)
        (boolTypeCell : RawTerm scope)) :
    False := by
  obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped, convToUniverseCode⟩ :=
    HasTypeDescPi.invertSigmaTyCode typed
  exact Conv.boolTypeCell_not_universeCode convToUniverseCode

/-- **A universe code is never typed at `boolCode`.**  `inversionUniverseCode` exposes the code's classifier
as `Conv` the next universe; `Conv.boolTypeCell_not_universeCode` refutes that against `boolTypeCell`.  The
`boolType` analogue of `universeCodeNotTypedAtEmptyType`. -/
theorem HasTypeDescPi.universeCodeNotTypedAtBoolType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed :
      HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (boolTypeCell : RawTerm scope)) :
    False :=
  Conv.boolTypeCell_not_universeCode (HasTypeDescPi.inversionUniverseCode typed)

/-- **A `listCode` data former is never typed at `boolCode`.**  Via the head-agnostic
`formerClassifierConvUniverseGeneric`: a `List element` classifier is `Conv` a universe code, refuted against
`boolTypeCell` by `Conv.boolTypeCell_not_universeCode`.  The `boolType` analogue of
`listFormerNotTypedAtEmptyType`. -/
theorem HasTypeDescPi.listFormerNotTypedAtBoolType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {element : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (.mkGen .gen_listCode () (.childCons element .childNil))
        (boolTypeCell : RawTerm scope)) :
    False := by
  obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
    HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_listCode rfl
  exact Conv.boolTypeCell_not_universeCode convToUniverseCode

/-- **An `optionCode` data former is never typed at `boolCode`** — the one-child option twin of
`listFormerNotTypedAtBoolType`, via `formerClassifierConvUniverseGeneric` + `typingRuleDescOf_optionCode`. -/
theorem HasTypeDescPi.optionFormerNotTypedAtBoolType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {element : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (.mkGen .gen_optionCode () (.childCons element .childNil))
        (boolTypeCell : RawTerm scope)) :
    False := by
  obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
    HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_optionCode rfl
  exact Conv.boolTypeCell_not_universeCode convToUniverseCode

/-- **★ No closed-NORMAL grown term is typed at `boolCode`.**  Grown bool-type vacuity: by the closed
canonical forms (`closedNormalSubjectHead`) the subject is λ / Π / Σ / universe / list / option, each refuted
at `boolTypeCell` by the per-head `*NotTypedAtBoolType` lemmas.  No subject reduction needed (the classifier
is read only at the already-normal subject) — so unconditional on GCC-5 / §5.  The grown disjunct of
combined bool canonicity is empty for normal subjects; full canonicity adds grown SN (SN-043, shipped) plus
the SR dispatcher (SN-055 / #842) to reduce an arbitrary closed `t : boolCode` to its normal form. -/
theorem HasTypeDescPi.noClosedNormalTermAtBoolType {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (boolTypeCell : RawTerm 0))
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed normal
      (fun emptyIndex => emptyIndex.elim0) with
      headLam | headPi | headSigma | headUniverse | headList | headOption
  · obtain ⟨_body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
    rw [bodyEq] at typed
    exact HasTypeDescPi.lambdaNotTypedAtBoolType typed
  · obtain ⟨_domain, _codomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
    rw [piEq] at typed
    exact HasTypeDescPi.piFormerNotTypedAtBoolType typed
  · obtain ⟨_domain, _codomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
    rw [sigmaEq] at typed
    exact HasTypeDescPi.sigmaFormerNotTypedAtBoolType typed
  · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
    rw [universeEq] at typed
    exact HasTypeDescPi.universeCodeNotTypedAtBoolType typed
  · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
    rw [listEq] at typed
    exact HasTypeDescPi.listFormerNotTypedAtBoolType typed
  · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
    rw [optionEq] at typed
    exact HasTypeDescPi.optionFormerNotTypedAtBoolType typed

/-- **★ Combined closed-NORMAL bool canonical forms over all three engines.**  A closed NORMAL term typed at
`boolTypeCell` by `HasTypeDescDataIntro` OR `HasTypeDescBaseType` OR `HasTypeDescPi` is `boolTrueCell` /
`boolFalseCell`.  The two standalone disjuncts delegate to `standaloneBoolCanonicalForms` (#1063); the grown
disjunct is ruled out by `noClosedNormalTermAtBoolType` (vacuous — the grown engine has no closed-normal
inhabitant of `boolCode`).  Unconditional: no GCC-5, no §5.  The CANON-1 (#1048) normal-subject headline —
the closed-normal inhabitants of `boolCode` across the whole kernel are exactly the two Boolean values. -/
theorem closedNormalBoolCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    subject = boolTrueCell ∨ subject = boolFalseCell := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped
  · exact standaloneBoolCanonicalForms (Or.inl dataIntroTyped)
  · exact standaloneBoolCanonicalForms (Or.inr baseTypeTyped)
  · exact (HasTypeDescPi.noClosedNormalTermAtBoolType grownTyped normal).elim

end FX1Poly.Typed
