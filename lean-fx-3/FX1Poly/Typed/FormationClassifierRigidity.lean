import FX1Poly.Typed.UnitReadbackAnnotationBoundary
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/FormationClassifierRigidity
   — ★ brick 8, a POSITIVE verdict: literal classifier matching is COMPLETE (#481)

The mandated post-brick-7 completeness re-analysis targeted the remaining LITERAL-match sites:
`asPiCode? classifier` in the readback and `asPiCode? (context.lookup index)` in the spine —
the suspected 10th-boundary family was "classifiers/lookups that merely CONVERT to Π codes
fall to the collapse" (the standing honest-boundary note since brick 1).  The analysis closes
the family EMPTY, as theorems:

  * **Formation subjects are step-free** (`subjectAdmitsNoStep`, shipped): the formation engine
    has no `piIntro`/`piElim` arms, so formation-typed terms are app-free former/variable/
    universe trees — no redex anywhere, β/ι-NORMAL by construction.
  * **Rigidity** (`formationSubjects_convRigid`): `Conv`-related formation subjects are EQUAL —
    `Conv.eq_of_noStep` on two step-free endpoints.
  * **Π-detection completeness** (`piCodeDetection_completeOnFormationClassifiers`): a
    formation-typed classifier `Conv` to ANY Π code literally IS a Π code (with `Conv`-related
    components — which the trust-the-classifier λ arm and the spine arm absorb).  Via
    `Conv.reducesToPiTyCode` + step-freeness collapsing the reduction chain.
  * **Lookup completeness** (`WfContextDesc.piCodeDetection_completeOnLookups`): under the wf
    presupposition every context entry is formation-typed IN THE SAME CONTEXT
    (`lookupIsTypeDesc`), so the spine arm's literal lookup match loses nothing either.
  * The unit arm's literal `classifier = unitTypeCell` test is likewise complete
    (`unitDetection_completeOnFormationClassifiers` — rigidity against the unit code).

CONSEQUENCE: within the soundness presupposition (classifier FORMATION-typed, context wf) the
readback's literal dispatch loses NOTHING — the 9th boundary's annotation-mismatch phenomenon
cannot recur at the classifier or lookup positions, because reducible type codes are not
formation-typable in the first place.  The standing honest-boundary note (2) is RETIRED.

## Zero-axiom verification

Pure composition of shipped pieces: `subjectAdmitsNoStep` + `Conv.eq_of_noStep` /
`StepStar.eq_of_noStep` + `Conv.reducesToPiTyCode` + `lookupIsTypeDesc`; the `asPiCode?` firing
lemma is `rfl` on the symbolic Π cell.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Formation subjects are `Conv`-rigid**: two formation-typed terms (any contexts, any
classifiers) related by `Conv` are EQUAL — both are step-free, so the join's common reduct is
both endpoints at once. -/
theorem HasTypeDesc.formationSubjects_convRigid {profile : PolyProfile} {scope : Nat}
    {leftContext rightContext : TypingContext profile scope}
    {leftSubject rightSubject leftClassifier rightClassifier : RawTerm scope}
    (leftTyped : HasTypeDesc profile leftContext leftSubject leftClassifier)
    (rightTyped : HasTypeDesc profile rightContext rightSubject rightClassifier)
    (converts : Conv leftSubject rightSubject) :
    leftSubject = rightSubject :=
  Conv.eq_of_noStep leftTyped.subjectAdmitsNoStep rightTyped.subjectAdmitsNoStep converts

/-- **Π-detection is complete on formation-typed classifiers**: a formation-typed classifier
`Conv` to a Π code IS literally a Π code, with `Conv`-related components.  The reduction chain
supplied by `Conv.reducesToPiTyCode` collapses against step-freeness. -/
theorem HasTypeDesc.piCodeDetection_completeOnFormationClassifiers {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {classifier reclassifier domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (classifierTyped : HasTypeDesc profile context classifier reclassifier)
    (converts : Conv classifier (piTyCodeCell domainCode codomainCode)) :
    ∃ (literalDomain : RawTerm scope) (literalCodomain : RawTerm (scope + 1)),
      classifier = piTyCodeCell literalDomain literalCodomain ∧
      Conv domainCode literalDomain ∧ Conv codomainCode literalCodomain := by
  obtain ⟨domainReduct, codomainReduct, classifierChain, domainConv, codomainConv⟩ :=
    Conv.reducesToPiTyCode converts
  have chainCollapses :=
    StepStar.eq_of_noStep classifierTyped.subjectAdmitsNoStep classifierChain
  exact ⟨domainReduct, codomainReduct, chainCollapses.symm, domainConv, codomainConv⟩

/-- `asPiCode?` fires on every literal Π cell — the symbolic computation lemma. -/
theorem asPiCode?_piTyCodeCell {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    asPiCode? (piTyCodeCell domainCode codomainCode) = some (domainCode, codomainCode) := rfl

/-- **The readback's Π arm fires on every formation-typed classifier `Conv` to a Π code** —
the operational form of the detection completeness. -/
theorem asPiCode?_firesOnFormationClassifiers {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {classifier reclassifier domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (classifierTyped : HasTypeDesc profile context classifier reclassifier)
    (converts : Conv classifier (piTyCodeCell domainCode codomainCode)) :
    ∃ (literalDomain : RawTerm scope) (literalCodomain : RawTerm (scope + 1)),
      asPiCode? classifier = some (literalDomain, literalCodomain) := by
  obtain ⟨literalDomain, literalCodomain, classifierIsPi, _, _⟩ :=
    HasTypeDesc.piCodeDetection_completeOnFormationClassifiers classifierTyped converts
  rw [classifierIsPi]
  exact ⟨literalDomain, literalCodomain, asPiCode?_piTyCodeCell literalDomain literalCodomain⟩

/-- **The spine arm's literal lookup match is complete under the wf presupposition**: every
context entry is formation-typed in the SAME context (`lookupIsTypeDesc`), so a lookup `Conv`
to a Π code literally IS one. -/
theorem WfContextDesc.piCodeDetection_completeOnLookups {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (contextWellFormed : WfContextDesc context) (index : Fin scope)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (converts : Conv (context.lookup index) (piTyCodeCell domainCode codomainCode)) :
    ∃ (literalDomain : RawTerm scope) (literalCodomain : RawTerm (scope + 1)),
      context.lookup index = piTyCodeCell literalDomain literalCodomain ∧
      Conv domainCode literalDomain ∧ Conv codomainCode literalCodomain := by
  obtain ⟨entryLevel, entryFlag, entryFormationTyped⟩ :=
    WfContextDesc.lookupIsTypeDesc context contextWellFormed index
  exact HasTypeDesc.piCodeDetection_completeOnFormationClassifiers
    entryFormationTyped converts

/-- **The unit arm's literal test is complete**: a formation-typed classifier `Conv` to the
unit code IS the unit code — rigidity against `unitTypeCellFormationTyped`. -/
theorem HasTypeDesc.unitDetection_completeOnFormationClassifiers {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {classifier reclassifier : RawTerm scope}
    (classifierTyped : HasTypeDesc profile context classifier reclassifier)
    (converts : Conv classifier unitTypeCell) :
    classifier = unitTypeCell :=
  HasTypeDesc.formationSubjects_convRigid classifierTyped
    (unitTypeCellFormationTyped context) converts

end FX1Poly.Typed
