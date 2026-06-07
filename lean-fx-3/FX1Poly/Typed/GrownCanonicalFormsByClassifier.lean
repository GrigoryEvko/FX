import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.PiTypeFunctionInversion
import FX1Poly.Typed.GrownEngineHonesty

/-! # FX1Poly/Typed/GrownCanonicalFormsByClassifier — canonical forms PER TYPE for the grown engine

`GrownCanonicalForms.closedNormalSubjectHead` proves the WEAK canonical-forms statement: a closed normal
grown-typed term has head `gen_lam` / `gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` — one of four
shapes, regardless of its classifier.  The standard textbook **canonical-forms-per-type** lemma is sharper: it
reads the classifier and pins the value's shape EXACTLY.  This file ships the two non-degenerate instances over
what the grown engine types — function values and type values.

  * `HasTypeDescPi.closedNormalFunctionIsLambda` — a closed normal term of FUNCTION type (`piTyCodeCell …`) is a
    λ, and its body is extracted (`∃ body, subject = lamCell body`).  Of the four `closedNormalSubjectHead`
    shapes, the three type-former heads are refuted at a Π classifier by the `*NotTypedAtPiType` inversions
    (`PiTypeFunctionInversion`: a Π / Σ former or a universe code is a TYPE, classified by a universe code, never
    a member of a Π type); only the λ head survives.  This is the canonical-forms half of progress AT a function
    type — the shape future η / function-extensionality / typed-readback work consumes.

  * `HasTypeDescPi.closedNormalTypeIsFormer` — a closed normal term of TYPE (one inhabiting a universe
    `universeCodeCell levelExpr flag`) is a type FORMER: its head is `gen_piTyCode` / `gen_sigmaTyCode` /
    `gen_universeCode`, never `gen_lam`.  The λ head is refuted at a universe classifier by
    `GrownEngineHonesty.lam_notTypedAtUniverseCode` (a λ inhabits Π, not `Type@e`); the other three
    `closedNormalSubjectHead` heads ARE the type-former heads.  The canonical-forms half of progress AT a
    universe — a closed normal TYPE is a Π / Σ / universe code (a syntactic type), the type-level canonicity fact.

Both are the per-classifier refinements of `closedNormalSubjectHead`: it gives "one of four heads", these read
the classifier to drop the impossible ones.  `#672`-independent, no subject reduction — pure inversion over the
shipped closed-canonical-forms recursor plus the classifier-mismatch inversions.

## Zero-axiom verification

`rcases` on `closedNormalSubjectHead`'s four-way head disjunction; the impossible heads reconstruct their cell
shape (`eq_{lamCell,piTyCodeCell,sigmaTyCodeCell,universeCodeCell}_of_headGenerator`) and are refuted by the
classifier-mismatch inversions (`*NotTypedAtPiType` / `lam_notTypedAtUniverseCode`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch before
landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Canonical forms at a function type.**  A closed normal term whose classifier is a Π type (`piTyCodeCell`)
is a λ, with its body extracted.  Of the four `closedNormalSubjectHead` head shapes, the Π / Σ formers and the
universe code are refuted at a Π classifier by the `*NotTypedAtPiType` inversions (a type former / code is a
TYPE, never a member of a Π type), leaving only the λ head, reconstructed by `eq_lamCell_of_headGenerator`. -/
theorem HasTypeDescPi.closedNormalFunctionIsLambda {profile : PolyProfile} {subject : RawTerm 0}
    {outerDomain : RawTerm 0} {outerCodomain : RawTerm 1}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (piTyCodeCell outerDomain outerCodomain))
    (normal : RawTerm.isStepNormalForm subject) :
    ∃ body : RawTerm 1, subject = lamCell body := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed normal
      (fun emptyIndex => emptyIndex.elim0) with
      headLam | headPi | headSigma | headUniverse | headList
  · exact eq_lamCell_of_headGenerator headLam
  · obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
    rw [piEq] at typed
    exact (HasTypeDescPi.piFormerNotTypedAtPiType typed).elim
  · obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
    rw [sigmaEq] at typed
    exact (HasTypeDescPi.sigmaFormerNotTypedAtPiType typed).elim
  · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
    rw [universeEq] at typed
    exact (HasTypeDescPi.universeCodeNotTypedAtPiType typed).elim
  · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
    rw [listEq] at typed
    exact (HasTypeDescPi.listFormerNotTypedAtPiType typed).elim

/-- **Canonical forms at a universe.**  A closed normal term whose classifier is a universe
(`universeCodeCell levelExpr flag`) — i.e. a closed normal TYPE — is a type FORMER: its head is `gen_piTyCode`,
`gen_sigmaTyCode`, or `gen_universeCode`, never `gen_lam`.  The λ head is refuted at a universe classifier by
`lam_notTypedAtUniverseCode` (a λ inhabits Π, not `Type@e`); the other three `closedNormalSubjectHead` heads are
exactly the type-former heads.  The type-level canonicity fact: closed normal types are syntactic type formers. -/
theorem HasTypeDescPi.closedNormalTypeIsFormer {profile : PolyProfile} {subject : RawTerm 0}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (universeCodeCell levelExpr flag))
    (normal : RawTerm.isStepNormalForm subject) :
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode ∨
    RawTerm.headGenerator subject = Generator.gen_listCode := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed normal
      (fun emptyIndex => emptyIndex.elim0) with headLam | rest
  · obtain ⟨body, lamEq⟩ := eq_lamCell_of_headGenerator headLam
    rw [lamEq] at typed
    exact (lam_notTypedAtUniverseCode levelExpr flag typed).elim
  · exact rest

end FX1Poly.Typed
