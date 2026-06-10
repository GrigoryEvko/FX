import FX1Poly.Typed.GrownOpenProgress
import FX1Poly.Typed.GrownCanonicalFormsByClassifier

/-! # FX1Poly/Typed/GrownOpenCanonicalFormsByClassifier — open canonical forms PER TYPE (with neutrals)

`GrownCanonicalFormsByClassifier` proved canonical forms per type for CLOSED terms: a closed normal term at a
function type is a λ (`closedNormalFunctionIsLambda`), at a universe is a type former
(`closedNormalTypeIsFormer`).  Closedness eliminates the variable leaf, so those two shapes are exhaustive.  In an
OPEN context a normal form can additionally be a **neutral** (a variable, or a stuck application).  This file
ships the open per-type canonical-forms lemmas — the same classifier-driven shape refinement, but admitting the
neutral disjunct — over the shipped `openNormalSubjectCanonicalOrNeutral` (open canonical forms) plus the
context-general classifier-mismatch inversions.

  * `HasTypeDescPi.openNormalFunctionIsLambdaOrNeutral` — a normal grown-typed term at a Π type
    (`piTyCodeCell …`) in ANY well-formed context is a λ (`∃ body, subject = lamCell body`) OR a `Core.IsNeutral`
    term.  Of the open canonical-forms disjuncts, the six type-former heads (Π / Σ / universe / list / option /
    unit) are refuted at a Π classifier by the `*NotTypedAtPiType` inversions (a former / universe code is a TYPE,
    never a member of a Π type); the λ head and the neutral case survive.

  * `HasTypeDescPi.openNormalTypeIsFormerOrNeutral` — a normal grown-typed term at a universe
    (`universeCodeCell levelExpr flag`) in ANY well-formed context is a type FORMER (head `gen_piTyCode` /
    `gen_sigmaTyCode` / `gen_universeCode` / `gen_listCode` / `gen_optionCode` / `gen_unitCode`) OR a
    `Core.IsNeutral` term.  The λ head is refuted at a universe classifier by `lam_notTypedAtUniverseCode` (a λ
    inhabits Π, not `Type@e`); the six former heads and the neutral case survive.

This is exactly the dichotomy a type-directed NbE / η-long readback (the `TY-CONV-quote` / `η-M15` line) branches
on: at a function type, recurse into a λ body or η-expand a neutral; at a universe, descend into a type former or
stop at a neutral.  `closedNormalFunctionIsLambda` / `closedNormalTypeIsFormer` are the empty-context
specializations where the neutral disjunct is vacuous.  `#672`-independent — pure inversion, no subject reduction,
no SN.

## Zero-axiom verification

`rcases` on `openNormalSubjectCanonicalOrNeutral`'s `(IsGrownCanonicalHead ∨ IsNeutral)` result; the impossible
heads reconstruct their cell shape (`eq_{lamCell,piTyCodeCell,sigmaTyCodeCell,universeCodeCell,listCodeCell,optionCodeCell,unitCodeCell}_of_headGenerator`)
and are refuted by the context-general classifier-mismatch inversions; the surviving canonical head and the
neutral case are returned directly.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Open canonical forms at a function type.**  A normal grown-typed term whose classifier is a Π type
(`piTyCodeCell`) in any well-formed context is a λ (with its body extracted) OR a `Core.IsNeutral` term.  Of the
open canonical-forms disjuncts, the Π / Σ / list / option / unit formers and the universe code are refuted at a Π
classifier by the `*NotTypedAtPiType` inversions (a type former / code is a TYPE, never a member of a Π type);
the λ head (reconstructed by `eq_lamCell_of_headGenerator`) and the neutral case survive.  The open
generalization of `closedNormalFunctionIsLambda`. -/
theorem HasTypeDescPi.openNormalFunctionIsLambdaOrNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed : HasTypeDescPi profile context subject (piTyCodeCell outerDomain outerCodomain))
    (wellFormed : WfContextDesc context)
    (normal : RawTerm.isStepNormalForm subject) :
    (∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)), subject = lamCell domainAnn body) ∨
      IsNeutral subject := by
  rcases HasTypeDescPi.openNormalSubjectCanonicalOrNeutral typed wellFormed normal with
      (headLam | headPi | headSigma | headUniverse | headList | headOption | headUnit) | neutral
  · exact Or.inl (eq_lamCell_of_headGenerator headLam)
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
  · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
    rw [optionEq] at typed
    exact (HasTypeDescPi.optionFormerNotTypedAtPiType typed).elim
  · have unitEq := eq_unitCodeCell_of_headGenerator headUnit
    rw [unitEq] at typed
    exact (HasTypeDescPi.unitFormerNotTypedAtPiType typed).elim
  · exact Or.inr neutral

/-- **Open canonical forms at a universe.**  A normal grown-typed term whose classifier is a universe
(`universeCodeCell levelExpr flag`) in any well-formed context — a normal TYPE — is a type FORMER (head
`gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` / `gen_listCode` / `gen_optionCode` / `gen_unitCode`) OR a
`Core.IsNeutral` term.  The λ head is refuted at a universe classifier by `lam_notTypedAtUniverseCode` (a λ
inhabits Π, not `Type@e`); the six former heads and the neutral case survive.  The open generalization of
`closedNormalTypeIsFormer`. -/
theorem HasTypeDescPi.openNormalTypeIsFormerOrNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile context subject (universeCodeCell levelExpr flag))
    (wellFormed : WfContextDesc context)
    (normal : RawTerm.isStepNormalForm subject) :
    (RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_universeCode ∨
     RawTerm.headGenerator subject = Generator.gen_listCode ∨
     RawTerm.headGenerator subject = Generator.gen_optionCode ∨
     RawTerm.headGenerator subject = Generator.gen_unitCode) ∨ IsNeutral subject := by
  rcases HasTypeDescPi.openNormalSubjectCanonicalOrNeutral typed wellFormed normal with
      (headLam | rest) | neutral
  · obtain ⟨_domainAnn, body, lamEq⟩ := eq_lamCell_of_headGenerator headLam
    rw [lamEq] at typed
    exact (lam_notTypedAtUniverseCode levelExpr flag typed).elim
  · exact Or.inl rest
  · exact Or.inr neutral

end FX1Poly.Typed
