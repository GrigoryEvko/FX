import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.HasTypeDescPiValidity
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeDescPiCongruence — grown-engine congruence-at-typing building blocks
    (the λ/app cong arms of subject reduction, modulo the child's SR; toward #458)

The subject-reduction master dispatcher (#458), built by recursion on `Step`, handles the
congruence (`Step.cong`) case by: inverting the parent's grown typing, strong-normalization-reducing
the one stepped child, and re-assembling the parent at the same classifier.  This file ships the
RE-ASSEMBLY half for the `lamCell` and `appCell` heads — each as a self-contained, recursion-free
lemma that takes the child's type-preservation as a HYPOTHESIS (`childPreserves`), exactly the shape
`Step.subjectReduction child` supplies.

Splitting these out keeps the dispatcher thin (its `cong` arm just dispatches on the head and applies
the matching lemma with `childPreserves := fun typed => Step.subjectReduction childStep wf typed`) and
keeps each congruence's metatheory — inversion + reconstruction + the dependent-output `Conv` for the
argument case — isolated and individually audited.

## The three λ/app congruences

  * `congLamBody` — replace a λ's body by a same-typed body'.  `invertLam` exposes the λ's own
    `domain`/`codomain` (and `Conv classifier (Π domain codomain)`); `childPreserves` retypes the body
    at the codomain under the domain binder; `piIntro` rebuilds the λ at `Π domain codomain`; validity
    (`classifierIsTypeDesc`) + `conv` returns it to the original `classifier`.
  * `congFunction` — replace an application's function by a same-typed function'.  `invertApp` exposes
    the Π-code and the dependent output `Conv`; `childPreserves` retypes the function at the SAME Π-code
    (SR preserves type); `piElim` rebuilds at `subst0 codomain argument`; `conv` returns to `classifier`.
  * `congArgument` — replace an application's argument by a same-typed argument', given `Conv argument
    argument'` (from the step).  Same as `congFunction`, except the dependent output MOVES
    (`subst0 codomain argument` ⤳ `subst0 codomain argument'`), reconciled by `Conv.subst0 (refl codomain)
    argConv.sym` before the `conv` to `classifier`.

`childPreserves` is universe-of-typing-general (`∀ {S}, … f S → … f' S`, and for the binder case
`∀ {D S}, … (cons D) body S → … (cons D) body' S`) — precisely what `Step.subjectReduction`'s
"preserves ANY classifier" shape provides, so no existential domain/codomain leaks to the caller.

## Zero-axiom verification

Each lemma composes shipped zero-axiom results (`invertLam` / `invertApp`, `piIntro` / `piElim`, the
`conv` rule, `classifierIsTypeDesc`, `Conv.subst0` / `Conv.trans` / `Conv.sym`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **λ-body congruence (at typing).**  A `lamCell body` typed at `classifier`, with a same-typed
replacement `body'` (preserved at any codomain under any domain binder), gives `lamCell body'` typed
at the SAME `classifier`.  The `Step.cong`-on-a-λ-body case of subject reduction, modulo the body's SR
(supplied as `childPreserves`). -/
theorem HasTypeDescPi.congLamBody {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {body body' : RawTerm (scope + 1)} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (lamCell body) classifier)
    (childPreserves : ∀ {bindingType : RawTerm scope} {bodyClassifier : RawTerm (scope + 1)},
      HasTypeDescPi profile (context.cons bindingType) body bodyClassifier →
        HasTypeDescPi profile (context.cons bindingType) body' bodyClassifier)
    (wellFormed : WfContext context) :
    HasTypeDescPi profile context (lamCell body') classifier := by
  obtain ⟨domainCode, codomainCode, domainLevel, codomainLevel, flag,
      convClassifierPi, domainTyped, codomainTyped, bodyTyped⟩ := typed.invertLam
  have rebuiltLam :
      HasTypeDescPi profile context (lamCell body') (piTyCodeCell domainCode codomainCode) :=
    HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped codomainTyped
      (childPreserves bodyTyped)
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ := typed.classifierIsTypeDesc wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag rebuiltLam convClassifierPi.sym
    classifierTyped

/-- **Application-function congruence (at typing).**  An `appCell functionTerm argument` typed at
`classifier`, with a same-typed replacement `functionTerm'`, gives `appCell functionTerm' argument`
typed at the SAME `classifier`.  The dependent output is unchanged (the argument is fixed), so only
the invertApp `Conv` is composed.  The `Step.cong`-on-an-application-function case, modulo the
function's SR. -/
theorem HasTypeDescPi.congFunction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm functionTerm' argument : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (appCell functionTerm argument) classifier)
    (childPreserves : ∀ {functionClassifier : RawTerm scope},
      HasTypeDescPi profile context functionTerm functionClassifier →
        HasTypeDescPi profile context functionTerm' functionClassifier)
    (wellFormed : WfContext context) :
    HasTypeDescPi profile context (appCell functionTerm' argument) classifier := by
  obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, convClassifierOutput⟩ :=
    typed.invertApp
  have rebuiltApp :
      HasTypeDescPi profile context (appCell functionTerm' argument)
        (RawTerm.subst0 codomainCode argument) :=
    HasTypeDescPi.piElim (childPreserves functionTyped) argumentTyped
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ := typed.classifierIsTypeDesc wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag rebuiltApp convClassifierOutput.sym
    classifierTyped

/-- **Application-argument congruence (at typing).**  An `appCell functionTerm argument` typed at
`classifier`, with a same-typed replacement `argument'` and `Conv argument argument'` (from the step),
gives `appCell functionTerm argument'` typed at the SAME `classifier`.  Here the dependent output MOVES
(`subst0 codomainCode argument` ⤳ `subst0 codomainCode argument'`), reconciled by `Conv.subst0`.  The
`Step.cong`-on-an-application-argument case, modulo the argument's SR. -/
theorem HasTypeDescPi.congArgument {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument argument' : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (appCell functionTerm argument) classifier)
    (childPreserves : ∀ {argumentClassifier : RawTerm scope},
      HasTypeDescPi profile context argument argumentClassifier →
        HasTypeDescPi profile context argument' argumentClassifier)
    (argumentConverts : Conv argument argument')
    (wellFormed : WfContext context) :
    HasTypeDescPi profile context (appCell functionTerm argument') classifier := by
  obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, convClassifierOutput⟩ :=
    typed.invertApp
  have rebuiltApp :
      HasTypeDescPi profile context (appCell functionTerm argument')
        (RawTerm.subst0 codomainCode argument') :=
    HasTypeDescPi.piElim functionTyped (childPreserves argumentTyped)
  have convMovedOutput : Conv (RawTerm.subst0 codomainCode argument') classifier :=
    Conv.trans (Conv.subst0 (Conv.refl codomainCode) argumentConverts.sym) convClassifierOutput.sym
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ := typed.classifierIsTypeDesc wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag rebuiltApp convMovedOutput classifierTyped

end FX1Poly.Typed
