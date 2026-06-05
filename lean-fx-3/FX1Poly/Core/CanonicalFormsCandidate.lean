import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.NormalFormUnique
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.NeutralStepClosure

/-! # Foundation/PolyCell/Core/CanonicalFormsCandidate
    — the generic "strongly-normalizing, neutral-or-value" candidate skeleton (data-canonicity foundation)

The shipped reducibility model (`ReducibleTypeStep`) gives every NON-Π / non-universe type code the bare
strong-normalization candidate (`IsStronglyNormalizing`).  That suffices for SN but carries NO canonicity
content: a closed strongly-normalizing term need not reduce to a CONSTRUCTOR.  Data canonicity (closed bool ↝
`true`/`false`, closed Empty uninhabited, SN-047/048/049/050/059/062) needs the SHARPER candidate that a member
is strongly normalizing AND is either neutral or reduces to a designated VALUE form.

`CanonicalFormsPredicate isValue` is that candidate, parameterized by an arbitrary value predicate `isValue`
(instantiated per data type: `isValue := (· is `boolTrue` or `boolFalse`)` for `bool`, the empty predicate for
`Empty`, the constructor shapes for `nat`/`list`/...).  It is the reusable skeleton every data candidate shares,
so its closure proofs are proved ONCE here generically rather than per type.

## What is proved (CR1, CR3) and what is deferred (CR2)

A Girard reducibility candidate (`IsReducibilityCandidate`) needs CR1 / CR2 / CR3 (`ReducibilityCandidate.lean`).
Two of the three are GENERIC — independent of `isValue` — and are discharged here:

* **CR1** (`stronglyNormalizing`) — the first conjunct, directly.
* **CR3** (`neutralExpansion`) — a neutral term whose every one-step reduct is a member is itself a member: it is
  strongly normalizing (`Acc.intro` over the reducts' SN, exactly the shipped `isStronglyNormalizing_-
  isReducibilityCandidate` CR3 pattern) and neutral (the left disjunct), with NO appeal to `isValue`.

CR2 (forward closure under one `Step`) is the data-specific residual and is DELIBERATELY DEFERRED: preserving the
"neutral OR reduces-to-value" disjunct forward needs (i) IsNeutral closed under `Step` (an 11-eliminator-arm
`Step.from_X` inversion — neutrals never head-fire because a neutral scrutinee is no constructor) and (ii)
per-term confluence to carry `StepStar term value` past one `Step` (the value is a normal form, unique by
`normalForm_unique` on the SN member).  Both prerequisites are shipped substrate; assembling CR2 is the next
data-candidate task (toward SN-063 bool reducibility).  This file is the honest 2-of-3 foundation, not a full
candidate — `IsReducibilityCandidate (CanonicalFormsPredicate isValue)` is NOT yet claimed.

## Zero-axiom verification

CR1 is a projection; CR3 is `Acc.intro` + `Or.inl` (the shipped SN-candidate CR3 pattern, propext-free).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The strongly-normalizing neutral-or-value candidate predicate**, parameterized by a value predicate.  A
term is a member when it is strongly normalizing AND either neutral or reduces (by `StepStar`) to a term
satisfying `isValue`.  This is the canonicity-bearing refinement of the bare SN candidate: a CLOSED member,
being non-neutral (`IsNeutral.noClosed`), must reduce to a value — the closed-canonical-forms payload. -/
def CanonicalFormsPredicate {scope : Nat} (isValue : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  IsStronglyNormalizing term ∧
    (IsNeutral term ∨ ∃ value : RawTerm scope, StepStar term value ∧ isValue value)

/-- **CR1 for the canonical-forms candidate**: every member is strongly normalizing — the first conjunct. -/
theorem CanonicalFormsPredicate.stronglyNormalizing {scope : Nat}
    {isValue : RawTerm scope → Prop} {term : RawTerm scope}
    (member : CanonicalFormsPredicate isValue term) :
    IsStronglyNormalizing term :=
  member.1

/-- **CR3 for the canonical-forms candidate**: a neutral term whose every one-step reduct is a member is itself
a member.  It is strongly normalizing because all its reducts are (`Acc.intro` over their SN witnesses, the
shipped `isStronglyNormalizing_isReducibilityCandidate` CR3 shape), and it is neutral (left disjunct) — no
appeal to `isValue`, so this holds for every data value predicate uniformly. -/
theorem CanonicalFormsPredicate.neutralExpansion {scope : Nat}
    {isValue : RawTerm scope → Prop} {term : RawTerm scope}
    (termIsNeutral : IsNeutral term)
    (reductsAreMembers : ∀ reduct : RawTerm scope, Step term reduct →
      CanonicalFormsPredicate isValue reduct) :
    CanonicalFormsPredicate isValue term :=
  ⟨Acc.intro term (fun reduct stepToReduct => (reductsAreMembers reduct stepToReduct).1),
    Or.inl termIsNeutral⟩

/-- **The candidate contains every variable.**  A variable is neutral (`IsNeutral.var`) and has no reducts
(`noStep_var`), so CR3's premise holds vacuously — variables are members of every canonical-forms candidate.
This is the candidate-nonemptiness fact the fundamental theorem's variable case consumes. -/
theorem CanonicalFormsPredicate.containsVariable {scope : Nat}
    {isValue : RawTerm scope → Prop} (index : Fin scope) :
    CanonicalFormsPredicate isValue (.mkGen .gen_var index .childNil) :=
  CanonicalFormsPredicate.neutralExpansion (IsNeutral.var index)
    (fun _reduct stepFromVar => (noStep_var index stepFromVar).elim)

/-- **Every strongly-normalizing NEUTRAL term is a member of every canonical-forms candidate.**  The full CR3
neutral leaf: `containsVariable` is the special vacuous case (a variable has no reducts), this is the general
case where a neutral may reduce into its children.  Well-founded recursion on the term's SN accessibility — at
each term, every reduct stays neutral (`IsNeutral.closedUnderStep`) and is SN-smaller, so the inductive
hypothesis makes it a member, and `neutralExpansion` lifts membership back to the term.  No appeal to `isValue`,
so it holds for every data value predicate uniformly — the reducibility leaf any neutral-eliminator member
argument (a stuck `app` / `fst` / `boolElim …` over a neutral head) consumes. -/
theorem CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral {scope : Nat}
    {isValue : RawTerm scope → Prop} {term : RawTerm scope}
    (termStronglyNormalizing : IsStronglyNormalizing term)
    (termIsNeutral : IsNeutral term) :
    CanonicalFormsPredicate isValue term := by
  revert termIsNeutral
  induction termStronglyNormalizing with
  | intro _currentTerm _accessibility inductiveHypothesis =>
      intro currentIsNeutral
      exact CanonicalFormsPredicate.neutralExpansion currentIsNeutral
        (fun reduct stepToReduct =>
          inductiveHypothesis reduct stepToReduct (currentIsNeutral.closedUnderStep stepToReduct))

/-- **CR2 for the canonical-forms candidate**, the formerly-deferred forward-closure leg — discharged from the
two genuinely-provable data-specific facts.  A member's reduct stays a member: it is strongly normalizing (the
shipped SN candidate's CR2), and its "neutral or reduces-to-value" disjunct is preserved:

* if the term is neutral, the reduct is neutral by `neutralClosedUnderStep` (a neutral never head-fires — a
  neutral scrutinee is no constructor — so its reducts are congruence reducts, still neutral);
* if the term reduces to a `value`, then since `value` is a NORMAL FORM (`isValueImpliesNormal`) and the term is
  strongly normalizing, per-term confluence (`confluence_of_localJoin_and_accessible`) joins the one-step reduct
  with the value-reduction, and the value's rigidity (`eq_of_noStep` via `isStepNormalForm_blocks_step`) collapses
  the join's apex onto the value — so the reduct also reduces to the value.

The two hypotheses are exactly the data-specific obligations (both shipped-able kernel facts: `IsNeutral` closed
under `Step` is an 11-arm `Step.from_X` inversion; data values ARE normal forms by construction).  Confluence is
discharged per-term by the member's own SN witness — no global-confluence assumption. -/
theorem CanonicalFormsPredicate.closedUnderStep {scope : Nat}
    {isValue : RawTerm scope → Prop}
    (neutralClosedUnderStep :
      ∀ {neutralTerm neutralReduct : RawTerm scope},
        IsNeutral neutralTerm → Step neutralTerm neutralReduct → IsNeutral neutralReduct)
    (isValueImpliesNormal :
      ∀ {value : RawTerm scope}, isValue value → RawTerm.isStepNormalForm value)
    {term reduct : RawTerm scope}
    (member : CanonicalFormsPredicate isValue term) (stepToReduct : Step term reduct) :
    CanonicalFormsPredicate isValue reduct := by
  refine ⟨isStronglyNormalizing_isReducibilityCandidate.closedUnderStep member.1 stepToReduct, ?_⟩
  rcases member.2 with termIsNeutral | ⟨value, termReducesToValue, valueIsValue⟩
  · exact Or.inl (neutralClosedUnderStep termIsNeutral stepToReduct)
  · have valueIsNormal : RawTerm.isStepNormalForm value := isValueImpliesNormal valueIsValue
    have reductJoinsValue : StepStar.Join reduct value :=
      StepStar.confluence_of_localJoin_and_accessible member.1
        (StepStar.trans stepToReduct (StepStar.refl reduct)) termReducesToValue
    obtain ⟨apexTerm, reductToApex, valueToApex⟩ := reductJoinsValue
    have apexEqualsValue : apexTerm = value :=
      StepStar.eq_of_noStep
        (fun stepReduct stepFromValue =>
          RawTerm.isStepNormalForm_blocks_step valueIsNormal stepReduct stepFromValue)
        valueToApex
    exact Or.inr ⟨value, apexEqualsValue ▸ reductToApex, valueIsValue⟩

/-- **The canonical-forms predicate is a full Girard reducibility candidate**, given the two data-specific
facts (`IsNeutral` closed under `Step` + data values are normal forms).  Bundles the generic CR1
(`stronglyNormalizing`) and CR3 (`neutralExpansion`) with the now-discharged CR2 (`closedUnderStep`).  Once the
two facts are supplied for a concrete data type (e.g. `bool` with `isValue := · = boolTrue ∨ · = boolFalse`),
this is an honest `IsReducibilityCandidate` ready to be the data type's arm of the reducibility model — the
foundation for unconditional data canonicity (SN-063 bool reducibility / SN-047 bool canonicity). -/
theorem CanonicalFormsPredicate.isReducibilityCandidate {scope : Nat}
    {isValue : RawTerm scope → Prop}
    (neutralClosedUnderStep :
      ∀ {neutralTerm neutralReduct : RawTerm scope},
        IsNeutral neutralTerm → Step neutralTerm neutralReduct → IsNeutral neutralReduct)
    (isValueImpliesNormal :
      ∀ {value : RawTerm scope}, isValue value → RawTerm.isStepNormalForm value) :
    IsReducibilityCandidate (CanonicalFormsPredicate isValue) where
  stronglyNormalizing := CanonicalFormsPredicate.stronglyNormalizing
  closedUnderStep := CanonicalFormsPredicate.closedUnderStep neutralClosedUnderStep isValueImpliesNormal
  neutralExpansion := CanonicalFormsPredicate.neutralExpansion

/-- **The canonical-forms predicate is a reducibility candidate given ONLY that data values are normal
forms** — the neutral half of the obligation is now discharged unconditionally.  The
`neutralClosedUnderStep` argument of `CanonicalFormsPredicate.isReducibilityCandidate` is exactly
`IsNeutral.closedUnderStep` (`NeutralStepClosure.lean`: a neutral's one-step reduct is again neutral), so a
concrete data type need only supply `isValueImpliesNormal` for its constructors — trivial, since a
constructor with normal children admits no `Step`.  This is the form a data type instantiates to obtain its
arm of the reducibility model (toward SN-063 bool reducibility / SN-047 bool canonicity). -/
theorem CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal {scope : Nat}
    {isValue : RawTerm scope → Prop}
    (isValueImpliesNormal :
      ∀ {value : RawTerm scope}, isValue value → RawTerm.isStepNormalForm value) :
    IsReducibilityCandidate (CanonicalFormsPredicate isValue) :=
  CanonicalFormsPredicate.isReducibilityCandidate IsNeutral.closedUnderStep isValueImpliesNormal

/-- **Closed canonical-forms members are canonical** — the canonicity payload of the candidate.  A CLOSED
member (scope 0) cannot be neutral: `IsNeutral.noClosed` refutes the neutral disjunct (no closed term is a
stuck eliminator — every neutral bottoms out at a variable, of which scope 0 has none).  So the member's
"neutral OR reduces-to-value" disjunct collapses to its right branch: the member reduces to a designated
`isValue`.  Combined with a proof that a closed well-typed term is a member (the fundamental theorem), this is
exactly data canonicity — a closed term of the data type reduces to a constructor (SN-047 / SN-049).  The
extraction is `#672`-independent; only the membership half awaits the typed reducibility fundamental theorem. -/
theorem CanonicalFormsPredicate.closedReducesToValue {isValue : RawTerm 0 → Prop} {term : RawTerm 0}
    (member : CanonicalFormsPredicate isValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isValue value := by
  rcases member.2 with termIsNeutral | reducesToValue
  · exact (IsNeutral.noClosed termIsNeutral).elim
  · exact reducesToValue

/-- **A normal value is a member of its canonical-forms candidate.**  If `value` satisfies the value
predicate and is a structural normal form, it is a member: it is strongly normalizing (a normal form admits
no `Step`, so `Acc.intro` closes vacuously via `RawTerm.isStepNormalForm_blocks_step`) and reduces
reflexively to itself, a value.  This is the constructor-reducibility helper every data type instantiates for
its (normal) constructors — `value ↝* value` with `value` canonical. -/
theorem CanonicalFormsPredicate.memberOfValue {scope : Nat} {isValue : RawTerm scope → Prop}
    {value : RawTerm scope}
    (valueIsNormal : RawTerm.isStepNormalForm value) (valueIsValue : isValue value) :
    CanonicalFormsPredicate isValue value :=
  ⟨Acc.intro value
      (fun reduct stepFromValue =>
        absurd stepFromValue (RawTerm.isStepNormalForm_blocks_step valueIsNormal reduct)),
    Or.inr ⟨value, StepStar.refl value, valueIsValue⟩⟩

end FX1Poly.Core
