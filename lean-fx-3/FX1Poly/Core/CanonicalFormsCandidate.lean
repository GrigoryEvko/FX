import FX1Poly.Core.ReducibilityCandidate

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

end FX1Poly.Core
