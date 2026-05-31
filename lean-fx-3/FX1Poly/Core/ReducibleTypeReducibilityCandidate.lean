import FX1Poly.Core.ReducibleType
import FX1Poly.Core.DependentArrowReducibilityCandidate

/-! # Foundation/PolyCell/Core/ReducibleTypeReducibilityCandidate
    — every candidate the dependent reducibility relation assigns is a Girard reducibility candidate

The dependent reducibility relation `ReducibleType` assigns a candidate predicate to each type code.  This
file closes the loop: every such candidate satisfies all three Girard CR conditions (CR1 strong
normalization, CR2 forward step-closure, CR3 neutral expansion), by induction on the derivation —

  * `whnfExpand` inherits its weak-head contractum's candidate-hood verbatim (the induction hypothesis);
  * `neutral` denotes the strong-normalization candidate, itself a candidate
    (`isStronglyNormalizing_isReducibilityCandidate`);
  * `piType` denotes the DEPENDENT function-space candidate, a candidate by
    `isDependentArrowReducible_isReducibilityCandidate` (whose CR3 was bridged by conversion-invariance).

This is the reducibility-candidate hand-off the fundamental theorem consumes: the variable case becomes
`candidate.containsVariable`, the conversion case `ReducibleType.convTransfer`, and the elimination cases
the candidates' `closedUnderStep` / `stronglyNormalizing`.

## Scope `scope + 1`

The arrow CR1 needs an inhabitant of the domain candidate to instantiate the function.  Over an arbitrary
scope a candidate can be empty (e.g. the closed `never` candidate), so CR1 would fail.  The uniform
inhabitant is a VARIABLE (`IsReducibilityCandidate.containsVariable`), which requires at least one variable
in scope; stating the theorem at `scope + 1` makes variable 0 available, and — because every `ReducibleType`
sub-derivation stays at the SAME scope — that one variable serves every nested Π.  The fundamental theorem
applies this at its context scope (always populated); the closed apex is reached by weakening.

## Zero-axiom verification

`induction reducible` with three `exact`s (the `whnfExpand` IH, the SN candidate, the dependent-arrow
candidate fed variable 0 via `Fin.mk 0 (Nat.succ_pos _)` — the explicit `⟨0, _⟩`, not the propext-leaking
`Fin` `OfNat` numeral).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Every dependent-reducibility candidate is a Girard reducibility candidate.**  By induction on the
`ReducibleType` derivation: `whnfExpand` reuses the induction hypothesis, `neutral` is the
strong-normalization candidate, and `piType` is the dependent function-space candidate (CR1's domain
inhabitant supplied uniformly by variable 0). -/
theorem ReducibleType.isReducibilityCandidate {scope : Nat} {typeCode : RawTerm (scope + 1)}
    {candidate : RawTerm (scope + 1) → Prop} (reducible : ReducibleType typeCode candidate) :
    IsReducibilityCandidate candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType =>
      exact isStronglyNormalizing_isReducibilityCandidate
  | piType _codomainCandidate _domainReducible codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      exact isDependentArrowReducible_isReducibilityCandidate
        domainInductiveHypothesis codomainInductiveHypothesis codomainReducible
        (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
        (domainInductiveHypothesis.containsVariable ⟨0, Nat.succ_pos scope⟩)

end FX1Poly.Core
