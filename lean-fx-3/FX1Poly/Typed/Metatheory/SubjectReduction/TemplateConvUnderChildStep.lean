import FX1Poly.Typed.Engine.RuleTables.CellTemplate
import FX1Poly.Core.Rewriting.Conversion.ConvCongruence
import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair
import FX1Poly.Typed.Metatheory.Universe.ConvCodeInjectivity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/TemplateConvUnderChildStep
    — SR-DSL-1: generic Conv-drift over CellTemplate (the unconditional drift keystone)

When a child of a cell steps, the cell's `interpret?`-produced type/classifier DRIFTS to a `Conv`-equal term.
The design lock's keystone: this is UNCONDITIONAL (no SN, no flag-uniqueness) because `Conv := StepStar.Join`,
so every `interpret?` arm lifts a children-level `Conv` to an output `Conv` by the shipped congruences
(`Conv.ofChildren` / `Conv.subst0` / `Conv.substPair` / `Conv.subst` / `Conv.rename` / `Conv.piTyCode_cong`).
ONE induction on `CellTemplate` SUBSUMES the per-row drift corpus (`ElimOutputTypeCongruence` for outputs +
`DependentBranchTypeMotiveCongruence` for branch classifiers): a new eliminator row needs NO new drift lemma.

This file ships the substrate in layers: the weakening-preserves-`Conv` helpers (this section), the
`ConvChildren`-projection-at-shift helpers, then the mutual `templateConvUnderChildStep` / `spineConvUnderChildStep`.

## Zero-axiom

`Conv.weaken` / `Conv.rename` / `Conv.refl` over structural `Nat`/`ConvChildren` inductions — no `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-! ## Weakening preserves `Conv` (the depth-grading substrate) -/

/-- `RawTerm.weakenBy depth` preserves `Conv` — iterated `Conv.weaken` over the depth.  Used by the `childAt`
and `universeCode` arms (which weaken a projected/built term to the current depth). -/
theorem Conv.weakenByConv {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (convProof : Conv leftTerm rightTerm) :
    (depth : Nat) → Conv (RawTerm.weakenBy depth leftTerm) (RawTerm.weakenBy depth rightTerm)
  | 0 => convProof
  | depth + 1 => Conv.weaken (Conv.weakenByConv convProof depth)

/-- `RawTerm.weakenBodyUnderOneBinderBy depth` preserves `Conv` — iterated `Conv.rename (lift weaken)` keeping
the body's own binder innermost.  Used by the `childBodyAt` and `+1`-macro arms. -/
theorem Conv.weakenBodyUnderOneBinderByConv {scope : Nat} {leftBody rightBody : RawTerm (scope + 1)}
    (convProof : Conv leftBody rightBody) :
    (depth : Nat) →
    Conv (RawTerm.weakenBodyUnderOneBinderBy depth leftBody)
         (RawTerm.weakenBodyUnderOneBinderBy depth rightBody)
  | 0 => convProof
  | depth + 1 =>
      Conv.rename (RawRenaming.lift RawRenaming.weaken)
        (Conv.weakenBodyUnderOneBinderByConv convProof depth)

/-- `RawTerm.weakenBodyUnderTwoBindersBy depth` preserves `Conv` — iterated `Conv.rename (lift (lift weaken))`
keeping both of the body's binders innermost.  Used by the `substPairInto` and `+2`-macro (`natSucc`) arms. -/
theorem Conv.weakenBodyUnderTwoBindersByConv {scope : Nat} {leftBody rightBody : RawTerm (scope + 2)}
    (convProof : Conv leftBody rightBody) :
    (depth : Nat) →
    Conv (RawTerm.weakenBodyUnderTwoBindersBy depth leftBody)
         (RawTerm.weakenBodyUnderTwoBindersBy depth rightBody)
  | 0 => convProof
  | depth + 1 =>
      Conv.rename (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (Conv.weakenBodyUnderTwoBindersByConv convProof depth)

end FX1Poly.Typed
