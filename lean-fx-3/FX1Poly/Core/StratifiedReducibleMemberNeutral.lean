import FX1Poly.Core.StratifiedReducibleMember
import FX1Poly.Core.StratifiedReducibleTypeNeutral
import FX1Poly.Core.StratifiedReducibleTypeReducibilityCandidate

/-! # FX1Poly/Core/StratifiedReducibleMemberNeutral
    — stratified membership at a neutral classifier is exactly strong normalization

The stratified port of `IsReducibleMember.atNeutralClassifier` (`ReducibleMemberNeutral`).  At the
stratified relation `ReducibleTypeAt level`, the `neutral` arm assigns the strong-normalization candidate to
every weak-head-normal type code that is neither Π-rooted (the dependent-arrow arm) nor universe-rooted (the
Tarski-universe arm — the EXTRA guard the stratified `ReducibleTypeStep.neutral` carries over the
non-stratified two-guard `ReducibleType.neutral`, because a universe code has its own stratified arm rather
than the SN candidate).  So stratified membership at such a classifier collapses to a single sharp statement:

  `IsReducibleMemberAt level classifier term ↔ IsStronglyNormalizing term`   (classifier neutral).

This is the stratified counterpart of the semantic heart of why the reducibility model proves SN: every type
whose code is a weak-head-normal non-Π non-universe leaf (a variable, a stuck eliminator, a data former)
classifies EXACTLY the strongly-normalizing terms at every level.  The `←` direction (an SN term is a member
of its neutral-type classifier) feeds the variable / stuck-eliminator membership arms of the fundamental
theorem; the `→` direction extracts SN from membership at a fixed neutral type — the candidate→SN bridge
WITHOUT the `scope + 1` / `predLevel + 1` restriction of the general CR1
(`IsReducibleMemberAt.stronglyNormalizing`), because here the classifier pins the candidate to
`IsStronglyNormalizing` directly via `ReducibleTypeAt.deterministic`.

## Zero-axiom verification

`ReducibleTypeAt.deterministic` against the explicit `neutral` witness for the `→` direction; the explicit
`neutral`-candidate `ReducibleTypeStep.neutral` (per-level by `cases level`, mirroring
`reducibleOfWeakHeadNormalFormer`) for the `←` direction.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **The strong-normalization candidate is the stratified reducible-type denotation of a neutral classifier.**
A weak-head-normal non-Π non-universe type code is a reducible type at every level, with candidate exactly
`IsStronglyNormalizing` (the `neutral` arm of `ReducibleTypeStep`, fired from the three guards alone).
Per-level by `cases level` — the same dispatch `ReducibleTypeAt.reducibleOfWeakHeadNormalFormer` uses, but
keeping the candidate DEFINITIONALLY `IsStronglyNormalizing` rather than packaging it existentially, so the
membership iff below can read it back by determinism. -/
theorem ReducibleTypeAt.stronglyNormalizingAtNeutral {scope : Nat} {level : Nat}
    {typeCode : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    ReducibleTypeAt level typeCode IsStronglyNormalizing := by
  cases level with
  | zero => exact ReducibleTypeStep.neutral weakHeadNormal notPiType notUniverse
  | succ predLevel => exact ReducibleTypeStep.neutral weakHeadNormal notPiType notUniverse

/-- **Stratified membership at a neutral classifier is exactly strong normalization.**  A weak-head-normal
non-Π non-universe type code denotes the strong-normalization candidate at every level
(`stronglyNormalizingAtNeutral`), so a term is a stratified reducible member of it precisely when strongly
normalizing.  `→`: the member's candidate coincides with the SN candidate by
`ReducibleTypeAt.deterministic`.  `←`: the SN candidate is itself the witnessing candidate. -/
theorem IsReducibleMemberAt.atNeutralClassifier {scope : Nat} {level : Nat}
    {classifier term : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
    (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : classifier.rootGenerator ≠ Generator.gen_universeCode) :
    IsReducibleMemberAt level classifier term ↔ IsStronglyNormalizing term := by
  constructor
  · intro member
    obtain ⟨candidate, reducible, membership⟩ := member
    exact (ReducibleTypeAt.deterministic reducible
      (ReducibleTypeAt.stronglyNormalizingAtNeutral weakHeadNormal notPiType notUniverse) term).mp
      membership
  · intro stronglyNormalizing
    exact ⟨IsStronglyNormalizing,
      ReducibleTypeAt.stronglyNormalizingAtNeutral weakHeadNormal notPiType notUniverse,
      stronglyNormalizing⟩

/-- **A variable is a stratified reducible member of any reducible type** (at a positive level / non-empty
scope).  At `predLevel + 1` the type's candidate is a genuine Girard reducibility candidate
(`ReducibleTypeAt.isReducibilityCandidate`), and every reducibility candidate contains all variables
(`IsReducibilityCandidate.containsVariable` — a variable is neutral with no reducts, so CR3 holds
vacuously).  Packaged at the `IsReducibleMemberAt` layer: the witnessing candidate is the type's own, the
membership is variable-containment.  This is the var-0 ingredient of the binder-lifted reducible
environment (the fresh variable a `RawTermSubst.lift` introduces is a reducible member of the lifted
binding type) and the membership form of the fundamental theorem's variable case. -/
theorem IsReducibleMemberAt.variable {scope : Nat} {predLevel : Nat}
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeAt (predLevel + 1) typeCode candidate)
    (index : Fin (scope + 1)) :
    IsReducibleMemberAt (predLevel + 1) typeCode (.mkGen .gen_var index .childNil) :=
  ⟨candidate, reducible, reducible.isReducibilityCandidate.containsVariable index⟩

end FX1Poly.Core
