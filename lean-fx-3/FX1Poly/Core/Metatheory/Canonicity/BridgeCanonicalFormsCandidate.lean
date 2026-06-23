import FX1Poly.Core.Metatheory.Canonicity.CanonicalFormsCandidate
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion

/-! # FX1Poly/Core/BridgeCanonicalFormsCandidate
    — the bridge-type introduction candidate: the unary `pathLam` constructor, zero-axiom

The bridge type `Bridge A left right` (the path type from `left` to `right` in `A`) has a single introduction
`pathLam body` — the path abstraction binding an interval variable, with `body` a value of the carrier under
that binder.  So `isPathLamValue` is the single unary tagged shape — the path-type analogue of `isReflValue`
(`refl`), `option`'s `some`, `either`'s `inl`/`inr` — here with the body living UNDER ONE interval binder
(`scope + 1`), since `gen_pathLam` is a binder constructor (its sole child shifts by one).

This is the canonical-value substrate the dependent `pathApp` (endpoint-β) eliminator member dispatches on: the
path scrutinee arrives as a member of the head-expansion-closed `dataTaitCandidate isPathLamValue`, and the value
case (`path = pathLam body`) fires the endpoint-β rule.  Unlike the structural data eliminators (whose contractum
is a passive branch), `pathApp` is a genuine β-elimination — its contractum `body[argument]` is a substitution —
so the eliminator member supplies the contractum SN as a residue rather than from a structural spine lemma; this
file is only the value-predicate / value-head substrate, shared with both routes.

## Zero-axiom verification

A `pathLam` cell with a normal body is no redex root (`gen_pathLam` is an introduction, not a redex head) and
its `isStepNormalFormBool` reduces to the body's (the one-child spine recursion, the binder shift immaterial to
the boolean).  Mirrors `isReflValue_impliesStepNormalForm`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- The `pathLam` constructor cell over a body under one interval binder. -/
abbrev pathLamValueCell {scope : Nat} (body : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_pathLam () (.childCons body .childNil)

/-- **The pathLam value predicate.**  A term is a bridge value when it is `pathLam body` with the body a
structural normal form (a value of the carrier under the interval binder).  The single unary tagged shape —
`pathLam` is the bridge type's only introduction. -/
def isPathLamValue {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ body : RawTerm (scope + 1), term = pathLamValueCell body ∧ RawTerm.isStepNormalForm body

/-- **PathLam values are structural normal forms.**  A `pathLam` cell with a normal body is no redex root and
its `isStepNormalFormBool` reduces to the body's (the one-child spine recursion).  The sole data obligation of
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isPathLamValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsPathLam : isPathLamValue value) : RawTerm.isStepNormalForm value := by
  obtain ⟨body, valueEq, bodyNormal⟩ := valueIsPathLam
  subst valueEq
  show (RawTerm.isStepNormalFormBool body && true) = true
  rw [Bool.and_true]
  exact bodyNormal

/-- **The bridge data reducibility candidate.**  `CanonicalFormsPredicate isPathLamValue` — the strongly-
normalizing terms that are neutral or reduce to a `pathLam` value — is a full Girard reducibility candidate
(CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the
value-normality fact is `isPathLamValue_impliesStepNormalForm`.  The Tait candidate for the bridge type. -/
theorem bridgeCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isPathLamValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isPathLamValue_impliesStepNormalForm

/-- **The pathLam value-head generator predicate.**  The sole bridge data constructor. -/
def isPathLamValueHead (generator : Generator) : Prop :=
  generator = .gen_pathLam

/-- **The pathLam constructor-head predicate.**  A term is bridge-constructor-headed when it is `pathLam body`
with the body ARBITRARY (no normality side-condition — unlike `isPathLamValue`).  The predicate the dependent
`pathApp` value dispatch fires the endpoint-β on (it fires on `pathLam(anything)`) and the trichotomy concludes;
`isPathLamValue ⊆ isPathLamConstructorHead`. -/
def isPathLamConstructorHead {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ body : RawTerm (scope + 1), term = pathLamValueCell body

/-- **A pathLam value is bridge-constructor-headed.**  Drops the body-normality side-condition of
`isPathLamValue` — the easy inclusion the trichotomy's candidate-side bridge composes with. -/
theorem isPathLamConstructorHead_ofIsPathLamValue {scope : Nat} {term : RawTerm scope}
    (valueIsPathLam : isPathLamValue term) : isPathLamConstructorHead term := by
  obtain ⟨body, valueEq, _bodyNormal⟩ := valueIsPathLam
  exact ⟨body, valueEq⟩

/-- **A pathLam value's root generator is the pathLam value head.**  The candidate-side trichotomy bridge: a
normal bridge value's root is `gen_pathLam`. -/
theorem isPathLamValueHead_ofIsPathLamValue {scope : Nat} {term : RawTerm scope}
    (valueIsPathLam : isPathLamValue term) : isPathLamValueHead term.rootGenerator := by
  obtain ⟨_body, valueEq, _bodyNormal⟩ := valueIsPathLam
  exact congrArg RawTerm.rootGenerator valueEq

/-- **★ Root-generator reconstruction for pathLam.**  A term whose root generator is the bridge constructor IS
bridge-constructor-headed — `pathLam body` structurally.  The conclusion-side trichotomy bridge, recovering the
focus's constructor shape from `reachesValueHead`'s root-generator output.  Mirrors
`isReflConstructorHead_ofValueHead`'s head-recovery (match the cell, `change`+`subst` the root equation), then
collapses the `Unit` payload and the unary body GADT (`[1]`). -/
theorem isPathLamConstructorHead_ofValueHead {scope : Nat} {term : RawTerm scope}
    (rootIsPathLam : isPathLamValueHead term.rootGenerator) : isPathLamConstructorHead term := by
  match term, rootIsPathLam with
  | .mkGen generator payload children, rootIsPathLam =>
      change generator = .gen_pathLam at rootIsPathLam
      subst rootIsPathLam
      match payload, children with
      | (), .childCons body .childNil => exact ⟨body, rfl⟩

end FX1Poly.Core
