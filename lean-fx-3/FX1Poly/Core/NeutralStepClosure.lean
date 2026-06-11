import FX1Poly.Core.StepInversion
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # Foundation/PolyCell/Core/NeutralStepClosure
    — a neutral term's one-step reduct is still neutral (`IsNeutral` is `Step`-closed)

`IsNeutral` (`NeutralTerm.lean`) carves out the terms that are stuck at the root: a variable, or an
elimination form whose *principal* child is itself neutral, so no root reduction (β / ι) can fire.  This
file proves the matching closure fact: **a neutral term cannot step OUT of neutrality** — every one-step
reduct of a neutral term is again neutral.  Concretely, a neutral can only undergo a *congruence* step
(some child reduces), never a root redex, and a congruence step preserves the stuck shape: the principal
child either stays the same neutral, or steps to a neutral by induction; a non-principal child stepping
leaves the principal child (hence the neutrality) untouched.

This is the `neutralClosedUnderStep` obligation that `CanonicalFormsCandidate.lean`'s CR2
(`CanonicalFormsPredicate.closedUnderStep`) and the full `IsReducibilityCandidate` bundle
(`CanonicalFormsPredicate.isReducibilityCandidate`) take as a hypothesis.  Discharging it here turns the
neutral half of every canonical-forms candidate unconditional — one of the two remaining data facts on
the road to unconditional bool reducibility and closed-data canonicity.

## Proof shape

Induction on the `IsNeutral` derivation, one arm per elimination form.  Each arm inverts the step with the
matching `Step.from_X` inversion (`StepInversion.lean`), which splits into iota disjuncts (the principal
child equals a CONSTRUCTOR) and congruence disjuncts (a child steps):

* **Iota disjuncts are impossible.**  The iota arm asserts the principal child equals a constructor cell
  (`gen_lam` / `gen_pair` / `gen_boolTrue` / `gen_natSucc` / … / `gen_refl`).  But the principal child is
  neutral, and a neutral's `rootGenerator` is always an elimination head, never a constructor.  Casing the
  principal child's neutrality witness (subject free — the propext-safe direction) sends its `rootGenerator`
  to a concrete elimination generator, refuted against the constructor generator by `Generator.noConfusion`
  (the `IsNeutral.not_lam` pattern from `ReducibilityCandidateArrow.lean`, generalized over every
  constructor).
* **Congruence on the principal child** uses the arm's induction hypothesis to get a neutral reduct, then
  rebuilds the same elimination form around it.
* **Congruence on a non-principal child** leaves the principal child — hence its neutrality — unchanged, so
  the same elimination constructor rebuilds the neutral with the original principal-neutrality witness.

The `var` arm is vacuous: a variable has no reducts (`noStep_var`).

## Zero-axiom verification

Induction on a `Prop` inductive (the `IsNeutral` recursor), `Step.from_X` inversions (cased Step ctors,
no propext), `Generator.noConfusion ∘ congrArg RawTerm.rootGenerator` (the shipped propext-free
constructor-disjointness refutation), and goal-only `rw` (`Eq.mpr`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **`IsNeutral` is closed under `Step`.**  A neutral term's every one-step reduct is again neutral: a
neutral can only step by congruence (no root redex fires, because its principal child is neutral, never a
constructor), and congruence preserves the stuck shape.  This is the `neutralClosedUnderStep` hypothesis of
`CanonicalFormsPredicate.closedUnderStep` (`CanonicalFormsCandidate.lean`), discharged unconditionally. -/
theorem IsNeutral.closedUnderStep {scope : Nat} {term reduct : RawTerm scope}
    (neutral : IsNeutral term) (step : Step term reduct) : IsNeutral reduct := by
  induction neutral generalizing reduct with
  | var index =>
      exact (noStep_var index step).elim
  | app headIsNeutral headIH =>
      rcases Step.from_app step with
        ⟨_domainAnn, _body, headEq, _⟩ | ⟨_fnAfter, reductEq, stepHead⟩ | ⟨_argAfter, reductEq, _⟩
      · cases headIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator headEq)
      · rw [reductEq]; exact IsNeutral.app (headIH stepHead)
      · rw [reductEq]; exact IsNeutral.app headIsNeutral
  | fst argumentIsNeutral argumentIH =>
      rcases Step.from_fst step with
        ⟨_first, _second, argumentEq, _⟩ | ⟨_argAfter, reductEq, stepArgument⟩
      · cases argumentIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator argumentEq)
      · rw [reductEq]; exact IsNeutral.fst (argumentIH stepArgument)
  | snd argumentIsNeutral argumentIH =>
      rcases Step.from_snd step with
        ⟨_first, _second, argumentEq, _⟩ | ⟨_argAfter, reductEq, stepArgument⟩
      · cases argumentIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator argumentEq)
      · rw [reductEq]; exact IsNeutral.snd (argumentIH stepArgument)
  | boolElim scrutineeIsNeutral scrutineeIH =>
      rcases Step.from_boolElim step with
        ⟨scrutineeEq, _⟩ | ⟨scrutineeEq, _⟩ | ⟨_motiveAfter, reductEq, _⟩
        | ⟨_thenAfter, reductEq, _⟩ | ⟨_elseAfter, reductEq, _⟩
        | ⟨_scrutAfter, reductEq, stepScrutinee⟩
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · rw [reductEq]; exact IsNeutral.boolElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.boolElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.boolElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.boolElim (scrutineeIH stepScrutinee)
  | natElim scrutineeIsNeutral scrutineeIH =>
      rcases Step.from_natElim step with
        ⟨scrutineeEq, _⟩ | ⟨_predecessor, scrutineeEq, _⟩ | ⟨_motiveAfter, reductEq, _⟩
        | ⟨_zeroAfter, reductEq, _⟩ | ⟨_succAfter, reductEq, _⟩
        | ⟨_scrutAfter, reductEq, stepScrutinee⟩
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · rw [reductEq]; exact IsNeutral.natElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.natElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.natElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.natElim (scrutineeIH stepScrutinee)
  | natRec scrutineeIsNeutral scrutineeIH =>
      rcases Step.from_natRec step with
        ⟨scrutineeEq, _⟩ | ⟨_predecessor, scrutineeEq, _⟩ | ⟨_motiveAfter, reductEq, _⟩
        | ⟨_zeroAfter, reductEq, _⟩ | ⟨_succAfter, reductEq, _⟩
        | ⟨_scrutAfter, reductEq, stepScrutinee⟩
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · rw [reductEq]; exact IsNeutral.natRec scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.natRec scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.natRec scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.natRec (scrutineeIH stepScrutinee)
  | listElim scrutineeIsNeutral scrutineeIH =>
      rcases Step.from_listElim step with
        ⟨scrutineeEq, _⟩ | ⟨_headVal, _tailVal, scrutineeEq, _⟩ | ⟨_motiveAfter, reductEq, _⟩
        | ⟨_nilAfter, reductEq, _⟩ | ⟨_consAfter, reductEq, _⟩
        | ⟨_scrutAfter, reductEq, stepScrutinee⟩
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · rw [reductEq]; exact IsNeutral.listElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.listElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.listElim scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.listElim (scrutineeIH stepScrutinee)
  | optionMatch scrutineeIsNeutral scrutineeIH =>
      rcases Step.from_optionMatch step with
        ⟨scrutineeEq, _⟩ | ⟨_value, scrutineeEq, _⟩ | ⟨_motiveAfter, reductEq, _⟩
        | ⟨_noneAfter, reductEq, _⟩ | ⟨_someAfter, reductEq, _⟩
        | ⟨_scrutAfter, reductEq, stepScrutinee⟩
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · rw [reductEq]; exact IsNeutral.optionMatch scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.optionMatch scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.optionMatch scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.optionMatch (scrutineeIH stepScrutinee)
  | eitherMatch scrutineeIsNeutral scrutineeIH =>
      rcases Step.from_eitherMatch step with
        ⟨_value, scrutineeEq, _⟩ | ⟨_value, scrutineeEq, _⟩ | ⟨_motiveAfter, reductEq, _⟩
        | ⟨_leftAfter, reductEq, _⟩ | ⟨_rightAfter, reductEq, _⟩
        | ⟨_scrutAfter, reductEq, stepScrutinee⟩
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · cases scrutineeIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator scrutineeEq)
      · rw [reductEq]; exact IsNeutral.eitherMatch scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.eitherMatch scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.eitherMatch scrutineeIsNeutral
      · rw [reductEq]; exact IsNeutral.eitherMatch (scrutineeIH stepScrutinee)
  | idJ witnessIsNeutral witnessIH =>
      rcases Step.from_idJ step with
        ⟨_rawWitness, witnessEq, _⟩ | ⟨_baseAfter, reductEq, _⟩ | ⟨_witnessAfter, reductEq, stepWitness⟩
      · cases witnessIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator witnessEq)
      · rw [reductEq]; exact IsNeutral.idJ witnessIsNeutral
      · rw [reductEq]; exact IsNeutral.idJ (witnessIH stepWitness)
  | idStrictRec witnessIsNeutral witnessIH =>
      rcases Step.from_idStrictRec step with
        ⟨_rawWitness, witnessEq, _⟩ | ⟨_baseAfter, reductEq, _⟩ | ⟨_witnessAfter, reductEq, stepWitness⟩
      · cases witnessIsNeutral <;>
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator witnessEq)
      · rw [reductEq]; exact IsNeutral.idStrictRec witnessIsNeutral
      · rw [reductEq]; exact IsNeutral.idStrictRec (witnessIH stepWitness)

end FX1Poly.Core
