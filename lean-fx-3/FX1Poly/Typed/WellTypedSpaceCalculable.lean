import FX1Poly.Core.SpaceBound
import FX1Poly.Typed.WellTypedCostCalculable

/-! # FX1Poly/Typed/WellTypedSpaceCalculable
    — ★ every well-typed FX program has calculable SPACE (COST-3 brick 6, typed half)

The Dim-15 twin of `WellTypedCostCalculable`: typed SN feeds the kernel
space bound with zero glue.  Every well-typed program carries a
computable bound on the size of EVERY term its canonical evaluation
visits — input, all intermediates, and the normal form.

Honest scope: the bound covers the CANONICAL strategy's intermediates
(the path the shipped normalizer takes), computed FROM THE TERM; typing
contributes totality.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-- ★ **The space calculator for closed well-typed programs**: a
computable bound on the size of every term the canonical evaluation
visits. -/
def HasTypeDescPi.spaceCalculator {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) : Nat :=
  RawTerm.spaceBound subject derivation.closedStronglyNormalizing

/-- The space calculator is SOUND: every canonically-visited term of a
closed well-typed program has size at most `spaceCalculator`. -/
theorem HasTypeDescPi.spaceCalculator_isSound {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier)
    {intermediate : RawTerm 0}
    (visited : RawTerm.OnCanonicalPath subject intermediate) :
    RawTerm.size intermediate ≤ derivation.spaceCalculator :=
  RawTerm.spaceBound_isSound derivation.closedStronglyNormalizing visited

/-- The open twin over a well-formed context. -/
def HasTypeDescPi.spaceCalculatorOpen {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (derivation : HasTypeDescPi profile context subject classifier) : Nat :=
  RawTerm.spaceBound subject
    (derivation.stronglyNormalizingOfWfContextDesc contextWellFormed)

/-- Open-program space soundness. -/
theorem HasTypeDescPi.spaceCalculatorOpen_isSound {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (derivation : HasTypeDescPi profile context subject classifier)
    {intermediate : RawTerm scope}
    (visited : RawTerm.OnCanonicalPath subject intermediate) :
    RawTerm.size intermediate ≤ derivation.spaceCalculatorOpen contextWellFormed :=
  RawTerm.spaceBound_isSound
    (derivation.stronglyNormalizingOfWfContextDesc contextWellFormed) visited

/-- ★ **Every closed well-typed FX program has calculable space**: a
computable bound covering the input, every canonical intermediate, and
THE computed normal form (the Dim-15 §6.3 promise at the kernel,
completing the time half of `wellTypedClosedProgram_costIsCalculable`). -/
theorem wellTypedClosedProgram_spaceIsCalculable {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    (∀ {intermediate : RawTerm 0},
        RawTerm.OnCanonicalPath subject intermediate →
        RawTerm.size intermediate ≤ derivation.spaceCalculator)
      ∧ RawTerm.size
          (RawTerm.normalize subject derivation.closedStronglyNormalizing)
          ≤ derivation.spaceCalculator :=
  ⟨fun visited => derivation.spaceCalculator_isSound visited,
   RawTerm.normalize_size_le_spaceBound subject derivation.closedStronglyNormalizing⟩

end FX1Poly.Typed
