import LeanFX2.Reduction.Step

/-! # Reduction/StepStar — reflexive-transitive closure of Step.

`StepStar source target` chains zero-or-more `Step`s.  The two-Ty +
two-RawTerm signature mirrors `Step`'s relaxed shape (lean-fx-2's
raw-aware Term threads `RawTerm.fst pairRaw` into `Term.snd`'s type
which forces non-trivial Ty mismatches at certain reductions).

## Constructors

* `refl term` — every term is in its own RT closure (zero steps)
* `step single rest` — one Step prepended to a StepStar tail

## Operations

* `StepStar.snoc chain single` — append a single Step at the end
* `StepStar.append chain1 chain2` — concatenate two chains
* `StepStar.fromStep single` — single-step ⇒ multi-step

## mapStep abstraction

`StepStar.mapStep` lifts a Term-mapping that respects single-step
reduction into one that respects RT closure.  This single lifter
replaces ~13 cong rules in lean-fx (StepStar.app_cong,
StepStar.lam_cong, etc.) with 1-line corollary applications per
`feedback_lean_mapStep_pattern`.

## Cast helpers

Same shape as Step's: castSourceType, castTargetType,
castSourceTerm, castTargetTerm.  Used at boundaries where
StepStar witnesses transit through propositionally equal types
or terms.
-/

namespace LeanFX2

/-- Reflexive-transitive closure of `Step`.  Two Ty + two RawTerm
indices match `Step`'s signature — composition of `Step`s naturally
threads through changing Ty/raw indices. -/
inductive StepStar :
    ∀ {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {sourceType targetType : Ty level scope}
      {sourceRaw targetRaw : RawTerm scope},
      Term context sourceType sourceRaw →
      Term context targetType targetRaw →
      Prop
  /-- The reflexive constructor: zero steps. -/
  | refl {mode level scope} {context : Ctx mode level scope}
      {someType : Ty level scope} {someRaw : RawTerm scope}
      (someTerm : Term context someType someRaw) :
      StepStar someTerm someTerm
  /-- Prepend a single `Step` to an existing chain. -/
  | step {mode level scope} {context : Ctx mode level scope}
      {sourceType middleType targetType : Ty level scope}
      {sourceRaw middleRaw targetRaw : RawTerm scope}
      {sourceTerm : Term context sourceType sourceRaw}
      {middleTerm : Term context middleType middleRaw}
      {targetTerm : Term context targetType targetRaw} :
      Step sourceTerm middleTerm →
      StepStar middleTerm targetTerm →
      StepStar sourceTerm targetTerm

/-- Append a `Step` at the end of a `StepStar` chain. -/
theorem StepStar.snoc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm middleTerm)
    (singleStep : Step middleTerm targetTerm) :
    StepStar sourceTerm targetTerm := by
  induction chain with
  | refl _ => exact StepStar.step singleStep (StepStar.refl _)
  | step head _ tailIH => exact StepStar.step head (tailIH singleStep)

/-- Concatenate two `StepStar` chains. -/
theorem StepStar.append
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (chainLeft : StepStar sourceTerm middleTerm)
    (chainRight : StepStar middleTerm targetTerm) :
    StepStar sourceTerm targetTerm := by
  induction chainLeft with
  | refl _ => exact chainRight
  | step head _ tailIH => exact StepStar.step head (tailIH chainRight)

/-- Lift a single `Step` into a `StepStar` chain of length 1. -/
theorem StepStar.fromStep
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    StepStar sourceTerm targetTerm :=
  StepStar.step singleStep (StepStar.refl _)

/-! ## mapStep — the cong-rule lifter.

`StepStar.mapStep` takes a Term-transformer whose action commutes
with single Step reduction and lifts it into one that commutes
with multi-step.  Used to derive every congruence rule of StepStar
in 1 line.

Concretely: if `singleStepRespectful` says "every Step on inner
terms gives a Step on the wrapped output", then `mapStep` gives
"every StepStar on inner terms gives a StepStar on the wrapped
output."

The Term-transformer is allowed to change its source/target Ty
and raw indices — both inputs and outputs of the transformer are
indexed Term values.  This generality lets a single mapStep cover
binders (e.g., `Term.lam`), eliminators (e.g., `Term.app`,
`Term.appPi`), and projections.  Since the typed Term's signature
varies per arity, mapStep is stated for the simplest unary form;
N-ary cong rules apply mapStep at one position at a time. -/

theorem StepStar.mapStep
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerSourceType innerTargetType : Ty level scope}
    {innerSourceRawA innerSourceRawB : RawTerm scope}
    {innerSourceTerm : Term context innerSourceType innerSourceRawA}
    {innerTargetTerm : Term context innerTargetType innerSourceRawB}
    (mapInnerToOuter :
      ∀ {tyMid : Ty level scope} {rawMid : RawTerm scope},
        Term context tyMid rawMid →
        Σ' (tyOut : Ty level scope) (rawOut : RawTerm scope),
          Term context tyOut rawOut)
    (mapInnerStep :
      ∀ {tyA tyB : Ty level scope} {rawA rawB : RawTerm scope}
        {termA : Term context tyA rawA} {termB : Term context tyB rawB},
        Step termA termB →
        Step (mapInnerToOuter termA).snd.snd (mapInnerToOuter termB).snd.snd)
    (chain : StepStar innerSourceTerm innerTargetTerm) :
    StepStar (mapInnerToOuter innerSourceTerm).snd.snd
             (mapInnerToOuter innerTargetTerm).snd.snd := by
  induction chain with
  | refl term => exact StepStar.refl (mapInnerToOuter term).snd.snd
  | step head _ tailIH => exact StepStar.step (mapInnerStep head) tailIH

/-! ## Cast helpers — propositional transport for indices. -/

/-- Replace the source Ty by a propositionally equal Ty. -/
theorem StepStar.castSourceType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    StepStar (typeEquality ▸ sourceTerm) targetTerm := by
  cases typeEquality
  exact chain

/-- Replace the target Ty by a propositionally equal Ty. -/
theorem StepStar.castTargetType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    StepStar sourceTerm (typeEquality ▸ targetTerm) := by
  cases typeEquality
  exact chain

/-- Replace the source Term by a propositionally equal Term. -/
theorem StepStar.castSourceTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceOriginal sourceReplacement : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (sourceEquality : sourceOriginal = sourceReplacement)
    (chain : StepStar sourceOriginal targetTerm) :
    StepStar sourceReplacement targetTerm := by
  cases sourceEquality
  exact chain

/-- Replace the target Term by a propositionally equal Term. -/
theorem StepStar.castTargetTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (chain : StepStar sourceTerm targetOriginal) :
    StepStar sourceTerm targetReplacement := by
  cases targetEquality
  exact chain

end LeanFX2
