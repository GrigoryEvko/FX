import FX1Poly.Typed.PinnedReflectionLamClassifierResidual
import FX1Poly.Typed.ConvExistentialStrengtheningRefutation

/-! Probe: STR-8b brick iii-b — the BARE λ-classifier pin residual is FALSE.  The STR-1 witness
(the weakened identity λ typed at `Π (var 0). (var 1)` in `[Type@0]`) satisfies EVERY premise of
`PinnedReflectionLamClassifierResidual` — normal, in-image, target+source wf, vacuous condition,
vacuously-injective empty renaming — yet its classifier has no pin
(`variableDomainPi_notConvWeakenImage`).  The discharge route must target the λ-REDUCT residual
directly, where the OUTPUT PIN premise rules this witness out (its instantiated codomain is the
fresh variable itself — unpinnable, so the premises are unsatisfiable there). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem pinnedReflectionLamClassifierResidual_isFalse (profile : PolyProfile) :
    ¬ PinnedReflectionLamClassifierResidual profile := by
  intro residual
  have subjectEq : RawTerm.weaken identityLambda
      = lamCell (variableCell (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)) := rfl
  have lamTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (lamCell (variableCell (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2))) variableDomainPi := by
    have weakenedTyping := weakenedIdentityTypedAtVariableDomainPi profile
    rwa [subjectEq] at weakenedTyping
  have lamNormal : RawTerm.isStepNormalForm
      (lamCell (variableCell (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2))) := by decide
  have targetWellFormed : WfContextDescPi
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0)) :=
    ⟨trivial, LevelExpr.lzero.lsucc, UniverseFlag.standard,
      HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation .empty LevelExpr.lzero UniverseFlag.standard)⟩
  have weakenInjectiveAtZero :
      Function.Injective (RawRenaming.weaken : RawRenaming 0 1) :=
    fun {leftIndex} _rightIndex _imagesAgree => leftIndex.elim0
  obtain ⟨base, classifierPinned, _baseValid⟩ :=
    residual lamTyped lamNormal targetWellFormed RawRenaming.weaken TypingContext.empty
      weakenInjectiveAtZero
      (ContextReflectsRename.ofWeakenCons profile TypingContext.empty (typeZeroCode 0))
      WfContextDescPi.emptyIsWellFormed
      (sourceLam := identityLambda) subjectEq.symm
  exact variableDomainPi_notConvWeakenImage base classifierPinned

end FX1Poly.Typed

#print axioms FX1Poly.Typed.pinnedReflectionLamClassifierResidual_isFalse
