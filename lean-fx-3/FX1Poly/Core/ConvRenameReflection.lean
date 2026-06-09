import FX1Poly.Core.StepRenameReflectAssembly
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.RawTermStrengthen

/-! # FX1Poly/Core/ConvRenameReflection — `Conv` reflects an injective renaming (the grown-strengthening primitive)

`Step.reflectRename` (#1104) reflects a single renamed `Step` back to the source for ANY renaming.  This
file lifts that to the whole convertibility relation: if two RENAMED terms are convertible, their sources
are convertible (given the renaming is term-injective).  The headline corollary, `Conv.reflectWeaken`, is
the missing reflection primitive that grown strengthening — the inverse of `weakenUnderBinding`, blocking
grown η-contraction subject reduction (#477 / PAR-2) — needs in EVERY arm: each arm of the strengthening
induction lands a `Conv classifier` fact under a binder and must strip the `weaken` to descend a scope.

Three lemmas build to it:

  * **`StepStar.reflectRename`** — lift `Step.reflectRename` over a whole `StepStar` chain by induction
    on the chain: a chain out of `rename rho t` reflects to a chain out of `t` whose image is the target.
    No injectivity needed (renaming preserves the term skeleton, so every reduct of a renamed term is the
    image of a reduct of the source).
  * **`RawTerm.weaken_injective`** — `weaken` is injective, because `strengthen` is its partial left
    inverse (`RawTerm.strengthen_weaken : strengthen (weaken t) = some t`, #350): apply `strengthen` to
    both sides and read off `Option.some.inj`.  Works at every scope, including `scope = 0` (where no
    total demotion renaming `Fin 1 → Fin 0` exists — which is why this injective-reflection route, not a
    left-inverse-renaming route, is the correct one).
  * **`Conv.reflectRename`** — `Conv` is `StepStar.Join` (a shared common reduct).  Reflect each join-leg
    through `rho` to a common renamed reduct, then injectivity identifies the two reflected reducts, and
    rejoining them at that shared source reduct gives `Conv` of the sources.

`Conv.reflectWeaken` instantiates `Conv.reflectRename` at `RawRenaming.weaken` with `weaken_injective`.

## Zero-axiom

`StepStar.reflectRename` is `Step.reflectRename` + a chain induction; `weaken_injective` is `congrArg
strengthen` + `Option.some.inj`; `Conv.reflectRename` unfolds the `StepStar.Join` definition of `Conv` and
rejoins.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Each is
audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- Lift `Step.reflectRename` over a whole `StepStar` chain: a chain out of a renamed term reflects to a
chain out of the source whose image under the renaming is the original chain target. -/
theorem StepStar.reflectRename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) :
    ∀ {sourceTerm : RawTerm sourceScope} {targetReduct : RawTerm targetScope},
      StepStar (RawTerm.rename rho sourceTerm) targetReduct →
      ∃ sourceReduct : RawTerm sourceScope,
        StepStar sourceTerm sourceReduct ∧ RawTerm.rename rho sourceReduct = targetReduct := by
  intro sourceTerm targetReduct chain
  generalize hEq : RawTerm.rename rho sourceTerm = startTerm at chain
  induction chain generalizing sourceTerm with
  | refl term => exact ⟨sourceTerm, .refl _, hEq⟩
  | trans headStep tailChain tailIH =>
      subst hEq
      obtain ⟨srcReduct, srcStep, srcImage⟩ := Step.reflectRename rho headStep
      obtain ⟨finalReduct, tailReflected, finalImage⟩ := tailIH srcImage
      exact ⟨finalReduct, .trans srcStep tailReflected, finalImage⟩

/-- Weakening is injective: `strengthen` is its partial left inverse (`RawTerm.strengthen_weaken`). -/
theorem RawTerm.weaken_injective {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (weakenEq : RawTerm.weaken leftTerm = RawTerm.weaken rightTerm) :
    leftTerm = rightTerm := by
  have strengthenEq := congrArg RawTerm.strengthen weakenEq
  rw [RawTerm.strengthen_weaken, RawTerm.strengthen_weaken] at strengthenEq
  exact Option.some.inj strengthenEq

/-- Lifting a renaming preserves injectivity: `lift ρ` sends `0 ↦ 0` and `k+1 ↦ Fin.succ (ρ k)`, so it is
injective whenever `ρ` is.  The binder-case prerequisite for a general (any-injective-renaming)
`rename` injectivity — the substrate the recursive arms of grown strengthening's renaming-reflection would
consume.  Axiom-clean: direct `⟨0,_⟩`/`⟨k+1,_⟩` matching + `Fin.val`/`Nat` reasoning (no `Fin.cases`,
`simp`, or `omega`, all of which pull `propext`). -/
theorem RawRenaming.lift_injective {source target : Nat} {rho : RawRenaming source target}
    (rhoInjective : Function.Injective rho) :
    Function.Injective (RawRenaming.lift rho) := by
  intro firstIndex secondIndex liftEq
  obtain ⟨firstValue, firstBound⟩ := firstIndex
  obtain ⟨secondValue, secondBound⟩ := secondIndex
  match firstValue, secondValue with
  | 0, 0 => rfl
  | 0, secondPred + 1 =>
      have valEq : (0 : Nat)
          = (rho ⟨secondPred, Nat.lt_of_succ_lt_succ secondBound⟩).val + 1 :=
        congrArg Fin.val liftEq
      exact Nat.noConfusion valEq
  | firstPred + 1, 0 =>
      have valEq : (rho ⟨firstPred, Nat.lt_of_succ_lt_succ firstBound⟩).val + 1 = (0 : Nat) :=
        congrArg Fin.val liftEq
      exact Nat.noConfusion valEq
  | firstPred + 1, secondPred + 1 =>
      have succValEq : (rho ⟨firstPred, Nat.lt_of_succ_lt_succ firstBound⟩).val + 1
          = (rho ⟨secondPred, Nat.lt_of_succ_lt_succ secondBound⟩).val + 1 :=
        congrArg Fin.val liftEq
      have renamedEq : rho ⟨firstPred, Nat.lt_of_succ_lt_succ firstBound⟩
          = rho ⟨secondPred, Nat.lt_of_succ_lt_succ secondBound⟩ :=
        Fin.eq_of_val_eq (Nat.succ.inj succValEq)
      have predEq : firstPred = secondPred := congrArg Fin.val (rhoInjective renamedEq)
      subst predEq
      rfl

/-- **★ `Conv` reflects an injective renaming.**  If two renamed terms are convertible, their sources are
convertible, provided the renaming is term-injective.  Reflect both join-chains back through `rho`
(`StepStar.reflectRename`) to a shared renamed reduct, strip the injective renaming to identify the two
reflected reducts, and rejoin them at that source reduct. -/
theorem Conv.reflectRename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (renameInjective : ∀ {leftReduct rightReduct : RawTerm sourceScope},
      RawTerm.rename rho leftReduct = RawTerm.rename rho rightReduct → leftReduct = rightReduct)
    {leftTerm rightTerm : RawTerm sourceScope}
    (convertibility : Conv (RawTerm.rename rho leftTerm) (RawTerm.rename rho rightTerm)) :
    Conv leftTerm rightTerm := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftReflected, leftSourceChain, leftImage⟩ := StepStar.reflectRename rho leftChain
  obtain ⟨rightReflected, rightSourceChain, rightImage⟩ := StepStar.reflectRename rho rightChain
  have imagesAgree : RawTerm.rename rho leftReflected = RawTerm.rename rho rightReflected := by
    rw [leftImage, rightImage]
  have reflectedEq : leftReflected = rightReflected := renameInjective imagesAgree
  exact ⟨leftReflected, leftSourceChain, reflectedEq ▸ rightSourceChain⟩

/-- **★ `Conv` reflects weakening.**  If two weakened terms are convertible, their sources are
convertible — the `RawRenaming.weaken` instance of `Conv.reflectRename`, discharging injectivity by
`RawTerm.weaken_injective`.  This is the reflection primitive grown strengthening (the inverse of
`weakenUnderBinding`) needs: every arm must strip a `weaken` off a `Conv` classifier to descend a scope. -/
theorem Conv.reflectWeaken {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (convertibility : Conv (RawTerm.weaken leftTerm) (RawTerm.weaken rightTerm)) :
    Conv leftTerm rightTerm :=
  Conv.reflectRename RawRenaming.weaken
    (fun imagesAgree => RawTerm.weaken_injective imagesAgree) convertibility

end FX1Poly.Core
