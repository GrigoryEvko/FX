import FX1Poly.Typed.GrownCheck
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.HasTypeDescPiFormerInversion

/-! Probe: GrownCheck structural helpers (STR-4) — context conversion under pointwise-`Conv`
(+ the Conv-related-binders cons condition + the binder-swap corollary), the target-side Π
exposure, and the lam/app soundness reassembly shapes. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The context-condition extends under CONV-RELATED bindings (generalizes
`convContextCondition_cons`): index 0 compares the weakened bindings (`Conv.rename` of the binding
conversion); successors compare the weakened entries (`Conv.rename` of the original condition). -/
theorem convContextCondition_consConv {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {sourceBinding targetBinding : RawTerm scope}
    (bindingConv : Conv sourceBinding targetBinding)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    ∀ index : Fin (scope + 1),
      Conv ((sourceContext.cons sourceBinding).lookup index)
        ((targetContext.cons targetBinding).lookup index) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show Conv (RawTerm.rename RawRenaming.weaken sourceBinding)
        (RawTerm.rename RawRenaming.weaken targetBinding)
      exact Conv.rename RawRenaming.weaken bindingConv
  | succ k =>
      show Conv (RawTerm.rename RawRenaming.weaken
            (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        (RawTerm.rename RawRenaming.weaken
            (targetContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
      exact Conv.rename RawRenaming.weaken
        (contextConv ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)

mutual

/-- GrownCheck context conversion: a check survives replacing the context by a pointwise-`Conv`
related one, at the SAME target — the var leaf absorbs the lookup change, everything else passes
through structurally. -/
theorem GrownCheck.convContext {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {subject target : RawTerm scope}
    (checked : GrownCheck profile sourceContext subject target) :
    ∀ (targetContext : TypingContext profile scope),
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      GrownCheck profile targetContext subject target :=
  match checked with
  | .var index lookupConverts => fun _targetContext contextConv =>
      .var index ((contextConv index).sym.trans lookupConverts)
  | .universeCode levelExpr flag successorConverts => fun _ _ =>
      .universeCode levelExpr flag successorConverts
  | .former generator payload children levels flag rule isFormation premises outputConverts =>
      fun targetContext contextConv =>
      .former generator payload children levels flag rule isFormation
        (GrownCheckTelescope.convContext premises targetContext contextConv) outputConverts
  | .lam domainCode codomainCode targetConverts bodyChecks => fun targetContext contextConv =>
      .lam domainCode codomainCode targetConverts
        (GrownCheck.convContext bodyChecks (targetContext.cons domainCode)
          (convContextCondition_cons domainCode contextConv))
  | .app domainCode codomainCode functionChecks argumentChecks outputConverts =>
      fun targetContext contextConv =>
      .app domainCode codomainCode
        (GrownCheck.convContext functionChecks targetContext contextConv)
        (GrownCheck.convContext argumentChecks targetContext contextConv)
        outputConverts

/-- Telescope context conversion — the mutual companion. -/
theorem GrownCheckTelescope.convContext {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (premises : GrownCheckTelescope profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      GrownCheckTelescope profile targetContext levels flag children :=
  match premises with
  | .nil _ flag => fun targetContext _ => .nil targetContext flag
  | .cons _ head headLevel restLevels flag rest headChecks restChecks =>
      fun targetContext contextConv =>
      .cons targetContext head headLevel restLevels flag rest
        (GrownCheck.convContext headChecks targetContext contextConv)
        (GrownCheckTelescope.convContext restChecks (targetContext.cons head)
          (convContextCondition_cons head contextConv))

end

/-- The binder-swap corollary — the reflection's swap-the-floating-binder ingredient: a check
under a consed binder survives replacing that binder by a `Conv`-equal one. -/
theorem GrownCheck.convBinder {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {sourceBinding targetBinding : RawTerm scope}
    {subject target : RawTerm (scope + 1)}
    (checked : GrownCheck profile (context.cons sourceBinding) subject target)
    (bindingConv : Conv sourceBinding targetBinding) :
    GrownCheck profile (context.cons targetBinding) subject target :=
  checked.convContext (context.cons targetBinding)
    (convContextCondition_consConv bindingConv (fun _ => Conv.refl _))

/-- Target-side Π EXPOSURE: a typed target `Conv` a Π-code reduces to a Π-code whose components
are `Conv` the originals AND carry their own typings — `reducesToPiTyCode` + SR-star +
`invertPiTyCode`.  The lam-arm soundness ingredient (and the app-arm's, applied at the function's
Π target). -/
theorem HasTypeDescPi.piTargetExposure {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {target domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (wellFormed : WfContextDescPi context)
    (targetTyped :
      HasTypeDescPi profile context target (universeCodeCell targetLevel targetFlag))
    (targetConverts : Conv (piTyCodeCell domainCode codomainCode) target) :
    ∃ (domainReduct : RawTerm scope) (codomainReduct : RawTerm (scope + 1))
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      StepStar target (piTyCodeCell domainReduct codomainReduct) ∧
      Conv domainCode domainReduct ∧ Conv codomainCode codomainReduct ∧
      HasTypeDescPi profile context domainReduct (universeCodeCell domainLevel flag) ∧
      HasTypeDescPi profile (context.cons domainReduct) codomainReduct
        (universeCodeCell codomainLevel flag) := by
  obtain ⟨domainReduct, codomainReduct, targetChain, domainConv, codomainConv⟩ :=
    Conv.reducesToPiTyCode targetConverts.sym
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, _convToCode⟩ :=
    HasTypeDescPi.invertPiTyCode
      (HasTypeDescPi.subjectReductionStar wellFormed targetTyped targetChain)
  exact ⟨domainReduct, codomainReduct, domainLevel, codomainLevel, flag,
    targetChain, domainConv, codomainConv, domainTyped, codomainTyped⟩

/-- Lam-arm soundness REASSEMBLY: given the target's typing, its reduction to a Π-code, the
reduct components' typings, and the body typed at the REDUCT components, the λ types at the
target — `piIntro` + the grown `conv` back along the reduction chain. -/
theorem GrownCheck.lamSoundGivenBodyTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {target domainReduct : RawTerm scope} {codomainReduct body : RawTerm (scope + 1)}
    {targetLevel domainLevel codomainLevel : LevelExpr} {targetFlag flag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context target (universeCodeCell targetLevel targetFlag))
    (targetReduces : StepStar target (piTyCodeCell domainReduct codomainReduct))
    (domainTyped :
      HasTypeDescPi profile context domainReduct (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainReduct) codomainReduct
        (universeCodeCell codomainLevel flag))
    (bodyTyped : HasTypeDescPi profile (context.cons domainReduct) body codomainReduct) :
    HasTypeDescPi profile context (lamCell body) target :=
  HasTypeDescPi.conv targetLevel targetFlag
    (HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped codomainTyped bodyTyped)
    (Conv.fromStepStar targetReduces).sym
    targetTyped

/-- App-arm soundness REASSEMBLY: given the target's typing and the components' typings at the
relation's Π-code, the application types at the target — `piElim` + the grown `conv` through the
output leaf. -/
theorem GrownCheck.appSoundGivenComponentsTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {target functionTerm argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context target (universeCodeCell targetLevel targetFlag))
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode)
    (outputConverts : Conv (RawTerm.subst0 codomainCode argument) target) :
    HasTypeDescPi profile context (appCell functionTerm argument) target :=
  HasTypeDescPi.conv targetLevel targetFlag
    (HasTypeDescPi.piElim functionTyped argumentTyped) outputConverts targetTyped

#print axioms FX1Poly.Typed.convContextCondition_consConv
#print axioms FX1Poly.Typed.GrownCheck.convContext
#print axioms FX1Poly.Typed.GrownCheckTelescope.convContext
#print axioms FX1Poly.Typed.GrownCheck.convBinder
#print axioms FX1Poly.Typed.HasTypeDescPi.piTargetExposure
#print axioms FX1Poly.Typed.GrownCheck.lamSoundGivenBodyTyped
#print axioms FX1Poly.Typed.GrownCheck.appSoundGivenComponentsTyped

end FX1Poly.Typed
