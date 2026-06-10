import FX1Poly.Typed.GrownCheckContextConversion
import FX1Poly.Typed.CurryFixpointDivergence
import FX1Poly.Typed.TypedFragmentAcyclicity

/-! Probe: the RAW GrownCheck relation is UNSOUND even at a typed target (STR-5 refutation).

The exploit threads the Curry fix-point TYPE `X := curryOmega (λT. Π T. Type@0)` — which `Conv`-unfolds
to `Π X. Type@0` — through the app arm's floating Π-code: Ω = (λx.xx)(λx.xx) then CHECKS at `Type@0`
(a typed target!) while Ω is untypable (SN-043).  Soundness of the raw relation is FALSE; typehood must
enter the strengthening pipeline elsewhere. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The Π-former body `Π (var 0). Type@0` — the recursive-type generator's body. -/
def piFormerBody : RawTerm 1 :=
  piTyCodeCell (variableCell ⟨0, Nat.succ_pos 0⟩) (typeZeroCode 2)

/-- The Π-former generator `λT. Π T. Type@0`. -/
def piFormerLambda : RawTerm 0 :=
  lamCell piFormerBody

/-- The recursive Π-type `X := curryOmega (λT. Π T. Type@0)` — the ill-founded type code with
`X ~Conv~ Π X. Type@0`. -/
def recursivePiType : RawTerm 0 :=
  curryOmega piFormerLambda

/-- `X` reduces to `Π X. Type@0` in two steps: the curry unfolding, then β (the subst0 of the
Π-former body at `X` computes definitionally to `Π X. Type@0`). -/
theorem recursivePiType_reducesToPi :
    StepStar recursivePiType (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
  have betaStep : Step (appCell piFormerLambda recursivePiType)
      (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
    Step.beta
  StepStar.trans (curryOmega_step piFormerLambda) (StepStar.single betaStep)

/-- `X ~Conv~ Π X. Type@0` — the recursive-type unfolding as a conversion. -/
theorem recursivePiType_convPi :
    Conv recursivePiType (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
  Conv.fromStepStar recursivePiType_reducesToPi

/-- The self-application body `(var 0)(var 0)` CHECKS at `Type@0` under the context `[X]` — the
var-arm leaves absorb the recursive unfolding (weakened). -/
theorem selfApplicationBodyChecks (profile : PolyProfile) :
    GrownCheck profile
      ((TypingContext.empty (profile := profile)).cons recursivePiType)
      (appCell (variableCell ⟨0, Nat.succ_pos 0⟩) (variableCell ⟨0, Nat.succ_pos 0⟩))
      (typeZeroCode 1) :=
  have lookupConvPi : Conv (RawTerm.weaken recursivePiType)
      (piTyCodeCell (RawTerm.weaken recursivePiType) (typeZeroCode 2)) :=
    Conv.rename RawRenaming.weaken recursivePiType_convPi
  GrownCheck.app (RawTerm.weaken recursivePiType) (typeZeroCode 2)
    (GrownCheck.var ⟨0, Nat.succ_pos 0⟩ lookupConvPi)
    (GrownCheck.var ⟨0, Nat.succ_pos 0⟩ (Conv.refl _))
    (Conv.refl _)

/-- The self-applicator `λx. x x` CHECKS at the honest-looking Π-code `Π X. Type@0`. -/
theorem selfApplicationChecksAtPi (profile : PolyProfile) :
    GrownCheck profile (TypingContext.empty (profile := profile))
      selfApplicationLambda
      (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
  GrownCheck.lam recursivePiType (typeZeroCode 1)
    (Conv.refl _)
    (selfApplicationBodyChecks profile)

/-- The self-applicator ALSO checks at the recursive type `X` itself (the unfolding read
backwards through the λ-arm's `Conv` leaf). -/
theorem selfApplicationChecksAtRecursiveType (profile : PolyProfile) :
    GrownCheck profile (TypingContext.empty (profile := profile))
      selfApplicationLambda
      recursivePiType :=
  GrownCheck.lam recursivePiType (typeZeroCode 1)
    recursivePiType_convPi.sym
    (selfApplicationBodyChecks profile)

/-- ★ **Ω CHECKS at `Type@0`** — the untypable diverging combinator passes the raw relation at a
TYPED target, by routing the app arm's floating Π-code through the recursive type `X`. -/
theorem omegaChecksAtTypeZero (profile : PolyProfile) :
    GrownCheck profile (TypingContext.empty (profile := profile))
      omegaCombinator
      (typeZeroCode 0) :=
  GrownCheck.app recursivePiType (typeZeroCode 1)
    (selfApplicationChecksAtPi profile)
    (selfApplicationChecksAtRecursiveType profile)
    (Conv.refl _)

/-- ★★ **Raw-relation soundness is FALSE, even with a typed target and a well-formed context**:
were every `GrownCheck` at a typed target sound, Ω would be well-typed — contradicting
`omegaCombinator_notClosedWellTyped` (SN-043). -/
theorem grownCheckRawSoundness_isFalse (profile : PolyProfile) :
    ¬ (∀ (subject target : RawTerm 0) (targetLevel : LevelExpr) (targetFlag : UniverseFlag),
        WfContextDescPi (TypingContext.empty (profile := profile)) →
        HasTypeDescPi profile TypingContext.empty target
          (universeCodeCell targetLevel targetFlag) →
        GrownCheck profile TypingContext.empty subject target →
        HasTypeDescPi profile TypingContext.empty subject target) := by
  intro soundnessClaim
  exact omegaCombinator_notClosedWellTyped
    ⟨typeZeroCode 0,
      soundnessClaim omegaCombinator (typeZeroCode 0) LevelExpr.lzero.lsucc
        UniverseFlag.standard
        WfContextDescPi.emptyIsWellFormed
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero
            UniverseFlag.standard))
        (omegaChecksAtTypeZero profile)⟩

#print axioms FX1Poly.Typed.recursivePiType_convPi
#print axioms FX1Poly.Typed.omegaChecksAtTypeZero
#print axioms FX1Poly.Typed.grownCheckRawSoundness_isFalse

end FX1Poly.Typed
