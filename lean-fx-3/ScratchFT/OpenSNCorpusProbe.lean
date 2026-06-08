import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.WfContext

/-! Probe (NEVER committed): OSN-2 — open-context SN regression corpus via OB-5.
    Γ = (.empty).cons (Type@e) is a genuine NON-EMPTY well-formed context
    (wfContext_universeBinding). Four open terms typed in Γ, each discharged to
    IsStronglyNormalizing by OB-5 (HasTypeDescPi.stronglyNormalizingOfWfContext):
      1. an open universe code      (ofFormation)            — normal form
      2. an open context variable   (var bridge)             — uses the context
      3. an open identity lambda    (piIntro)                — binder in open ctx
      4. an open beta-redex         (piElim over 3)          — THE redex (non-vacuous)
    The whole point: OB-5 fires on terms living under a non-empty context. -/

namespace FX1Poly.Typed.Spike

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

-- Entry 1: open universe code Type@s in the 1-binding context.
theorem openUniverseCode_sn {profile : PolyProfile}
    (levelExpr subjectLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (universeCodeCell subjectLevel flag : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContext
    (wfContext_universeBinding levelExpr flag)
    (HasTypeDesc.toHasTypeDescPi
      (HasType.toHasTypeDesc
        (HasType.universeFormation
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr flag)) subjectLevel flag)))

-- Entry 2: open context variable var 0 (genuinely uses the context binding).
theorem openVariable_sn {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1) : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContext
    (wfContext_universeBinding levelExpr flag)
    (HasTypeDesc.toHasTypeDescPi
      (HasType.toHasTypeDesc
        (HasType.var
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr flag))
          (⟨0, Nat.succ_pos 0⟩ : Fin 1))))

-- Entry 3: open identity lambda λ(x:Type@s). x — a binder under the open context.
theorem openIdentityLambda_sn {profile : PolyProfile}
    (levelExpr subjectLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)) : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContext
    (wfContext_universeBinding levelExpr flag)
    (HasTypeDescPi.piIntro
      (context := (TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag))
      (domainCode := universeCodeCell subjectLevel flag)
      (codomainCode := universeCodeCell subjectLevel flag)
      (body := variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))
      (domainLevel := subjectLevel.lsucc) (codomainLevel := subjectLevel.lsucc) (flag := flag)
      (HasTypeDesc.toHasTypeDescPi
        (HasType.toHasTypeDesc
          (HasType.universeFormation _ subjectLevel flag)))
      (HasTypeDesc.toHasTypeDescPi
        (HasType.toHasTypeDesc
          (HasType.universeFormation _ subjectLevel flag)))
      (HasTypeDesc.toHasTypeDescPi
        (HasType.toHasTypeDesc
          (HasType.var _ (⟨0, Nat.succ_pos 1⟩ : Fin 2)))))

-- Entry 4: open beta-redex (λ(x:Type@(s+1)). x) Type@s — THE non-vacuous entry (has a redex).
-- Mirrors ClosedSNSmoke.closedIdentityApplication, lifted into the non-empty context Γ.
theorem openBetaRedex_sn {profile : PolyProfile}
    (levelExpr subjectLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
        (universeCodeCell subjectLevel flag) : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContext
    (wfContext_universeBinding levelExpr flag)
    (HasTypeDescPi.piElim
      (context := (TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag))
      (functionTerm := lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
      (argument := universeCodeCell subjectLevel flag)
      (domainCode := universeCodeCell subjectLevel.lsucc flag)
      (codomainCode := universeCodeCell subjectLevel.lsucc flag)
      (HasTypeDescPi.piIntro
        (domainLevel := subjectLevel.lsucc.lsucc) (codomainLevel := subjectLevel.lsucc.lsucc)
        (flag := flag)
        (HasTypeDesc.toHasTypeDescPi
          (HasType.toHasTypeDesc (HasType.universeFormation _ subjectLevel.lsucc flag)))
        (HasTypeDesc.toHasTypeDescPi
          (HasType.toHasTypeDesc (HasType.universeFormation _ subjectLevel.lsucc flag)))
        (HasTypeDesc.toHasTypeDescPi
          (HasType.toHasTypeDesc (HasType.var _ (⟨0, Nat.succ_pos 1⟩ : Fin 2)))))
      (HasTypeDesc.toHasTypeDescPi
        (HasType.toHasTypeDesc (HasType.universeFormation _ subjectLevel flag))))

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.openUniverseCode_sn
#print axioms FX1Poly.Typed.Spike.openVariable_sn
#print axioms FX1Poly.Typed.Spike.openIdentityLambda_sn
#print axioms FX1Poly.Typed.Spike.openBetaRedex_sn
