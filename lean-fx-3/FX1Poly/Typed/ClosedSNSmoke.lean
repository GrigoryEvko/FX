import FX1Poly.Typed.ClosedLevelIndexed

/-! # FX1Poly/Typed/ClosedSNSmoke
    — first UNCONDITIONAL strong-normalization results via the level-indexed fundamental theorem

Every strong-normalization result so far in the level-indexed lane has been CONDITIONAL on the (still
unassembled) `HasTypeDescPi.rec` fundamental theorem — the closed handoffs in `ClosedLevelIndexed.lean` take
the FT conclusion as a hypothesis.  This file ships the first UNCONDITIONAL SN theorems for CONCRETE closed
terms: where the term's level-indexed FT conclusion can be built directly by composing the already-shipped FT
ARMS at the empty context (no recursor needed, because these concrete terms exercise a fixed, finite set of
arms), the closed-SN handoff discharges it to plain `IsStronglyNormalizing`.

This is the end-to-end validation of the whole chain — FT arm ⟶ closed reducibility ⟶ CR1 ⟶ empty-renaming
SN reflection ⟶ `IsStronglyNormalizing` — on real closed terms, and a regression corpus for the arms.  It
demonstrates that nothing in the arms or the handoff is vacuous: they compose into genuine, hypothesis-free
SN.

## Zero-axiom verification

Each theorem is a single composition `closedSubjectStronglyNormalizingFromLevelIndexed _ (<FT arm at empty>)`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **UNCONDITIONAL strong normalization of a closed universe code.**  The first end-to-end SN result via the
level-indexed fundamental theorem: the `universeFormation` arm at the empty context makes `universeCodeCell
levelExpr flag` a level-indexed fundamental member of its parent universe, and the closed-SN handoff (CR1 +
empty-renaming reflection) discharges it to plain `IsStronglyNormalizing` — no hypothesis. -/
theorem universeCode_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (universeCodeCell levelExpr flag : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalUniverseFormationLevelIndexed emptyLevelVector 0
      (TypingContext.empty : TypingContext profile 0) levelExpr flag)

/-- **UNCONDITIONAL strong normalization of a closed Π type code between universe codes.**  Composes the
Π-former arm (domain + codomain both the `universeFormation` arm, quantified over the level) at the empty
context with the closed-SN handoff.  Demonstrates the dependent former arm fires end-to-end, hypothesis-free,
on a concrete closed type. -/
theorem closedPiBetweenUniverses_stronglyNormalizing {profile : PolyProfile}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (piTyCodeCell (universeCodeCell domainLevel flag)
        (universeCodeCell codomainLevel flag) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalPiFormationLevelIndexed emptyLevelVector 0
      (domainLevel := domainLevel.lsucc) (codomainLevel := codomainLevel.lsucc)
      (formerLevel := LevelExpr.lmax domainLevel.lsucc codomainLevel.lsucc) (flag := flag)
      (fun aboveLevel =>
        fundamentalUniverseFormationLevelIndexed emptyLevelVector aboveLevel
          (TypingContext.empty : TypingContext profile 0) domainLevel flag)
      (fun headLevel =>
        fundamentalUniverseFormationLevelIndexed (levelCons headLevel emptyLevelVector) 0
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell domainLevel flag)) codomainLevel flag))

/-- **UNCONDITIONAL strong normalization of the closed identity function on a universe.**  The term
`λ (x : Type@e). x = lamCell (variableCell 0)`, at type `Π (Type@e). Type@e`, is `IsStronglyNormalizing` —
proved by composing the `piIntro` arm (domain + codomain supplied by the `universeFormation` arm; BODY by the
`var` arm at index 0) at the empty context, then the closed-SN handoff.  This is the first unconditional SN
for a closed term with a LAMBDA and a BOUND VARIABLE — exercising `fundamentalPiIntroLevelIndexed` and
`fundamentalVarLevelIndexed` together end-to-end (the heart of the fundamental theorem), hypothesis-free.
The body's `var` lookup `(empty.cons (Type@e)).lookup 0` is the weakened binding, definitionally the
codomain `Type@e`, so the var arm feeds `piIntro`'s body premise directly.  The Fin-1 index is written
`⟨0, Nat.succ_pos 0⟩` (NOT the `(0 : Fin 1)` OfNat numeral, which pulls `propext`). -/
theorem closedIdentityOnUniverse_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalPiIntroLevelIndexed (context := (TypingContext.empty : TypingContext profile 0))
      emptyLevelVector 0
      (domainCode := universeCodeCell levelExpr flag)
      (codomainCode := universeCodeCell levelExpr flag)
      (body := variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
      (domainLevel := levelExpr.lsucc) (codomainLevel := levelExpr.lsucc) (flag := flag)
      (fundamentalUniverseFormationLevelIndexed emptyLevelVector (0 + 1)
        (TypingContext.empty : TypingContext profile 0) levelExpr flag)
      (fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) (0 + 1)
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        levelExpr flag)
      (fundamentalVarLevelIndexed (levelCons (0 + 1) emptyLevelVector)
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

end FX1Poly.Typed
