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

/-- **UNCONDITIONAL strong normalization of a closed β-redex.**  The application
`(λ (x : Type@(e+1)). x) (Type@e) = appCell (lamCell (variableCell 0)) (universeCodeCell e flag)` is
`IsStronglyNormalizing` — composing the `piElim` (application) arm over the identity function (itself the
`piIntro` + `var` composition) and the argument `Type@e : Type@(e+1)` (the `universeFormation` arm), all at
the empty context, then the closed-SN handoff.  First unconditional SN with an APPLICATION / β-redex: it
exercises `fundamentalPiElimLevelIndexed` AND the `subst0 codomainCode argument` in its conclusion (which
reduces definitionally here, the codomain being a closed cell), end-to-end — the reducing case of the
machinery, hypothesis-free. -/
theorem closedIdentityApplication_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalPiElimLevelIndexed (context := (TypingContext.empty : TypingContext profile 0))
      emptyLevelVector (0 + 1)
      (functionTerm := lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (argument := universeCodeCell levelExpr flag)
      (domainCode := universeCodeCell levelExpr.lsucc flag)
      (codomainCode := universeCodeCell levelExpr.lsucc flag)
      (fundamentalPiIntroLevelIndexed (context := (TypingContext.empty : TypingContext profile 0))
        emptyLevelVector 0
        (domainCode := universeCodeCell levelExpr.lsucc flag)
        (codomainCode := universeCodeCell levelExpr.lsucc flag)
        (body := variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (domainLevel := levelExpr.lsucc.lsucc) (codomainLevel := levelExpr.lsucc.lsucc) (flag := flag)
        (fundamentalUniverseFormationLevelIndexed emptyLevelVector (0 + 1)
          (TypingContext.empty : TypingContext profile 0) levelExpr.lsucc flag)
        (fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) (0 + 1)
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr.lsucc flag)) levelExpr.lsucc flag)
        (fundamentalVarLevelIndexed (levelCons (0 + 1) emptyLevelVector)
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr.lsucc flag)) (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (fundamentalUniverseFormationLevelIndexed emptyLevelVector 0
        (TypingContext.empty : TypingContext profile 0) levelExpr flag))

/-- **UNCONDITIONAL strong normalization of a closed Σ type code between universe codes.**  The Σ twin of
`closedPiBetweenUniverses_stronglyNormalizing`: composes the Σ-former arm (domain + codomain both the
`universeFormation` arm) at the empty context with the closed-SN handoff.  This is the FIRST end-to-end,
hypothesis-free SN result exercising `fundamentalSigmaFormationLevelIndexed` — demonstrating the Σ-formation
arm is non-vacuous and composes through to plain `IsStronglyNormalizing`, exactly as the Π-formation arm does.
Unlike Π's codomain premise (a `∀ headLevel` family), Σ's codomain premise is a single conclusion fixed at
`headLevel = predLevel + 1`. -/
theorem closedSigmaBetweenUniverses_stronglyNormalizing {profile : PolyProfile}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (sigmaTyCodeCell (universeCodeCell domainLevel flag)
        (universeCodeCell codomainLevel flag) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalSigmaFormationLevelIndexed emptyLevelVector 0
      (domainLevel := domainLevel.lsucc) (codomainLevel := codomainLevel.lsucc)
      (formerLevel := LevelExpr.lmax domainLevel.lsucc codomainLevel.lsucc) (flag := flag)
      (fun aboveLevel =>
        fundamentalUniverseFormationLevelIndexed emptyLevelVector aboveLevel
          (TypingContext.empty : TypingContext profile 0) domainLevel flag)
      (fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) 0
        ((TypingContext.empty : TypingContext profile 0).cons
          (universeCodeCell domainLevel flag)) codomainLevel flag))

/-- **UNCONDITIONAL strong normalization of the closed CONSTANT function on a universe.**  The term
`λ (x : Type@e). Type@0 = lamCell (universeCodeCell 0 flag)`, at type `Π (Type@e). Type@1`, is
`IsStronglyNormalizing` — the discarding companion to `closedIdentityOnUniverse_stronglyNormalizing`: the body
IGNORES the bound variable (it is `Type@0`, not the `var`), so the `piIntro` arm's BODY premise is supplied by
the `universeFormation` arm at the extended context rather than the `var` arm.  Exercises the var-free body
case of `fundamentalPiIntroLevelIndexed` end-to-end, hypothesis-free — the piIntro arm fires whether the body
uses the binder or discards it. -/
theorem closedConstantLambda_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (universeCodeCell LevelExpr.lzero flag) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalPiIntroLevelIndexed (context := (TypingContext.empty : TypingContext profile 0))
      emptyLevelVector 0
      (domainCode := universeCodeCell levelExpr flag)
      (codomainCode := universeCodeCell LevelExpr.lzero.lsucc flag)
      (body := universeCodeCell LevelExpr.lzero flag)
      (domainLevel := levelExpr.lsucc) (codomainLevel := LevelExpr.lzero.lsucc.lsucc) (flag := flag)
      (fundamentalUniverseFormationLevelIndexed emptyLevelVector (0 + 1)
        (TypingContext.empty : TypingContext profile 0) levelExpr flag)
      (fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) (0 + 1)
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        LevelExpr.lzero.lsucc flag)
      (fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) 0
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        LevelExpr.lzero flag))

/-- **UNCONDITIONAL strong normalization of a closed argument-DISCARDING β-redex.**  The application
`(λ (x : Type@(e+1)). Type@0) (Type@e)` is `IsStronglyNormalizing` — the discarding companion to
`closedIdentityApplication_stronglyNormalizing`: the function's body ignores its argument, so the β-contractum
`subst0 (Type@0) (Type@e)` ERASES the argument and yields `Type@0` (by defeq, the body being closed).  Composes
the `piElim` arm over the constant function (itself the discarding-`piIntro` + `universeFormation` composition)
and the argument `Type@e : Type@(e+1)`, then the closed-SN handoff.  Exercises `fundamentalPiElimLevelIndexed`
on the ERASING β-case end-to-end, hypothesis-free — the complement of the identity application's substituting
β-case. -/
theorem closedConstantApplication_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (appCell (lamCell (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell levelExpr flag) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalPiElimLevelIndexed (context := (TypingContext.empty : TypingContext profile 0))
      emptyLevelVector (0 + 1)
      (functionTerm := lamCell (universeCodeCell LevelExpr.lzero flag))
      (argument := universeCodeCell levelExpr flag)
      (domainCode := universeCodeCell levelExpr.lsucc flag)
      (codomainCode := universeCodeCell LevelExpr.lzero.lsucc flag)
      (fundamentalPiIntroLevelIndexed (context := (TypingContext.empty : TypingContext profile 0))
        emptyLevelVector 0
        (domainCode := universeCodeCell levelExpr.lsucc flag)
        (codomainCode := universeCodeCell LevelExpr.lzero.lsucc flag)
        (body := universeCodeCell LevelExpr.lzero flag)
        (domainLevel := levelExpr.lsucc.lsucc) (codomainLevel := LevelExpr.lzero.lsucc.lsucc) (flag := flag)
        (fundamentalUniverseFormationLevelIndexed emptyLevelVector (0 + 1)
          (TypingContext.empty : TypingContext profile 0) levelExpr.lsucc flag)
        (fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) (0 + 1)
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr.lsucc flag)) LevelExpr.lzero.lsucc flag)
        (fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) 0
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr.lsucc flag)) LevelExpr.lzero flag))
      (fundamentalUniverseFormationLevelIndexed emptyLevelVector 0
        (TypingContext.empty : TypingContext profile 0) levelExpr flag))

/-! ## Nested formers — the FT arms COMPOSE end-to-end

All witnesses above (and the original four) are formers whose CHILDREN are universe codes.  These three
exercise a former whose CHILD is itself a FORMER: the level-indexed Π- and Σ-formation arms compose into
hypothesis-free SN.  The inner former arm supplies the outer arm's codomain premise (at the binder-extended
context), so the closed-SN handoff still discharges to plain `IsStronglyNormalizing` with no recursor and no
hypothesis — demonstrating the arms NEST, not just fire individually. -/

/-- **UNCONDITIONAL strong normalization of a closed Π whose codomain is a Σ-former.**  The type
`Π (Type@0). Σ (Type@0). Type@0` is `IsStronglyNormalizing` — the Π-formation arm's codomain premise (a
`∀ headLevel` family at the binder-extended context) is supplied by the Σ-formation arm rather than a bare
`universeFormation`, so the two formation arms compose end-to-end.  First unconditional SN for a former with a
FORMER child. -/
theorem closedNestedPiOverSigma_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (sigmaTyCodeCell (universeCodeCell LevelExpr.lzero flag)
          (universeCodeCell LevelExpr.lzero flag)) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalPiFormationLevelIndexed emptyLevelVector 0
      (domainLevel := LevelExpr.lzero.lsucc)
      (codomainLevel := LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc)
      (formerLevel := LevelExpr.lmax LevelExpr.lzero.lsucc
        (LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc)) (flag := flag)
      (fun aboveLevel =>
        fundamentalUniverseFormationLevelIndexed emptyLevelVector aboveLevel
          (TypingContext.empty : TypingContext profile 0) LevelExpr.lzero flag)
      (fun headLevel =>
        fundamentalSigmaFormationLevelIndexed (levelCons headLevel emptyLevelVector) 0
          (domainLevel := LevelExpr.lzero.lsucc) (codomainLevel := LevelExpr.lzero.lsucc)
          (formerLevel := LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc) (flag := flag)
          (fun aboveLevel2 =>
            fundamentalUniverseFormationLevelIndexed (levelCons headLevel emptyLevelVector) aboveLevel2
              ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell LevelExpr.lzero flag))
              LevelExpr.lzero flag)
          (fundamentalUniverseFormationLevelIndexed
            (levelCons (0 + 1) (levelCons headLevel emptyLevelVector)) 0
            (((TypingContext.empty : TypingContext profile 0).cons
              (universeCodeCell LevelExpr.lzero flag)).cons (universeCodeCell LevelExpr.lzero flag))
            LevelExpr.lzero flag)))

/-- **UNCONDITIONAL strong normalization of a closed Σ whose codomain is a Π-former.**  The type
`Σ (Type@0). Π (Type@0). Type@0` is `IsStronglyNormalizing` — the dual nesting of
`closedNestedPiOverSigma`: the Σ-formation arm's codomain premise (a single conclusion) is supplied by the
Π-formation arm at the binder-extended context. -/
theorem closedNestedSigmaOverPi_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (sigmaTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
          (universeCodeCell LevelExpr.lzero flag)) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalSigmaFormationLevelIndexed emptyLevelVector 0
      (domainLevel := LevelExpr.lzero.lsucc)
      (codomainLevel := LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc)
      (formerLevel := LevelExpr.lmax LevelExpr.lzero.lsucc
        (LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc)) (flag := flag)
      (fun aboveLevel =>
        fundamentalUniverseFormationLevelIndexed emptyLevelVector aboveLevel
          (TypingContext.empty : TypingContext profile 0) LevelExpr.lzero flag)
      (fundamentalPiFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) 0
        (domainLevel := LevelExpr.lzero.lsucc) (codomainLevel := LevelExpr.lzero.lsucc)
        (formerLevel := LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc) (flag := flag)
        (fun aboveLevel2 =>
          fundamentalUniverseFormationLevelIndexed (levelCons (0 + 1) emptyLevelVector) aboveLevel2
            ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell LevelExpr.lzero flag))
            LevelExpr.lzero flag)
        (fun headLevel2 =>
          fundamentalUniverseFormationLevelIndexed
            (levelCons headLevel2 (levelCons (0 + 1) emptyLevelVector)) 0
            (((TypingContext.empty : TypingContext profile 0).cons
              (universeCodeCell LevelExpr.lzero flag)).cons (universeCodeCell LevelExpr.lzero flag))
            LevelExpr.lzero flag)))

/-- **UNCONDITIONAL strong normalization of a closed binary function type.**  The type
`Π (Type@0). Π (Type@0). Type@0` (a two-argument type former) is `IsStronglyNormalizing` — the Π-formation
arm nested inside its own codomain premise, the deepest of the three nestings: two binder-extended contexts. -/
theorem closedNestedPiOverPi_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
          (universeCodeCell LevelExpr.lzero flag)) : RawTerm 0) :=
  closedSubjectStronglyNormalizingFromLevelIndexed (profile := profile) 0
    (fundamentalPiFormationLevelIndexed emptyLevelVector 0
      (domainLevel := LevelExpr.lzero.lsucc)
      (codomainLevel := LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc)
      (formerLevel := LevelExpr.lmax LevelExpr.lzero.lsucc
        (LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc)) (flag := flag)
      (fun aboveLevel =>
        fundamentalUniverseFormationLevelIndexed emptyLevelVector aboveLevel
          (TypingContext.empty : TypingContext profile 0) LevelExpr.lzero flag)
      (fun headLevel =>
        fundamentalPiFormationLevelIndexed (levelCons headLevel emptyLevelVector) 0
          (domainLevel := LevelExpr.lzero.lsucc) (codomainLevel := LevelExpr.lzero.lsucc)
          (formerLevel := LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc) (flag := flag)
          (fun aboveLevel2 =>
            fundamentalUniverseFormationLevelIndexed (levelCons headLevel emptyLevelVector) aboveLevel2
              ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell LevelExpr.lzero flag))
              LevelExpr.lzero flag)
          (fun headLevel2 =>
            fundamentalUniverseFormationLevelIndexed
              (levelCons headLevel2 (levelCons headLevel emptyLevelVector)) 0
              (((TypingContext.empty : TypingContext profile 0).cons
                (universeCodeCell LevelExpr.lzero flag)).cons (universeCodeCell LevelExpr.lzero flag))
              LevelExpr.lzero flag)))

end FX1Poly.Typed
