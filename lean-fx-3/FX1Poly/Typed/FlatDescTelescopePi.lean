import FX1Poly.Typed.FlatDescTelescope
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution

/-! # FX1Poly/Typed/FlatDescTelescopePi — the GROWN flat formation premise telescope

`FlatDescTelescope` types every flat-former child with the FORMATION engine (`HasTypeDesc`).  That premise
is correct for the retired standalone flat engine, but it is NOT substitution-stable at the union: the
union's substitution lemma carries GROWN (`HasTypeDescPi`) substituent images, and a formation-typed flat
child whose head is a variable can be substituted by a term (e.g. a beta-redex at a universe code) that has
grown typing but NO formation typing — so the substituted children cannot rebuild a `FlatDescTelescope`,
and a union flat arm stated over the formation telescope makes the union's grown-image substitution lemma
FALSE.  The one-judgment repair is to state the union's flat-formation premise at the strongest prior
judgment: this file builds `FlatDescTelescopePi`, the same flat spine with every child typed by the GROWN
engine at its universe code.

  * `FlatDescTelescopePi` — the inductive: same `[0, 0, ...]` flat shape, `cons` premise
    `HasTypeDescPi profile context head (universeCodeCell headLevel flag)`.
  * `FlatDescTelescope.toPi` — every formation flat telescope embeds (per-child
    `HasTypeDescPi.ofFormation`), so every subject the retired flat engine typed is still typed by the
    union's grown-premised arm.
  * `FlatDescTelescopePi.renameRespectingTelescope` / `substRespectingTelescope` — the structural
    metatheory, per-child via the grown engine's own `renameRespectingContext` /
    `substRespectingContext`; the substitution version takes GROWN images, exactly the union's
    substitution side condition.
  * `FlatDescTelescopePi.twoChildComponents` — the `[0, 0]` projection, grown twin of the formation one.

## Zero-axiom

Structural `match`-recursion over the standalone (non-mutual) inductive, per-child reuse of the shipped
grown rename/subst lemmas, `rwa` over the closed-cell commutation equations.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedTypingEngines.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The GROWN flat formation premise telescope: every child is typed at its own universe code by the
grown engine (`HasTypeDescPi`) under the SAME base `context` — the substitution-stable twin of
`FlatDescTelescope` and the premise of the union's `flatFormation` arm. -/
inductive FlatDescTelescopePi (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    {binderShifts : List Nat} → List LevelExpr → RawTermChildren binderShifts scope → Prop where
  | nil : FlatDescTelescopePi profile context flag [] .childNil
  | cons {restShifts : List Nat} (head : RawTerm (scope + 0)) (headLevel : LevelExpr)
      (restLevels : List LevelExpr) (rest : RawTermChildren restShifts scope)
      (headTyped : HasTypeDescPi profile context head (universeCodeCell headLevel flag))
      (restTyped : FlatDescTelescopePi profile context flag restLevels rest) :
      FlatDescTelescopePi profile context flag (headLevel :: restLevels) (.childCons head rest)

/-- **Every formation flat telescope is a grown flat telescope** — per-child
`HasTypeDescPi.ofFormation`.  This is the embedding that keeps every subject the retired standalone flat
engine typed inside the union's grown-premised `flatFormation` arm. -/
theorem FlatDescTelescope.toPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    FlatDescTelescopePi profile context flag levels children :=
  match telescope with
  | .nil => FlatDescTelescopePi.nil
  | .cons head headLevel restLevels rest headTyped restTyped =>
      FlatDescTelescopePi.cons head headLevel restLevels rest
        (HasTypeDescPi.ofFormation headTyped)
        (FlatDescTelescope.toPi restTyped)

/-- **Grown flat telescope renaming.**  Re-types the flat premise spine along a context-respecting
renaming, per-child via the grown engine's `renameRespectingContext`; the flat `cons` keeps every sibling
at the SAME base context, so the renaming stays at the base `rawRenaming`. -/
theorem FlatDescTelescopePi.renameRespectingTelescope {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescopePi profile context flag levels children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : FX1Poly.Foundation.RawRenaming scope targetScope),
      (∀ index : Fin scope,
        RawTerm.rename rawRenaming (context.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      FlatDescTelescopePi profile targetContext flag levels
        (RawTermChildren.rename rawRenaming children) :=
  match telescope with
  | .nil => fun targetContext _rawRenaming _contextCondition => FlatDescTelescopePi.nil
  | .cons head headLevel restLevels rest headTyped restTyped =>
      fun targetContext rawRenaming contextCondition => by
        have renamedHeadTyped :
            HasTypeDescPi profile targetContext
              (RawTerm.rename rawRenaming head)
              (universeCodeCell headLevel flag) := by
          have headRenamed :=
            HasTypeDescPi.renameRespectingContext headTyped targetContext rawRenaming
              contextCondition
          rwa [rename_universeCodeCell] at headRenamed
        exact FlatDescTelescopePi.cons (RawTerm.rename rawRenaming head) headLevel restLevels
          (RawTermChildren.rename rawRenaming rest) renamedHeadTyped
          (FlatDescTelescopePi.renameRespectingTelescope restTyped targetContext rawRenaming
            contextCondition)

/-- **Grown flat telescope substitution.**  Re-types the flat premise spine along a substitution whose
substituents are GROWN-typed at the substituted lookup types — exactly the union substitution lemma's
side condition, which is what makes the union's `flatFormation` arm substitution-stable. -/
theorem FlatDescTelescopePi.substRespectingTelescope {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescopePi profile context flag levels children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : FX1Poly.Core.RawTermSubst scope targetScope),
      (∀ index : Fin scope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (context.lookup index))) →
      FlatDescTelescopePi profile targetContext flag levels
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil => fun targetContext _substitution _substitutionTyped => FlatDescTelescopePi.nil
  | .cons head headLevel restLevels rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeDescPi profile targetContext
              (RawTerm.subst substitution head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            HasTypeDescPi.substRespectingContext headTyped targetContext substitution
              substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        exact FlatDescTelescopePi.cons (RawTerm.subst substitution head) headLevel restLevels
          (RawTermChildren.subst substitution rest) substHeadTyped
          (FlatDescTelescopePi.substRespectingTelescope restTyped targetContext substitution
            substitutionTyped)

/-- **Two-child projection (grown).**  A grown flat telescope over the two-child `[0, 0]` spine yields
both children grown-typed at their universe codes under the SAME base context. -/
theorem FlatDescTelescopePi.twoChildComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {levels : List LevelExpr}
    {children : RawTermChildren [0, 0] scope}
    (telescope : FlatDescTelescopePi profile context flag levels children) :
    ∃ (firstChild secondChild : RawTerm scope) (firstLevel secondLevel : LevelExpr),
      levels = [firstLevel, secondLevel] ∧
      HasTypeDescPi profile context firstChild (universeCodeCell firstLevel flag) ∧
      HasTypeDescPi profile context secondChild (universeCodeCell secondLevel flag) := by
  cases telescope with
  | cons firstChild firstLevel _restLevels _rest firstTyped restTelescope =>
      cases restTelescope with
      | cons secondChild secondLevel _restLevels2 _rest2 secondTyped tailTelescope =>
          cases tailTelescope with
          | nil =>
              exact ⟨firstChild, secondChild, firstLevel, secondLevel, rfl, firstTyped, secondTyped⟩

end FX1Poly.Typed
