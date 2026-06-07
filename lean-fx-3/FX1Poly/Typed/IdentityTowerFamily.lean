import FX1Poly.Typed.TypedLambdaDerivations
import FX1Poly.Typed.TypedNormalizer

/-! # Foundation/PolyCell/Typed/IdentityTowerFamily
    — a uniformly-typed infinite identity-application family (recursive piElim + SN + β-chain to value)

`TypedLambdaDerivations.lean` ships CONCRETE single typed λ-derivations (the identity, the constant
function, one β-redex application).  This file lifts that to an INFINITE PARAMETERIZED FAMILY: the
"identity tower" `idTower e flag n = (λx. x)ⁿ (Type@e)` — `n` nested identity applications, all at the
universe `Type@(e+1)`, on the closed value `Type@e`.  It complements the §27.3 L2 metatheory-fuzz family
`metatheoryFuzzFamily` (the argument-discarding "constant" tower) with an identity tower, and is the first
recursive-typing witness that exercises the grown engine's `piElim` rule at EVERY height.

  * `idTower` — the family: `idTower e flag 0 = Type@e`; `idTower e flag (n+1) = (λx. x) (idTower e flag n)`.
  * `idTower_hasTypeDescPi` — every member types uniformly at `Type@(e+1)`.  Base: universe formation
    (`Type@e : Type@(e+1)`).  Step: `piElim` of the identity `λ(x:Type@(e+1)).x : Π(Type@(e+1)).Type@(e+1)`
    (firing-63 `identityOnUniverse_hasTypeDescPi` at level `e+1`) against the inductive hypothesis (the
    previous tower member, itself typed at `Type@(e+1)`).  The piElim result `subst0 Type@(e+1) (idTower n)`
    is definitionally `Type@(e+1)` (the constant codomain ignores the argument), so the family is uniformly
    typed.  This is RECURSIVE piElim — the rule fires `n` times in the `n`-th derivation.
  * `idTower_stronglyNormalizing` — every member is `IsStronglyNormalizing`, via SN-043
    (`HasTypeDescPi.closedStronglyNormalizing`) uniformly over the infinite family.
  * `idTower_reducesToValue` — every member β-reduces, in exactly `n` identity contractions, to the value
    `Type@e`: each `(λx. x) t ↝ t` (`Step.beta`, since `subst0 (var 0) t = t`) strips one identity, and the
    `StepStar` chain concatenates them.
  * `idTowerUniformlyTypedReducesToValue` — the packaged headline: for every height the tower member is
    well-typed at `Type@(e+1)`, strongly normalizing, and reduces to `Type@e`.  A demonstration that the
    typing engine + SN-043 scale uniformly to an infinite family, not just to finitely many fixtures.

Everything is closed (scope `0`).  Zero-axiom: structural induction on the height composing
`HasTypeDescPi.piElim` / `HasTypeDesc.universeFormation` / `identityOnUniverse_hasTypeDescPi` for typing,
`HasTypeDescPi.closedStronglyNormalizing` for SN, and `Step.beta` / `StepStar.trans` for the reduction
chain.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The identity tower `(λx. x)ⁿ (Type@e)` — `n` nested identity applications on the closed universe code
`Type@e`.  Height `0` is `Type@e`; height `n+1` wraps the previous in one identity application. -/
def idTower (levelExpr : LevelExpr) (flag : UniverseFlag) : Nat → RawTerm 0
  | 0 => universeCodeCell levelExpr flag
  | n + 1 => appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) (idTower levelExpr flag n)

/-- **Every tower member types uniformly at `Type@(e+1)`.**  Base by universe formation
(`Type@e : Type@(e+1)`); step by `piElim` of the identity at `Type@(e+1)` against the inductive
hypothesis — recursive `piElim`, firing `n` times in the `n`-th derivation. -/
theorem idTower_hasTypeDescPi {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∀ towerHeight, HasTypeDescPi profile TypingContext.empty (idTower levelExpr flag towerHeight)
      (universeCodeCell levelExpr.lsucc flag)
  | 0 => HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty levelExpr flag)
  | n + 1 => HasTypeDescPi.piElim
      (identityOnUniverse_hasTypeDescPi (profile := profile) levelExpr.lsucc flag)
      (idTower_hasTypeDescPi levelExpr flag n)

/-- **Every tower member is strongly normalizing.**  Typing fed through SN-043
(`HasTypeDescPi.closedStronglyNormalizing`), uniformly over the infinite family. -/
theorem idTower_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∀ towerHeight, IsStronglyNormalizing (idTower levelExpr flag towerHeight) :=
  fun towerHeight =>
    HasTypeDescPi.closedStronglyNormalizing
      (idTower_hasTypeDescPi (profile := profile) levelExpr flag towerHeight)

/-- **Every tower member β-reduces to the value `Type@e`** in exactly `towerHeight` identity
contractions.  Each `(λx. x) t ↝ t` (`Step.beta`, `subst0 (var 0) t = t`) strips one identity; the
`StepStar` chain concatenates them. -/
theorem idTower_reducesToValue (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∀ towerHeight, StepStar (idTower levelExpr flag towerHeight) (universeCodeCell levelExpr flag)
  | 0 => StepStar.refl _
  | n + 1 => StepStar.trans Step.beta (idTower_reducesToValue levelExpr flag n)

/-- ★ **The identity tower is a uniformly-typed, strongly-normalizing, value-reaching infinite family.**
For every height the tower member types at `Type@(e+1)`, is strongly normalizing, and reduces to `Type@e`
— the typing engine + SN-043 scale uniformly to an infinite family, not just to finitely many fixtures. -/
theorem idTowerUniformlyTypedReducesToValue {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (towerHeight : Nat) :
    HasTypeDescPi profile TypingContext.empty (idTower levelExpr flag towerHeight)
        (universeCodeCell levelExpr.lsucc flag) ∧
    IsStronglyNormalizing (idTower levelExpr flag towerHeight) ∧
    StepStar (idTower levelExpr flag towerHeight) (universeCodeCell levelExpr flag) :=
  ⟨idTower_hasTypeDescPi levelExpr flag towerHeight,
    idTower_stronglyNormalizing (profile := profile) levelExpr flag towerHeight,
    idTower_reducesToValue levelExpr flag towerHeight⟩

/-! ## The family collapses to one canonical value (conversion + normalization)

The whole tower reduces to `Type@e`, so — through the conversion relation and the SN-112 normalizer — the
infinitely many syntactically-distinct members are all definitionally ONE thing.  This connects the family
to firings' `Conv` (`Conv.fromStepStar`) and the computed normalizer (`HasTypeDescPi.normalForm` +
`reachedNormalForm_eq_normalForm`). -/

/-- The universe code `Type@e` is a step-normal form — a nullary leaf with no redex root, structurally
normal regardless of its level/flag payload (`rfl` over the Boolean normality check). -/
theorem universeCodeCell_isStepNormalForm (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.isStepNormalForm (universeCodeCell levelExpr flag : RawTerm 0) :=
  rfl

/-- Every tower member converts to the value `Type@e` — its reduction chain lifts to `Conv`. -/
theorem idTower_convToValue (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∀ towerHeight, Conv (idTower levelExpr flag towerHeight) (universeCodeCell levelExpr flag) :=
  fun towerHeight => Conv.fromStepStar (idTower_reducesToValue levelExpr flag towerHeight)

/-- All tower members are mutually convertible — the whole family is one conversion class, joined through
the common value `Type@e`. -/
theorem idTower_allConvertible (levelExpr : LevelExpr) (flag : UniverseFlag) (heightA heightB : Nat) :
    Conv (idTower levelExpr flag heightA) (idTower levelExpr flag heightB) :=
  Conv.trans (idTower_convToValue levelExpr flag heightA)
    (Conv.sym (idTower_convToValue levelExpr flag heightB))

/-- The SN-112 normalizer maps every tower member to the canonical value `Type@e` — the computed normal
form of each member is exactly `Type@e` (`reachedNormalForm_eq_normalForm` applied to the reduction to the
normal value). -/
theorem idTower_normalForm_eq_value {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag)
    (towerHeight : Nat) :
    (idTower_hasTypeDescPi (profile := profile) levelExpr flag towerHeight).normalForm =
      universeCodeCell levelExpr flag :=
  ((idTower_hasTypeDescPi (profile := profile) levelExpr flag towerHeight).reachedNormalForm_eq_normalForm
    (idTower_reducesToValue levelExpr flag towerHeight)
    (universeCodeCell_isStepNormalForm levelExpr flag)).symm

/-- ★ **The identity tower collapses to one canonical value.**  All members are mutually convertible and the
normalizer maps each to `Type@e` — infinitely many syntactically-distinct well-typed terms, all
definitionally equal, all normalizing to the single canonical value.  The conversion/normalization face of
the uniformly-typed family. -/
theorem idTowerCollapsesToCanonicalValue {profile : PolyProfile} (levelExpr : LevelExpr)
    (flag : UniverseFlag) (heightA heightB : Nat) :
    Conv (idTower levelExpr flag heightA) (idTower levelExpr flag heightB) ∧
    (idTower_hasTypeDescPi (profile := profile) levelExpr flag heightA).normalForm =
      universeCodeCell levelExpr flag ∧
    (idTower_hasTypeDescPi (profile := profile) levelExpr flag heightB).normalForm =
      universeCodeCell levelExpr flag :=
  ⟨idTower_allConvertible levelExpr flag heightA heightB,
    idTower_normalForm_eq_value levelExpr flag heightA,
    idTower_normalForm_eq_value levelExpr flag heightB⟩

end FX1Poly.Typed
