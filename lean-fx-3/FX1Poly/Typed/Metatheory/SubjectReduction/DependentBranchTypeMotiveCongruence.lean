import FX1Poly.Typed.Cell.NatElimDependentSuccType
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.ListElimDependentConsType
import FX1Poly.Typed.Metatheory.Universe.ConvCodeInjectivity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/DependentBranchTypeMotiveCongruence
    — the dependent-branch-type `Conv`-stability under a motive step (gate-2 motive-step substrate, #1740)

The motive-step arm of the eliminator-congruence subject reduction (gate 2 of the consistency leg #1697)
re-types a dependent eliminator cell when its MOTIVE child steps.  Unlike `boolElim`'s NULLARY branches (whose
classifiers `subst0 motive boolTrue/False` drift via the already-shipped `subst0_isConvStableUnderBodyStep`),
the recursive / coproduct / option / list eliminators carry NON-nullary dependent branch classifiers — Π types
(`(a : A) -> motive (ctor a)`) or a two-binder re-basing (`natElim` / `natRec`'s succ branch).  When the motive
steps, those branch types DRIFT, and the rebuilt cell's `elim` arm must reclassify each branch against the
drifted classifier; the `Conv`-stability of the drift is exactly this file.

Every one of these branch types embeds the motive purely by SUBSTITUTION (`RawTerm.subst σ motive` for a
branch-specific `σ`), optionally wrapped in `piTyCodeCell` formers whose other components do not mention the
motive.  So `Step motive motiveReduct` lifts to a branch-type `Conv` uniformly:

  * the substituted-motive leaf converts by `Conv.subst _ (Conv.fromStep motiveStep)` (the polynomial-monad
    substitution congruence applied to the single motive step), and
  * the `piTyCodeCell` wrappers lift componentwise by `Conv.piTyCode_cong` with `Conv.refl` on the
    motive-free domains.

`listElim`'s cons branch is a THREE-Π nest with the motive in BOTH the recursive-result binder type and the
codomain, so its lift is a nested `Conv.piTyCode_cong` over two converging leaves.  The `idJ` motive / base-case
drift is already covered by `idJOutputType_isConvStableUnderMotiveStep` (the `substPair` body leg), so it is not
re-derived here.

## Zero-axiom verification

`Conv.subst` / `Conv.fromStep` / `Conv.refl` / `Conv.piTyCode_cong` — all SN-free term-level `Conv`
congruences, no typing.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The `natElim` / `natRec` succ-branch type is `Conv`-stable when the motive steps.**  The succ-branch
type is the motive re-based at `natSucc (var 1)` (`RawTerm.subst σ motive`), so a motive step lifts directly by
the substitution congruence.  Shared by both recursors (the branch TYPE is identical). -/
theorem natElimDependentSuccBranchType_isConvStableUnderMotiveStep {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)} (motiveStep : Step motive motiveReduct) :
    Conv (natElimDependentSuccBranchType motive) (natElimDependentSuccBranchType motiveReduct) := by
  unfold natElimDependentSuccBranchType
  exact Conv.subst _ (Conv.fromStep motiveStep)

/-- **The `optionMatch` some-branch type is `Conv`-stable when the motive steps.**  The some-branch type is
`(a : A) -> motive (some a) = piTyCodeCell A (subst σ motive)`; the domain `A` is motive-free, the codomain is a
substituted motive, so the lift is `piTyCode_cong (refl A) (subst-congruence)`. -/
theorem optionMatchDependentSomeBranchType_isConvStableUnderMotiveStep {scope : Nat}
    (elementType : RawTerm scope) {motive motiveReduct : RawTerm (scope + 1)}
    (motiveStep : Step motive motiveReduct) :
    Conv (optionMatchDependentSomeBranchType motive elementType)
         (optionMatchDependentSomeBranchType motiveReduct elementType) := by
  unfold optionMatchDependentSomeBranchType
  refine Conv.piTyCode_cong (Conv.refl _) ?_
  unfold optionMatchDependentSomeBranchCodomain
  exact Conv.subst _ (Conv.fromStep motiveStep)

/-- **The `eitherMatch` inl-branch type is `Conv`-stable when the motive steps.**  `(a : A) -> motive (inl a)`
— the `optionMatch` some-branch twin at the left injection. -/
theorem eitherMatchDependentInlBranchType_isConvStableUnderMotiveStep {scope : Nat}
    (leftType : RawTerm scope) {motive motiveReduct : RawTerm (scope + 1)}
    (motiveStep : Step motive motiveReduct) :
    Conv (eitherMatchDependentInlBranchType motive leftType)
         (eitherMatchDependentInlBranchType motiveReduct leftType) := by
  unfold eitherMatchDependentInlBranchType
  refine Conv.piTyCode_cong (Conv.refl _) ?_
  unfold eitherMatchDependentInlBranchCodomain
  exact Conv.subst _ (Conv.fromStep motiveStep)

/-- **The `eitherMatch` inr-branch type is `Conv`-stable when the motive steps.**  `(b : B) -> motive (inr b)`
— the right-injection twin. -/
theorem eitherMatchDependentInrBranchType_isConvStableUnderMotiveStep {scope : Nat}
    (rightType : RawTerm scope) {motive motiveReduct : RawTerm (scope + 1)}
    (motiveStep : Step motive motiveReduct) :
    Conv (eitherMatchDependentInrBranchType motive rightType)
         (eitherMatchDependentInrBranchType motiveReduct rightType) := by
  unfold eitherMatchDependentInrBranchType
  refine Conv.piTyCode_cong (Conv.refl _) ?_
  unfold eitherMatchDependentInrBranchCodomain
  exact Conv.subst _ (Conv.fromStep motiveStep)

/-- **The `listElim` cons-branch type is `Conv`-stable when the motive steps.**  The cons branch is the
three-Π curry `(head : A) -> (tail : list A) -> (rec : motive tail) -> motive (cons head tail)`, with the motive
in BOTH the recursive-result binder type `motive tail` and the codomain `motive (cons head tail)` — so the lift
is a nested `piTyCode_cong` over the two motive-free outer domains and the two converging substituted-motive
leaves. -/
theorem listElimDependentConsBranchType_isConvStableUnderMotiveStep {scope : Nat}
    (elementType : RawTerm scope) {motive motiveReduct : RawTerm (scope + 1)}
    (motiveStep : Step motive motiveReduct) :
    Conv (listElimDependentConsBranchType motive elementType)
         (listElimDependentConsBranchType motiveReduct elementType) := by
  unfold listElimDependentConsBranchType
  refine Conv.piTyCode_cong (Conv.refl _)
    (Conv.piTyCode_cong (Conv.refl _) (Conv.piTyCode_cong ?_ ?_))
  · unfold listElimDependentRecBinderType
    exact Conv.subst _ (Conv.fromStep motiveStep)
  · unfold listElimDependentConsBranchCodomain
    exact Conv.subst _ (Conv.fromStep motiveStep)

end FX1Poly.Typed
