import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Typed.Cell.CellSubstitution
import FX1Poly.Axis.Term.Subst.RawTermSubstPair
import FX1Poly.Axis.Term.Subst.RawTermSubstLiftWeaken
import FX1Poly.Axis.Term.Rename.RawTermRenameAsSubst
import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename
import FX1Poly.Core.Rewriting.Conversion.ConvCongruence

/-! # FX1Poly/Typed/Cell/IdJDependentMotiveType
    — the dependent `idJ` motive-instantiation + path-binder context (JMAX-0, the genuine Paulin-Mohring substrate)

Genuine path induction (`idJ`, Paulin-Mohring) needs the two-binder motive `C : (b : A) -> Id A left b -> U`
instantiated at two points: the OUTPUT type `C[b := right, p := witness]` and the BASE-case type
`C[b := left, p := refl left]`.  `idJMotiveAt motive point path` is that instantiation — fill the inner path
binder (`var 0`) with `path` and the outer endpoint binder (`var 1`) with `point`.

This is EXACTLY the shipped two-variable parallel substitution `RawTerm.substPair` (`RawTermSubstPair.lean`,
the natElim/natRec succ-iota toolkit): `substPair body innerArg outerArg` fills `var 0 := innerArg`, `var 1 :=
outerArg`.  So `idJMotiveAt motive point path := substPair motive path point` (innerArg = `path` for the inner
path binder, outerArg = `point` for the outer endpoint binder), and its subst/rename push-through naturality is
the already-proven `RawTerm.substPair_subst_commute` / `RawTerm.substPair_rename_commute` — no new substrate
proof.  The genuine rule (JMAX-3), the SR-crux Conv lemma (JMAX-2), and the bridge/row are stated over these.

`idJMotiveSecondBinderType typeCode left` is the type of the motive's SECOND binder `p : Id A left b`, living
in the context already extended by `b : A` (so `typeCode`/`left` are weakened past the fresh `b`, and `b` is
`var 0`).  `idJElimRule`'s motive obligation (JMAX-3) classifies the motive at a universe over
`(context.cons typeCode).cons (idJMotiveSecondBinderType typeCode left)`.

## Zero-axiom
Definitions over the shipped `RawTerm.substPair` + the identity cell former `idTypeCell`; the naturality lemmas
delegate to the proven `substPair` commute laws.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Axis.Syntax

/-- The dependent `idJ` motive instantiated at endpoint `point` (the outer `b` binder, `var 1`) and path
`path` (the inner `p` binder, `var 0`): `idJMotiveAt motive point path := substPair motive path point`.  The
OUTPUT type of genuine `idJ` is `idJMotiveAt motive right witness`; the BASE-case type is
`idJMotiveAt motive left (reflCell left)`. -/
def idJMotiveAt {scope : Nat} (motive : RawTerm (scope + 2)) (point path : RawTerm scope) : RawTerm scope :=
  RawTerm.substPair motive path point

/-- The type of the motive's second binder `p : Id A left b` in the `b`-extended context: the identity code
with `typeCode`/`left` weakened past the fresh `b` (`var 0`).  `idJElimRule`'s motive obligation classifies
the motive at a universe over `(context.cons typeCode).cons (idJMotiveSecondBinderType typeCode left)`. -/
def idJMotiveSecondBinderType {scope : Nat} (typeCode left : RawTerm scope) : RawTerm (scope + 1) :=
  idTypeCell (RawTerm.weaken typeCode) (RawTerm.weaken left)
    (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)

/-- `RawTerm.subst` distributes over the identity cell DEFINITIONALLY (the `gen_idCode` cell is a `mkGen` with
three 0-shift children, and `subst` is the children-mapping fold).  Local `rfl` copy so this Cell-layer file
need not import `UnionCellSubstitution` (which sits ABOVE the engine — importing it would cycle through
`ElimRuleTable`); the canonical `subst_idTypeCell` lives there. -/
private theorem subst_idTypeCell_distrib {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (typeCode left right : RawTerm sourceScope) :
    RawTerm.subst substitution (idTypeCell typeCode left right)
      = idTypeCell (RawTerm.subst substitution typeCode) (RawTerm.subst substitution left)
          (RawTerm.subst substitution right) := rfl

/-- `RawTerm.rename` distributes over the identity cell DEFINITIONALLY (the rename twin of
`subst_idTypeCell_distrib`). -/
private theorem rename_idTypeCell_distrib {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) (typeCode left right : RawTerm sourceScope) :
    RawTerm.rename someRenaming (idTypeCell typeCode left right)
      = idTypeCell (RawTerm.rename someRenaming typeCode) (RawTerm.rename someRenaming left)
          (RawTerm.rename someRenaming right) := rfl

/-- **Substitution naturality of `idJMotiveSecondBinderType` under a lifted substitution** — the form the union
substitution-stability arm consumes to reshape the genuine `idJ` motive obligation's `b`-extended context binding.
The two weakened carriers commute with the lift via `RawTerm.subst_lift_weaken`; the fresh `var 0` is fixed by the
lift, so the whole equation is the `idTypeCell` distribution plus two weaken-commutes. -/
theorem subst_lift_idJMotiveSecondBinderType {scope targetScope : Nat}
    (typeCode left : RawTerm scope) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.lift substitution) (idJMotiveSecondBinderType typeCode left)
      = idJMotiveSecondBinderType (RawTerm.subst substitution typeCode)
          (RawTerm.subst substitution left) := by
  unfold idJMotiveSecondBinderType
  rw [subst_idTypeCell_distrib, RawTerm.subst_lift_weaken, RawTerm.subst_lift_weaken]
  -- the fresh `var 0` is fixed by the lift (`lift σ` sends index 0 to the newest var); definitional
  rfl

/-- **Renaming naturality of `idJMotiveSecondBinderType` under a lifted renaming** — the rename twin (the form the
union renaming-stability arm consumes).  Delegates to `RawTerm.rename_lift_weaken` for the two weakened carriers;
the fresh `var 0` is fixed by the lift. -/
theorem rename_lift_idJMotiveSecondBinderType {scope targetScope : Nat}
    (typeCode left : RawTerm scope) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (RawRenaming.lift someRenaming) (idJMotiveSecondBinderType typeCode left)
      = idJMotiveSecondBinderType (RawTerm.rename someRenaming typeCode)
          (RawTerm.rename someRenaming left) := by
  unfold idJMotiveSecondBinderType
  rw [rename_idTypeCell_distrib, RawTerm.rename_lift_weaken, RawTerm.rename_lift_weaken]
  -- the fresh `var 0` is fixed by the lift; definitional
  rfl

/-- **`iterateLiftRaw … 1` form** of `subst_lift_idJMotiveSecondBinderType` — the shape the union
substitution-stability arm's `SubstHostTyped.consTwice` presents the motive obligation's inner binding in
(`subst (iterateLiftRaw substitution 1) innerType`).  Definitionally identical to the `lift` form
(`iterateLiftRaw σ 1 ≡ lift σ`), so it closes by the underlying lemma directly. -/
theorem subst_iterateLift_idJMotiveSecondBinderType {scope targetScope : Nat}
    (typeCode left : RawTerm scope) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (iterateLiftRaw substitution 1) (idJMotiveSecondBinderType typeCode left)
      = idJMotiveSecondBinderType (RawTerm.subst substitution typeCode)
          (RawTerm.subst substitution left) :=
  subst_lift_idJMotiveSecondBinderType typeCode left substitution

/-- **`iterateLiftRaw … 1` form** of `rename_lift_idJMotiveSecondBinderType` — the shape the union
renaming-stability arm's two-binder host condition presents the motive obligation's inner binding in. -/
theorem rename_iterateLift_idJMotiveSecondBinderType {scope targetScope : Nat}
    (typeCode left : RawTerm scope) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (iterateLiftRaw someRenaming 1) (idJMotiveSecondBinderType typeCode left)
      = idJMotiveSecondBinderType (RawTerm.rename someRenaming typeCode)
          (RawTerm.rename someRenaming left) :=
  rename_lift_idJMotiveSecondBinderType typeCode left someRenaming

/-- **Substitution naturality of `idJMotiveAt`** (the `iterateLiftRaw` form the union substitution-stability
arm consumes): an outer substitution substitutes the two filled points and crosses the motive's two binders
via `iterateLiftRaw substitution 2` (defeq `lift (lift substitution)`).  Delegates to the proven
`RawTerm.substPair_subst_commute`. -/
theorem subst_idJMotiveAt_iterateLift {scope targetScope : Nat} (motive : RawTerm (scope + 2))
    (point path : RawTerm scope) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst substitution (idJMotiveAt motive point path)
      = idJMotiveAt (RawTerm.subst (iterateLiftRaw substitution 2) motive)
          (RawTerm.subst substitution point) (RawTerm.subst substitution path) := by
  unfold idJMotiveAt
  exact RawTerm.substPair_subst_commute motive path point substitution

/-- **Renaming naturality of `idJMotiveAt`** — the rename twin (the form the union renaming-stability arm
consumes).  Delegates to the proven `RawTerm.substPair_rename_commute`; `iterateLiftRaw someRenaming 2` is
defeq `RawRenaming.lift (RawRenaming.lift someRenaming)`. -/
theorem rename_idJMotiveAt_iterateLift {scope targetScope : Nat} (motive : RawTerm (scope + 2))
    (point path : RawTerm scope) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename someRenaming (idJMotiveAt motive point path)
      = idJMotiveAt (RawTerm.rename (iterateLiftRaw someRenaming 2) motive)
          (RawTerm.rename someRenaming point) (RawTerm.rename someRenaming path) := by
  unfold idJMotiveAt
  exact RawTerm.substPair_rename_commute someRenaming motive path point

/-- Pointwise `StepStar` between two two-variable `pair` substitutions, from chains on each substituent — the
two-binder analogue of `RawTermSubst.singleton_pointwise_stepStar`. -/
theorem pairPointwiseStepStar {scope : Nat}
    {innerLeft innerRight outerLeft outerRight : RawTerm scope}
    (innerChain : StepStar innerLeft innerRight) (outerChain : StepStar outerLeft outerRight) :
    RawTermSubst.PointwiseStepStar
      (RawTermSubst.pair innerLeft outerLeft) (RawTermSubst.pair innerRight outerRight) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact innerChain
  | ⟨1, _⟩ => exact outerChain
  | ⟨_ + 2, _⟩ => exact StepStar.refl _

/-- **`Conv` congruence in the two substituents of `substPair`** (body fixed): the two-binder analogue of
`Conv.subst0`.  Both legs reduce the two substituents to their joins via `pairPointwiseStepStar` +
`RawTerm.subst_pointwise_stepStar`, landing at the common `substPair body innerCommon outerCommon`. -/
theorem convSubstPairArgs {scope : Nat} (body : RawTerm (scope + 2))
    {innerLeft innerRight outerLeft outerRight : RawTerm scope}
    (innerConv : Conv innerLeft innerRight) (outerConv : Conv outerLeft outerRight) :
    Conv (RawTerm.substPair body innerLeft outerLeft) (RawTerm.substPair body innerRight outerRight) := by
  obtain ⟨innerCommon, innerLeftChain, innerRightChain⟩ := innerConv
  obtain ⟨outerCommon, outerLeftChain, outerRightChain⟩ := outerConv
  exact ⟨RawTerm.substPair body innerCommon outerCommon,
    RawTerm.subst_pointwise_stepStar (pairPointwiseStepStar innerLeftChain outerLeftChain) body,
    RawTerm.subst_pointwise_stepStar (pairPointwiseStepStar innerRightChain outerRightChain) body⟩

/-- **★ JMAX-2: the idJ-refl motive-instantiation Conv crux.**  The genuine `idJ` base case inhabits
`idJMotiveAt motive left (reflCell left)`; the redex output is `idJMotiveAt motive right (reflCell w)` (witness
`refl w`).  When the iota fires, the based identity content of `witness : Id A left right` supplies `Conv left w`
(hence `Conv (reflCell left) (reflCell w)` by `Conv.gen_refl_cong`) and `Conv left right`, whence the two motive
instantiations are `Conv`.  This is the subject-reduction reclassification the genuine `idJ` iota (JMAX-3)
consumes — `base` re-types at the redex's output up to `Conv`. -/
theorem idJReflMotiveConv {scope : Nat} (motive : RawTerm (scope + 2)) {left right w : RawTerm scope}
    (convLeftRight : Conv left right) (convLeftW : Conv left w) :
    Conv (idJMotiveAt motive left (reflCell left)) (idJMotiveAt motive right (reflCell w)) := by
  unfold idJMotiveAt
  exact convSubstPairArgs motive (Conv.gen_refl_cong convLeftW) convLeftRight

/-- **Singleton-substitution collapse of the motive's second-binder type.**  Filling the fresh `b`-binder
(`var 0`) with the outer endpoint `rightEndpoint` in `idJMotiveSecondBinderType typeCode left` cancels both
weakenings (`subst_singleton_renameWeaken_cancel`) and lands the fresh variable on `rightEndpoint`, giving the
based identity code `idTypeCell typeCode left rightEndpoint` — exactly the classifier the genuine `idJ` witness
inhabits.  The crux of the idJ output-formedness validity brick: the motive's inner-binder typing premise feeds
the two-binder transport `substPairUnderTwoBindingsUnionImages` at the right instantiated type. -/
theorem subst_singleton_idJMotiveSecondBinderType {scope : Nat}
    (typeCode left rightEndpoint : RawTerm scope) :
    RawTerm.subst (RawTermSubst.singleton rightEndpoint)
        (idJMotiveSecondBinderType typeCode left)
      = idTypeCell typeCode left rightEndpoint := by
  unfold idJMotiveSecondBinderType
  rw [subst_idTypeCell_distrib, RawTerm.weaken_eq_rename typeCode, RawTerm.weaken_eq_rename left,
    subst_singleton_renameWeaken_cancel, subst_singleton_renameWeaken_cancel]
  rfl

end FX1Poly.Typed
