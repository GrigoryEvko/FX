import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Tier0.Term.Subst.RawTermSubstPair
import FX1Poly.Tier0.Term.Rename.RawTermRenameAsSubst

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

open FX1Poly.Core FX1Poly.Tier0.Syntax

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

end FX1Poly.Typed
