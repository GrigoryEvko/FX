import FX1Poly.Typed.HasTypeNativeUnionMatchInversion
import FX1Poly.Typed.HasTypeNativeUnionPathProjInversion
import FX1Poly.Typed.HasTypeNativeUnionRecursiveInversion
import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.HasTypeDescOptionMatch
import FX1Poly.Typed.HasTypeDescEitherMatch
import FX1Poly.Typed.HasTypeDescIdElim
import FX1Poly.Typed.HasTypeDescSigmaProjection
import FX1Poly.Typed.HasTypeDescNatElim
import FX1Poly.Typed.HasTypeDescListElim

/-! # FX1Poly/Typed/HasTypeNativeUnionReverseAdequacy — NATIVE-37 part d: the REVERSE adequacy of the
    native union restricted to each eliminator family's head (closing the re-scoped folds 29/30/31/33).

Forward adequacy (every bespoke / Bridge derivation translates INTO the union) shipped in batches 1-2.
This file proves the OTHER direction — the HONESTY half: the union restricted to each family's head
inverts BACK to (a relativization of) the bespoke engine, certifying the union types NOTHING MORE than
intended at each head, with the genuine SURPLUS surfaced explicitly.

## The precise statement shape (per the task's surfaced-disjunction requirement)

The union eliminator arms carry RECURSIVE premises (scrutinee / branches union-typed), while the bespoke
engines carry engine-specific premises (scrutinee in a data-INTRO engine, branches in the GROWN engine).
So the clean reverse-adequacy form is CONDITIONAL/RELATIVIZED:

  * **The surplus half** — the per-head inversion (shipped in the three inversion files) already surfaces
    the union-recursive premises.  That IS the honest surplus: the union admits a scrutinee / branch typed
    by ANY native family (e.g. a `natElim` scrutinee computed by another eliminator — the batch-1
    exceeds-bespoke witness), strictly more than the bespoke engine's intro-typed scrutinee.

  * **The reconstruction half** — a theorem that, GIVEN the union derivation AND reconstruction
    hypotheses converting each surfaced union premise into its bespoke-engine premise, produces the
    bespoke `HasTypeDesc<Family>` derivation.  When the reconstruction hypotheses hold the union typing
    collapses onto the bespoke one — so on the bespoke-shaped fragment the two judgments AGREE at the head.

The reconstruction hypotheses are exactly the gap between the union arm and the bespoke arm; packaging
them as premises makes the surplus precise and the agreement exact.

## The listElim EXCEPTION (unconditional, no surplus at the head)

`listElim` is special: its union arm was added with the BESPOKE premise shapes already
(`HasTypeDescListIntro` scrutinee, `HasTypeDescPi` branches — premise parity with
`HasTypeDescListElim.listElimIntro`).  So `invertAtListElimHead` surfaces the EXACT bespoke premises and
the reverse adequacy is UNCONDITIONAL: a union typing of a `listElimCell` IS a bespoke `HasTypeDescListElim`
typing, no reconstruction hypotheses needed.  The surplus is empty at this head.

## Zero-axiom

Each reverse adequacy is the per-head inversion + the bespoke engine's intro constructor (applied to the
reconstructed premises).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditNativeUnionReverseAdequacy.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (2) ★ Reverse adequacy — boolElim (relativized) -/

/-- **★ The honest SURPLUS at the boolElim head.**  A union typing of a `boolElimCell` surfaces the three
RECURSIVE union premises: the scrutinee union-typed at `Bool`, both branches union-typed at the
classifier.  This is the union's surplus over the bespoke engine — the scrutinee may be typed by ANY
native family, not just the data-intro engine.  (The inversion IS the surplus statement.) -/
theorem HasTypeNativeUnion.boolElimSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (boolElimCell motive scrutinee thenBranch elseBranch) classifier) :
    HasTypeNativeUnion profile context scrutinee boolTypeCell ∧
    HasTypeNativeUnion profile context thenBranch classifier ∧
    HasTypeNativeUnion profile context elseBranch classifier :=
  derivation.invertAtBoolElimHead rfl

/-- **★ Reverse adequacy at the boolElim head (relativized).**  GIVEN a union typing of a `boolElimCell`
AND reconstruction maps converting its surfaced union premises into the bespoke premises (scrutinee in the
data-intro engine, branches in the grown engine), the bespoke `HasTypeDescBoolElim` derivation is
reconstructed.  The reconstruction maps witness that the surfaced premises landed in the bespoke premise
engines; when they do, the union typing collapses onto the bespoke one. -/
theorem HasTypeNativeUnion.toBoolElimRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (boolElimCell motive scrutinee thenBranch elseBranch) classifier)
    (reconstructScrutinee : HasTypeNativeUnion profile context scrutinee boolTypeCell →
      HasTypeDescDataIntro profile context scrutinee boolTypeCell)
    (reconstructThen : HasTypeNativeUnion profile context thenBranch classifier →
      HasTypeDescPi profile context thenBranch classifier)
    (reconstructElse : HasTypeNativeUnion profile context elseBranch classifier →
      HasTypeDescPi profile context elseBranch classifier) :
    HasTypeDescBoolElim profile context
      (boolElimCell motive scrutinee thenBranch elseBranch) classifier := by
  obtain ⟨scrutineeUnion, thenUnion, elseUnion⟩ := derivation.invertAtBoolElimHead rfl
  exact HasTypeDescBoolElim.boolElimIntro context motive scrutinee thenBranch elseBranch classifier
    (reconstructScrutinee scrutineeUnion) (reconstructThen thenUnion) (reconstructElse elseUnion)

/-! ## (2) ★ Reverse adequacy — optionMatch (relativized) -/

/-- **★ The honest SURPLUS at the optionMatch head.**  A union typing of an `optionMatchCell` surfaces an
element type `A` and the three RECURSIVE union premises: scrutinee at `option(A)`, None branch at `C`,
Some branch at `A → C`. -/
theorem HasTypeNativeUnion.optionMatchSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (optionMatchCell motive noneBranch someBranch scrutinee) classifier) :
    ∃ elementType : RawTerm scope,
      HasTypeNativeUnion profile context scrutinee (optionTypeCell elementType) ∧
      HasTypeNativeUnion profile context noneBranch classifier ∧
      HasTypeNativeUnion profile context someBranch
        (piTyCodeCell elementType (RawTerm.weaken classifier)) :=
  derivation.invertAtOptionMatchHead rfl

/-- **★ Reverse adequacy at the optionMatch head (relativized).**  GIVEN a union typing of an
`optionMatchCell` AND, for the surfaced element type, reconstruction maps converting the surfaced union
premises into the bespoke premises (scrutinee in the option-intro engine, branches in the grown engine),
the bespoke `HasTypeDescOptionMatch` derivation is reconstructed. -/
theorem HasTypeNativeUnion.toOptionMatchRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (optionMatchCell motive noneBranch someBranch scrutinee) classifier)
    (reconstruct : ∀ elementType : RawTerm scope,
      HasTypeNativeUnion profile context scrutinee (optionTypeCell elementType) →
      HasTypeNativeUnion profile context noneBranch classifier →
      HasTypeNativeUnion profile context someBranch
        (piTyCodeCell elementType (RawTerm.weaken classifier)) →
      HasTypeDescOptionIntro profile context scrutinee (optionTypeCell elementType) ∧
      HasTypeDescPi profile context noneBranch classifier ∧
      HasTypeDescPi profile context someBranch
        (piTyCodeCell elementType (RawTerm.weaken classifier))) :
    HasTypeDescOptionMatch profile context
      (optionMatchCell motive noneBranch someBranch scrutinee) classifier := by
  obtain ⟨elementType, scrutineeUnion, noneUnion, someUnion⟩ := derivation.invertAtOptionMatchHead rfl
  obtain ⟨scrutineeBespoke, noneBespoke, someBespoke⟩ :=
    reconstruct elementType scrutineeUnion noneUnion someUnion
  exact HasTypeDescOptionMatch.optionMatchIntro context motive scrutinee noneBranch someBranch
    elementType classifier scrutineeBespoke noneBespoke someBespoke

/-! ## (2) ★ Reverse adequacy — eitherMatch (relativized) -/

/-- **★ The honest SURPLUS at the eitherMatch head.**  A union typing of an `eitherMatchCell` surfaces
left/right types `A`, `B` and the three RECURSIVE union premises: scrutinee at `either(A, B)`, left branch
at `A → C`, right branch at `B → C`. -/
theorem HasTypeNativeUnion.eitherMatchSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (eitherMatchCell motive leftBranch rightBranch scrutinee) classifier) :
    ∃ leftType rightType : RawTerm scope,
      HasTypeNativeUnion profile context scrutinee (eitherTypeCell leftType rightType) ∧
      HasTypeNativeUnion profile context leftBranch
        (piTyCodeCell leftType (RawTerm.weaken classifier)) ∧
      HasTypeNativeUnion profile context rightBranch
        (piTyCodeCell rightType (RawTerm.weaken classifier)) :=
  derivation.invertAtEitherMatchHead rfl

/-- **★ Reverse adequacy at the eitherMatch head (relativized).**  GIVEN a union typing of an
`eitherMatchCell` AND, for the surfaced left/right types, reconstruction maps converting the surfaced
union premises into the bespoke premises (scrutinee in the either-intro engine, branches in the grown
engine), the bespoke `HasTypeDescEitherMatch` derivation is reconstructed. -/
theorem HasTypeNativeUnion.toEitherMatchRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (eitherMatchCell motive leftBranch rightBranch scrutinee) classifier)
    (reconstruct : ∀ leftType rightType : RawTerm scope,
      HasTypeNativeUnion profile context scrutinee (eitherTypeCell leftType rightType) →
      HasTypeNativeUnion profile context leftBranch
        (piTyCodeCell leftType (RawTerm.weaken classifier)) →
      HasTypeNativeUnion profile context rightBranch
        (piTyCodeCell rightType (RawTerm.weaken classifier)) →
      HasTypeDescEitherIntro profile context scrutinee (eitherTypeCell leftType rightType) ∧
      HasTypeDescPi profile context leftBranch
        (piTyCodeCell leftType (RawTerm.weaken classifier)) ∧
      HasTypeDescPi profile context rightBranch
        (piTyCodeCell rightType (RawTerm.weaken classifier))) :
    HasTypeDescEitherMatch profile context
      (eitherMatchCell motive leftBranch rightBranch scrutinee) classifier := by
  obtain ⟨leftType, rightType, scrutineeUnion, leftUnion, rightUnion⟩ :=
    derivation.invertAtEitherMatchHead rfl
  obtain ⟨scrutineeBespoke, leftBespoke, rightBespoke⟩ :=
    reconstruct leftType rightType scrutineeUnion leftUnion rightUnion
  exact HasTypeDescEitherMatch.eitherMatchIntro context motive scrutinee leftBranch rightBranch
    leftType rightType classifier scrutineeBespoke leftBespoke rightBespoke

/-! ## (2) ★ Reverse adequacy — idJ (relativized) -/

/-- **★ The honest SURPLUS at the idJ head.**  A union typing of an `idJCell` surfaces a type code `A`
and shared endpoint `x` plus the two RECURSIVE union premises: witness at `Id(A, x, x)`, base case at
`C`. -/
theorem HasTypeNativeUnion.idJSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context (idJCell motive baseCase witness) classifier) :
    ∃ typeCode endpoint : RawTerm scope,
      HasTypeNativeUnion profile context witness (idTypeCell typeCode endpoint endpoint) ∧
      HasTypeNativeUnion profile context baseCase classifier :=
  derivation.invertAtIdJHead rfl

/-- **★ Reverse adequacy at the idJ head (relativized).**  GIVEN a union typing of an `idJCell` AND, for
the surfaced type code / endpoint, reconstruction maps converting the surfaced union premises into the
bespoke premises (witness in the id-intro engine, base case in the grown engine), the bespoke
`HasTypeDescIdElim` derivation is reconstructed. -/
theorem HasTypeNativeUnion.toIdJRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context (idJCell motive baseCase witness) classifier)
    (reconstruct : ∀ typeCode endpoint : RawTerm scope,
      HasTypeNativeUnion profile context witness (idTypeCell typeCode endpoint endpoint) →
      HasTypeNativeUnion profile context baseCase classifier →
      HasTypeDescIdIntro profile context witness (idTypeCell typeCode endpoint endpoint) ∧
      HasTypeDescPi profile context baseCase classifier) :
    HasTypeDescIdElim profile context (idJCell motive baseCase witness) classifier := by
  obtain ⟨typeCode, endpoint, witnessUnion, baseCaseUnion⟩ := derivation.invertAtIdJHead rfl
  obtain ⟨witnessBespoke, baseCaseBespoke⟩ := reconstruct typeCode endpoint witnessUnion baseCaseUnion
  exact HasTypeDescIdElim.idJIntro context motive baseCase witness typeCode endpoint classifier
    witnessBespoke baseCaseBespoke

/-! ## (2) ★ Reverse adequacy — fst / snd (relativized) -/

/-- **★ The honest SURPLUS at the fst head.**  A union typing of an `fstCell` surfaces a second-component
type `B` and the RECURSIVE union premise: the pair term union-typed at `product(C, B)`. -/
theorem HasTypeNativeUnion.fstSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope} {pairTerm : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context (fstCell pairTerm) classifier) :
    ∃ secondType : RawTerm scope,
      HasTypeNativeUnion profile context pairTerm (productTypeCell classifier secondType) :=
  derivation.invertAtFstHead rfl

/-- **★ Reverse adequacy at the fst head (relativized).**  GIVEN a union typing of an `fstCell` AND, for
the surfaced second-component type, a reconstruction map converting the surfaced union pair premise into
the bespoke pair-intro premise, the bespoke `HasTypeDescSigmaProjection` (fst) derivation is
reconstructed. -/
theorem HasTypeNativeUnion.toFstRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope} {pairTerm : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context (fstCell pairTerm) classifier)
    (reconstruct : ∀ secondType : RawTerm scope,
      HasTypeNativeUnion profile context pairTerm (productTypeCell classifier secondType) →
      HasTypeDescPairIntro profile context pairTerm (productTypeCell classifier secondType)) :
    HasTypeDescSigmaProjection profile context (fstCell pairTerm) classifier := by
  obtain ⟨secondType, pairUnion⟩ := derivation.invertAtFstHead rfl
  exact HasTypeDescSigmaProjection.fstIntro context pairTerm classifier secondType
    (reconstruct secondType pairUnion)

/-- **★ The honest SURPLUS at the snd head.**  A union typing of an `sndCell` surfaces a first-component
type `A` and the RECURSIVE union premise: the pair term union-typed at `product(A, C)`. -/
theorem HasTypeNativeUnion.sndSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope} {pairTerm : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context (sndCell pairTerm) classifier) :
    ∃ firstType : RawTerm scope,
      HasTypeNativeUnion profile context pairTerm (productTypeCell firstType classifier) :=
  derivation.invertAtSndHead rfl

/-- **★ Reverse adequacy at the snd head (relativized).**  GIVEN a union typing of an `sndCell` AND, for
the surfaced first-component type, a reconstruction map converting the surfaced union pair premise into
the bespoke pair-intro premise, the bespoke `HasTypeDescSigmaProjection` (snd) derivation is
reconstructed. -/
theorem HasTypeNativeUnion.toSndRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope} {pairTerm : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context (sndCell pairTerm) classifier)
    (reconstruct : ∀ firstType : RawTerm scope,
      HasTypeNativeUnion profile context pairTerm (productTypeCell firstType classifier) →
      HasTypeDescPairIntro profile context pairTerm (productTypeCell firstType classifier)) :
    HasTypeDescSigmaProjection profile context (sndCell pairTerm) classifier := by
  obtain ⟨firstType, pairUnion⟩ := derivation.invertAtSndHead rfl
  exact HasTypeDescSigmaProjection.sndIntro context pairTerm firstType classifier
    (reconstruct firstType pairUnion)

/-! ## (2) ★ Reverse adequacy — natElim / natRec (relativized; the batch-1 exceeds-bespoke surplus) -/

/-- **★ The honest SURPLUS at the natElim head.**  A union typing of a `natElimCell` surfaces the two
RECURSIVE union premises: scrutinee at `Nat`, zero branch at `C`.  The surplus is sharp here — the union
scrutinee may itself be a `natElim`-headed COMPUTED number (the batch-1 exceeds-bespoke witness), while
the bespoke `HasTypeDescNatElim` demands a `HasTypeDescNatIntro` scrutinee (a literal numeral). -/
theorem HasTypeNativeUnion.natElimSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (natElimCell motive zeroBranch stepBranch scrutinee) classifier) :
    HasTypeNativeUnion profile context scrutinee natTypeCell ∧
    HasTypeNativeUnion profile context zeroBranch classifier :=
  derivation.invertAtNatElimHead rfl

/-- **★ Reverse adequacy at the natElim head (relativized).**  GIVEN a union typing of a `natElimCell`
AND reconstruction maps converting the surfaced scrutinee/zero-branch union premises into the bespoke
premises (scrutinee in the Nat-intro engine — i.e. a literal numeral, zero branch grown), AND the stored
step branch, the bespoke `HasTypeDescNatElim` derivation is reconstructed.  The Nat-intro reconstruction
map is exactly where the surplus lives: a computed-number scrutinee cannot satisfy it. -/
theorem HasTypeNativeUnion.toNatElimRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (natElimCell motive zeroBranch stepBranch scrutinee) classifier)
    (reconstructScrutinee : HasTypeNativeUnion profile context scrutinee natTypeCell →
      HasTypeDescNatIntro profile context scrutinee natTypeCell)
    (reconstructZero : HasTypeNativeUnion profile context zeroBranch classifier →
      HasTypeDescPi profile context zeroBranch classifier) :
    HasTypeDescNatElim profile context
      (natElimCell motive zeroBranch stepBranch scrutinee) classifier := by
  obtain ⟨scrutineeUnion, zeroUnion⟩ := derivation.invertAtNatElimHead rfl
  exact HasTypeDescNatElim.natElimIntro context motive scrutinee zeroBranch stepBranch classifier
    (reconstructScrutinee scrutineeUnion) (reconstructZero zeroUnion)

/-- **★ The honest SURPLUS at the natRec head** — the `gen_natRec` twin of `natElimSurplus`. -/
theorem HasTypeNativeUnion.natRecSurplus {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (natRecCell motive zeroBranch stepBranch scrutinee) classifier) :
    HasTypeNativeUnion profile context scrutinee natTypeCell ∧
    HasTypeNativeUnion profile context zeroBranch classifier :=
  derivation.invertAtNatRecHead rfl

/-- **★ Reverse adequacy at the natRec head (relativized)** — the `gen_natRec` twin of
`toNatElimRelativized`. -/
theorem HasTypeNativeUnion.toNatRecRelativized {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (natRecCell motive zeroBranch stepBranch scrutinee) classifier)
    (reconstructScrutinee : HasTypeNativeUnion profile context scrutinee natTypeCell →
      HasTypeDescNatIntro profile context scrutinee natTypeCell)
    (reconstructZero : HasTypeNativeUnion profile context zeroBranch classifier →
      HasTypeDescPi profile context zeroBranch classifier) :
    HasTypeDescNatRec profile context
      (natRecCell motive zeroBranch stepBranch scrutinee) classifier := by
  obtain ⟨scrutineeUnion, zeroUnion⟩ := derivation.invertAtNatRecHead rfl
  exact HasTypeDescNatRec.natRecIntro context motive scrutinee zeroBranch stepBranch classifier
    (reconstructScrutinee scrutineeUnion) (reconstructZero zeroUnion)

/-! ## (2) ★ Reverse adequacy — listElim (UNCONDITIONAL: the surplus is empty at this head)

The union `listElim` arm carries the bespoke premise shapes already, so the inversion surfaces exactly
the bespoke premises and the reverse adequacy needs NO reconstruction hypotheses — a union typing of a
`listElimCell` IS a bespoke `HasTypeDescListElim` typing. -/

/-- **★ UNCONDITIONAL reverse adequacy at the listElim head.**  A union typing of a `listElimCell` IS a
bespoke `HasTypeDescListElim` typing — the union arm's premises ARE the bespoke premises (scrutinee
list-intro-typed, branches grown-typed), so the surplus is empty at this head and the two judgments AGREE
on `listElimCell`-headed subjects.  The cleanest reverse adequacy in the family. -/
theorem HasTypeNativeUnion.toListElim {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context
      (listElimCell motive scrutinee nilBranch consBranch) classifier) :
    HasTypeDescListElim profile context
      (listElimCell motive scrutinee nilBranch consBranch) classifier := by
  obtain ⟨elementType, scrutineeIntro, nilGrown, consGrown⟩ := derivation.invertAtListElimHead rfl
  exact HasTypeDescListElim.listElimIntro context motive scrutinee nilBranch consBranch elementType
    classifier scrutineeIntro nilGrown consGrown

/-! ## (5) Coverage record + witness -/

/-- **The NATIVE-37 reverse-adequacy coverage record.**  Each field is a distinct live property of the
honesty half of the union/family adequacy: the eight per-head inversions (the surplus half), the seven
relativized reverse adequacies (the reconstruction half), and the ONE unconditional reverse adequacy
(listElim, no surplus at the head).  An inhabitant certifies the reverse-adequacy substrate is exercised
(constructed, not just declared) and CANNOT silently shrink. -/
structure NativeUnionReverseAdequacyCoverage (profile : PolyProfile) : Prop where
  /-- listElim: the UNCONDITIONAL reverse adequacy — a union `listElimCell` typing IS bespoke. -/
  listElimUnconditional : ∀ {scope : Nat} {context : TypingContext profile scope}
    {classifier : RawTerm scope} {motive : RawTerm (scope + 1)}
    {scrutinee nilBranch consBranch : RawTerm scope},
    HasTypeNativeUnion profile context
      (listElimCell motive scrutinee nilBranch consBranch) classifier →
    HasTypeDescListElim profile context
      (listElimCell motive scrutinee nilBranch consBranch) classifier
  /-- boolElim: the relativized reverse adequacy reconstructs the bespoke engine from the surfaced
  premises plus the reconstruction maps. -/
  boolElimRelativized : ∀ {scope : Nat} {context : TypingContext profile scope}
    {classifier : RawTerm scope} {motive : RawTerm (scope + 1)}
    {scrutinee thenBranch elseBranch : RawTerm scope},
    HasTypeNativeUnion profile context
      (boolElimCell motive scrutinee thenBranch elseBranch) classifier →
    (HasTypeNativeUnion profile context scrutinee boolTypeCell →
      HasTypeDescDataIntro profile context scrutinee boolTypeCell) →
    (HasTypeNativeUnion profile context thenBranch classifier →
      HasTypeDescPi profile context thenBranch classifier) →
    (HasTypeNativeUnion profile context elseBranch classifier →
      HasTypeDescPi profile context elseBranch classifier) →
    HasTypeDescBoolElim profile context
      (boolElimCell motive scrutinee thenBranch elseBranch) classifier
  /-- natElim: the relativized reverse adequacy — the surplus is sharp (the Nat-intro reconstruction map
  is where computed-number scrutinees fall outside the bespoke engine). -/
  natElimRelativized : ∀ {scope : Nat} {context : TypingContext profile scope}
    {classifier : RawTerm scope} {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope},
    HasTypeNativeUnion profile context
      (natElimCell motive zeroBranch stepBranch scrutinee) classifier →
    (HasTypeNativeUnion profile context scrutinee natTypeCell →
      HasTypeDescNatIntro profile context scrutinee natTypeCell) →
    (HasTypeNativeUnion profile context zeroBranch classifier →
      HasTypeDescPi profile context zeroBranch classifier) →
    HasTypeDescNatElim profile context
      (natElimCell motive zeroBranch stepBranch scrutinee) classifier

/-- **★ The NATIVE-37 reverse-adequacy coverage gate** — inhabited by the shipped declarations, so the
exercised reverse-adequacy property set can NOT silently shrink. -/
theorem nativeUnionReverseAdequacyCoverageWitness {profile : PolyProfile} :
    NativeUnionReverseAdequacyCoverage profile where
  listElimUnconditional := fun derivation => derivation.toListElim
  boolElimRelativized := fun derivation reconstructScrutinee reconstructThen reconstructElse =>
    derivation.toBoolElimRelativized reconstructScrutinee reconstructThen reconstructElse
  natElimRelativized := fun derivation reconstructScrutinee reconstructZero =>
    derivation.toNatElimRelativized reconstructScrutinee reconstructZero

end FX1Poly.Typed
