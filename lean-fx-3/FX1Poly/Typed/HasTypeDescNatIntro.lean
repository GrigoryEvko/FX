import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.NatTypeCodeSubstrate
import FX1Poly.Typed.CellConstructors

/-! # FX1Poly/Typed/HasTypeDescNatIntro — the standalone Nat introduction judgment
    (DI-3, the nat constructors: `natZero : Nat` and `natSucc(p) : Nat` — a RECURSIVE intro).

The list intro (`HasTypeDescListIntro`, #1077) was the first standalone data-intro judgment with a
self-referential (recursive) constructor; this is the NAT twin, and the simplest one: `Nat` is a
NULLARY ground type (no element type), so `natZero` needs NO premise at all (unlike `listNil`, whose
free element type carries a type-formedness premise), and `natSucc(p)` needs only a RECURSIVE
predecessor premise `p : Nat` typed BY THE SAME judgment.  Same cascade-free pattern (a brand-new
standalone judgment, NOT mutual with / NOT an arm of any existing engine), so it disturbs no recursor.
This is the scrutinee-typing prerequisite for the nat ELIMINATORS (`natElim` / `natRec`) and the
non-vacuous nat canonicity story (`SN-048`).

Like `HasTypeDescListIntro`, this judgment uses `natTypeCell` purely as a RAW classifier — it does NOT
depend on `Nat : Type@0` being derivable (the base-type formation row, deferred to keep the shared
`baseTypeRuleDescOf` / `HasTypeDescBaseType.subjectIsBaseTypeCode` two-way signature cascade-free).

## The two arms

  * `natZeroIntro` — `natZero : Nat` is the NULLARY arm with NO premise: `Nat` is a closed ground type,
    so `natZero` is unconditionally a nat value.  (Simpler than `listNilIntro`, which carries a free
    element-type-formedness premise.)
  * `natSuccIntro` — `natSucc(p) : Nat` is the RECURSIVE arm: a predecessor `p : Nat` typed by
    `HasTypeDescNatIntro` itself.  The recursion (strictly positive) is the genuinely-new structure,
    the nat analogue of `listConsIntro`'s tail premise.

  * `natZeroCell` / `natSuccCell` — the value cells (`gen_natZero`, arity 0; `gen_natSucc`, arity 1
    `[0]`), inline `mkGen`.
  * `HasTypeDescNatIntro` — the judgment, two arms (one nullary-unconditional, one recursive).
  * `HasTypeDescNatIntro.{natZeroTyped, natOneTyped, natTwoTyped}` (★) — the non-vacuous smokes:
    `0 : Nat`, `1 = succ 0 : Nat` (exercising the recursive arm), `2 = succ (succ 0) : Nat` (the
    recursion nested twice — the kernel's first typed nat numerals at a real Nat TYPE code).
  * `HasTypeDescNatIntro.subjectIsNatConstructor` / `classifierIsNat` — the closed-forms inversions
    (the subject IS a `natZero` or `natSucc`; the classifier IS `natTypeCell`).

## SR deferral (same as the other intros)

Judgment + smokes + inversions are SR-free.  The SR/SN quartet (a `natSucc` steps when its predecessor
steps) is the deliberate deferral (the recursive-eliminator engine-separation finding, #1078).

## Zero-axiom

A two-arm positive inductive (the recursive arm is strictly positive); the smokes are direct arm
applications (the `natOne`/`natTwo` smokes nest `natZeroIntro` recursively); the inversions are
free-index `cases` with `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The zero value cell `natZero` — `gen_natZero` (arity 0, no children). -/
def natZeroCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_natZero () .childNil

/-- The successor value cell `natSucc(predecessor)` — `gen_natSucc` (arity 1, `binderShifts = [0]`). -/
def natSuccCell {scope : Nat} (predecessor : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natSucc () (.childCons predecessor .childNil)

/-- **The Nat introduction judgment.**  A standalone layer (NOT mutual with / NOT an arm of any
existing engine) typing the nat value constructors at the nat type code `natTypeCell`.  `natZero` needs
NO premise (`Nat` is a closed ground type); `natSucc(p)` needs a RECURSIVE predecessor premise `p : Nat`
(typed by this judgment itself — strictly positive). -/
inductive HasTypeDescNatIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | natZeroIntro {scope : Nat} (context : TypingContext profile scope) :
      HasTypeDescNatIntro profile context natZeroCell natTypeCell
  | natSuccIntro {scope : Nat} (context : TypingContext profile scope)
      (predecessor : RawTerm scope)
      (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell) :
      HasTypeDescNatIntro profile context (natSuccCell predecessor) natTypeCell

/-- **★ `0 : Nat` is typed.**  The nullary `natZero` smoke — unconditionally a nat value (no premise),
the base of the numeral tower. -/
theorem HasTypeDescNatIntro.natZeroTyped {profile : PolyProfile} :
    HasTypeDescNatIntro profile (TypingContext.empty : TypingContext profile 0)
      natZeroCell natTypeCell :=
  HasTypeDescNatIntro.natZeroIntro TypingContext.empty

/-- **★ `1 = succ 0 : Nat` is typed.**  The RECURSIVE-arm smoke: `natSucc(natZero) : Nat`, exercising
the recursive predecessor premise (`natZero` typed by the same engine via `natZeroIntro`).  The first
nat the kernel types whose constructor exercises the recursive arm. -/
theorem HasTypeDescNatIntro.natOneTyped {profile : PolyProfile} :
    HasTypeDescNatIntro profile (TypingContext.empty : TypingContext profile 0)
      (natSuccCell natZeroCell) natTypeCell :=
  HasTypeDescNatIntro.natSuccIntro TypingContext.empty natZeroCell
    (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)

/-- **★ `2 = succ (succ 0) : Nat` is typed.**  The recursion nested twice — `natSucc(natSucc(natZero))
: Nat`, the predecessor itself a recursive `natSucc`.  Demonstrates the numeral tower the recursive arm
builds. -/
theorem HasTypeDescNatIntro.natTwoTyped {profile : PolyProfile} :
    HasTypeDescNatIntro profile (TypingContext.empty : TypingContext profile 0)
      (natSuccCell (natSuccCell natZeroCell)) natTypeCell :=
  HasTypeDescNatIntro.natSuccIntro TypingContext.empty (natSuccCell natZeroCell)
    (HasTypeDescNatIntro.natSuccIntro TypingContext.empty natZeroCell
      (HasTypeDescNatIntro.natZeroIntro TypingContext.empty))

/-- **★ Closed forms (subject): a nat-intro-typed subject is `natZero` or `natSucc`.**  Every term
typed by `HasTypeDescNatIntro` is `natZero` or `natSucc(p)` — the nat analogue of
`HasTypeDescListIntro.subjectIsListConstructor`.  Two-arm free-index `cases`; the SR-free canonicity
ingredient. -/
theorem HasTypeDescNatIntro.subjectIsNatConstructor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatIntro profile context subject classifier) :
    subject = natZeroCell ∨ (∃ predecessor : RawTerm scope, subject = natSuccCell predecessor) := by
  cases derivation with
  | natZeroIntro =>
      exact Or.inl rfl
  | natSuccIntro predecessor _predecessorTyped =>
      exact Or.inr ⟨predecessor, rfl⟩

/-- **★ Closed forms (classifier): a nat-intro classifier is `natTypeCell`.**  Every classifier a
`HasTypeDescNatIntro` derivation reaches is `Nat` — the classifier-side companion of
`subjectIsNatConstructor`.  Two-arm `cases`. -/
theorem HasTypeDescNatIntro.classifierIsNat {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatIntro profile context subject classifier) :
    classifier = natTypeCell := by
  cases derivation with
  | natZeroIntro =>
      rfl
  | natSuccIntro _predecessor _predecessorTyped =>
      rfl

end FX1Poly.Typed
