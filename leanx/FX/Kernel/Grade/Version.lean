import FX.Kernel.Grade.Tier

/-!
# Version (dimension 21) — code identity across revisions

Per `fx_design.md` §6.3 (dim 21), §15 (contracts), and §25.4
(automatic version computation).  Tier V in the spec.

## Version labels

Every FX declaration has a version label.  Surface syntax:

  * No annotation          → `version 1` (implicit default)
  * `@[version(N)]`        → `version N`

The kernel carrier is `Nat`: `0` is reserved for "unversioned
/ not applicable" (a declaration existing before the contract
layer is elaborated), and positive naturals are the user-
visible version labels.  Phase-1 uses `Nat` directly; Phase-2+
may refine to a custom struct carrying adapter metadata.

## Algebra

Parallel combine (`add`) is `Nat.max` — when two versioned
bindings meet (e.g., two arms of an `if`), the combined binding
lives at the newer version.  The assumption is that adapters
exist to lift the older to the newer (via `migration` edges
declared in a contract; §14.2), so the union typechecks.  If
the two versions are incomparable (i.e., no adapter exists),
the compiler's contract layer rejects before reaching the
grade-level check; the kernel `add` is thus sound for the
coarse lattice.

Sequential combine (`mul`) is also `Nat.max` — chaining a v1
operation with a v2 operation produces a v-max result.

  * add v1 v2 = Nat.max v1 v2
  * mul v1 v2 = Nat.max v1 v2
  * `0` is the identity (additive absorbing-by-below — any
    versioned binding absorbs the unversioned).

## Subsumption

`v1 ≤ v2` means "a v1-labelled value is usable where a v2-
labelled value is expected".  Per §15, adapters flow FORWARD
(v1 → v2 when v2 = v1 + 1 migration), so older versions are
the subsumed "less demanding" labels: `v1 ≤ v2` iff `Nat.le v1
v2`.

The kernel encodes this via `Nat.le`: `LessEq v1 v2 = v1 ≤ v2`.
Decidable via `Nat.decLe`.

Bottom: `0` (unversioned).
Top: there is no top — version labels grow unboundedly.
`add` being `Nat.max` is still sound: for any finite set of
labels used in a program, their max exists.

## Appendix H.8 realization

This file realizes the Tier-V slot of `Grade-semiring-laws`.
None of the laws are axioms — all are provable over `Nat.max`
and `Nat.le`.  The adapter-graph structure (§15.4) is a
separate Phase-6 concern that sits **above** the grade-level
lattice; this kernel interface doesn't change when adapters
arrive.
-/

namespace FX.Kernel

/-- Version label — a natural-number code revision tag.
    `0` reserved for "no version / legacy". -/
structure Version where
  label : Nat := 1
  deriving DecidableEq, Repr

namespace Version

/-- Unversioned — used as the grade-default and as the
    identity for `add`/`mul`. -/
def unversioned : Version := ⟨0⟩

/-- Parallel combine — take the newer version (Nat.max).  The
    "newer adapts" assumption: if both labels are present in a
    program, adapter chains exist to promote the older to the
    newer.  The contract layer rejects programs where no such
    adapter exists before the kernel sees them. -/
def add (leftVersion rightVersion : Version) : Version :=
  ⟨Nat.max leftVersion.label rightVersion.label⟩

/-- Sequential combine — same `Nat.max`, same reasoning. -/
def mul (leftVersion rightVersion : Version) : Version := add leftVersion rightVersion

/-! ## Subsumption

Older versions subsume newer via forward-directed adapter
chains (§15.4 migration edges).  `v1 ≤ v2` iff `v1.label ≤
v2.label` — a v1-labelled binding is usable where a v2-
labelled one is expected because the adapter `v1 → v2` exists.
-/

inductive LessEq : Version → Version → Prop where
  | mk : ∀ {leftLabel rightLabel}, leftLabel ≤ rightLabel →
           LessEq ⟨leftLabel⟩ ⟨rightLabel⟩

instance : LE Version := ⟨LessEq⟩

theorem LessEq.refl (version : Version) : version ≤ version :=
  LessEq.mk (Nat.le_refl version.label)

theorem LessEq.trans {lowerVersion middleVersion upperVersion : Version}
    (lowerLeMiddle : lowerVersion ≤ middleVersion)
    (middleLeUpper : middleVersion ≤ upperVersion) :
    lowerVersion ≤ upperVersion := by
  cases lowerLeMiddle with
  | mk lowerLe =>
    cases middleLeUpper with
    | mk middleLe =>
      exact LessEq.mk (Nat.le_trans lowerLe middleLe)

instance decLe : (leftVersion rightVersion : Version)
    → Decidable (LessEq leftVersion rightVersion)
  | ⟨leftLabel⟩, ⟨rightLabel⟩ =>
    if hLe : leftLabel ≤ rightLabel then
      isTrue (LessEq.mk hLe)
    else
      isFalse (fun contra => by cases contra; contradiction)

/-! ## Laws -/

theorem add_comm (leftVersion rightVersion : Version) :
    add leftVersion rightVersion = add rightVersion leftVersion := by
  simp [add, Nat.max_comm]

theorem add_assoc (leftVersion middleVersion rightVersion : Version) :
    add (add leftVersion middleVersion) rightVersion
      = add leftVersion (add middleVersion rightVersion) := by
  simp [add, Nat.max_assoc]

theorem add_idem (version : Version) : add version version = version := by
  cases version with
  | mk label => simp [add]

theorem unversioned_add (version : Version) : add unversioned version = version := by
  cases version with
  | mk label => simp [add, unversioned]

theorem add_unversioned (version : Version) : add version unversioned = version := by
  cases version with
  | mk label => simp [add, unversioned]

theorem mul_comm (leftVersion rightVersion : Version) :
    mul leftVersion rightVersion = mul rightVersion leftVersion :=
  add_comm leftVersion rightVersion

theorem mul_assoc (leftVersion middleVersion rightVersion : Version) :
    mul (mul leftVersion middleVersion) rightVersion
      = mul leftVersion (mul middleVersion rightVersion) :=
  add_assoc leftVersion middleVersion rightVersion

theorem mul_idem (version : Version) : mul version version = version :=
  add_idem version

theorem unversioned_mul (version : Version) : mul unversioned version = version :=
  unversioned_add version

theorem mul_unversioned (version : Version) : mul version unversioned = version :=
  add_unversioned version

/-- `unversioned` is the bottom: every version is `≥ unversioned`. -/
theorem unversioned_le (version : Version) : unversioned ≤ version := by
  cases version with
  | mk label => exact LessEq.mk (Nat.zero_le label)

end Version

/-! ## TierV instance (T5)

Version fits Tier V's versioned-lattice shape: `meet := Nat.max` is
total (no validity failure at the kernel level), commutative, and
associative.  Adapter resolution (§15.6) sits above the kernel in
the elaborator; `consistent` below is the kernel-level "same or
sub-label" check — the elaborator consults the adapter graph when
this returns `false`. -/
def consistent : Version → Version → Bool
  | ⟨leftLabel⟩, ⟨rightLabel⟩ => leftLabel = rightLabel || leftLabel < rightLabel

/-- `consistent` is reflexive: every version flows to itself
    without adapter.  Required by `TierV.consistent_refl` (T6).
    Trivial because the left disjunct `leftLabel = rightLabel` is
    `true` when both are the same Nat. -/
theorem consistent_refl (version : Version) : consistent version version = true := by
  cases version with
  | mk label =>
    simp [consistent]

instance : TierV Version where
  default         := Version.unversioned
  le              := Version.LessEq
  le_refl         := Version.LessEq.refl
  le_trans        := Version.LessEq.trans
  meet            := Version.add
  meet_comm       := Version.add_comm
  meet_assoc      := Version.add_assoc
  consistent      := consistent
  consistent_refl := consistent_refl

end FX.Kernel
