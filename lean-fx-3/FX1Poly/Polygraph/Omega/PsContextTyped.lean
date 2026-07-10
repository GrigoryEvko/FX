import FX1Poly.Polygraph.Omega.PsContext

/-! # Polygraph/Omega/PsContextTyped — the CaTT ps-context as a TYPED telescope on de Bruijn LEVELS
    (OMEGA-6 r2, B1)

★ **The typed telescope the r1 flat ps-context deferred — shipped on de Bruijn LEVELS so weakening is FREE
and substitution stays genuinely OMEGA-7.**  r1 (`PsContext.lean`) ships the ps-judgment as a flat move
sequence `PsContextRow` + the focus-dimension stack walk `psFocus` / `psContextCheck`.  Its docstring defers
"typed variables, a telescope, or substitution" to OMEGA-7 because a naive typed telescope drags
weakening / substitution.  r2 discharges the TYPING half of that deferral without dragging substitution, via
the load-bearing encoding decision:

## The load-bearing decision — de Bruijn LEVELS (distance-from-base), not indices

A CaTT context is a telescope `(x0 : A0), …, (x_{n-1} : A_{n-1})` where each `Ai` is `* | (s ->_A t)` with
`s, t` earlier variables.  Under de Bruijn INDICES (distance-from-END) appending a fresh variable shifts every
earlier index — that shift IS the weakening the r1 caveat feared.  Under de Bruijn LEVELS (distance-from-BASE)
appending a fresh variable at the end leaves every earlier level UNCHANGED — weakening is the trivial inclusion
`< n -> < n+1` (monotonicity of `<`), NOT a shift.  Substitution (instantiating a variable by a term) is a
DIFFERENT operation and stays deferred to OMEGA-7 ("substitution = pasting").  So r2 honestly ships "typed
telescope" while the substitution half of `fxOmega6_psContextTypedTelescope` remains genuinely open.

Consequence: `TeleType` is a SINGLE FLAT inductive with `Nat` levels as fields — NOT mutual, NOT `Nat`-indexed,
NOT `Fin`-indexed.  This sidesteps three minefields at once: the mutual term/type positivity wall, the
indexed-partial-match `propext` trap (`Carrier.lean` documents that exact trap), and the `Fin.cases` axiom
trap.  Scope is EXTRINSIC (matching the substrate discipline — `IsGlobularCell`, `psContextCheck` are all
extrinsic `Bool` / `Prop`).

## What ships (each piece zero-axiom, structural, ASCII-only)

  * **`TeleType`** — the boundary-type language `* | (s ->_A t)` with `Nat` LEVEL endpoints, `teleTypeDim` its
    dimension slot, `teleTypeBeq` structural equality.
  * **`teleTypeWellScoped` / `telescopeWellFormed`** — extrinsic well-scopedness (levels `< bound`) plus the
    typing discipline that a hom `s ->_A t`'s endpoints carry the base type (`telescope[s] = A = telescope[t]`).
  * **`elaboratePsContext`** — the TYPED elaborator: it refines the r1 move walk into a focus tracking
    `(telescope, level, type)` instead of only the dimension.  `pse` appends the fresh target `y` (type `A`,
    parallel to `x`) and the arrow `f : x ->_A y`; `psd` relocates the focus from the arrow to its target
    `y : A`; the final check accepts iff the focus type is `star`.
  * **`psTypedCheck`** — accept iff the elaboration's focus type is `star` (the CaTT ps-final rule, typed).
  * ★ **`psTypedCheck_implies_psContextCheck`** — THE ERASURE COMMUTING LEMMA: the typed check implies the r1
    untyped check, because `teleTypeDim (focus type)` IS the r1 `psFocus` (star ↦ 0, arrow ↦ dim + 1).

## Honesty (state it, do not over-claim)

On the bare move-sequence spine the types are FORCED (`pse` has no free choice), so `psTypedCheck` and
`psContextCheck` are EQUIVALENT (both directions shipped: `psTypedCheck_implies_psContextCheck` and the honest
converse `psContextCheck_implies_psTypedCheck`) — the typed ps-checker adds NO extra rejection at the ps-checker
level.  Claiming it is "strictly stronger" would be an over-claim.  Its value is that it PRODUCES the typed
context OBJECT (`PsTelescope`) that the coh fullness gate (`CohGateTyped.lean`) and the OMEGA-7 pasting engine
consume, and the typing becomes LOAD-BEARING at the coh gate, where boundary supports are supplied independently.

Raw Lean 4 + Init, STRUCTURAL only, ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The boundary-type language on de Bruijn levels -/

/-- A **telescope type** — the CaTT boundary-type language `* | (s ->_A t)` with de Bruijn LEVEL endpoints.
`star` is the object type `*` (dimension 0); `arrow base sourceLevel targetLevel` is the hom `s ->_base t`
whose two endpoint variables sit at `sourceLevel` / `targetLevel` and whose base type is `base`.  A single
FLAT inductive (levels are `Nat` FIELDS, not an index), so no mutual / positivity / indexed-match wall. -/
inductive TeleType where
  /-- The object type `*` at dimension 0. -/
  | star : TeleType
  /-- The hom type `sourceLevel ->_base targetLevel`, one dimension above `base`. -/
  | arrow : TeleType → Nat → Nat → TeleType
  deriving Repr

/-- The **dimension** of a telescope type: `star` is dimension 0, a hom over `base` is `teleTypeDim base + 1`.
Constant `Nat` motive, full enumeration — propext-free.  This is the erasure map: `teleTypeDim` of a focus
type IS the r1 `psFocus` dimension. -/
def teleTypeDim : TeleType → Nat
  | .star => 0
  | .arrow base _ _ => teleTypeDim base + 1

/-- Structural **`Bool` equality of telescope types** — full constructor enumeration (no wildcard), so
propext-free; levels compared by `Nat.beq`. -/
def teleTypeBeq : TeleType → TeleType → Bool
  | .star, .star => true
  | .arrow baseA sourceA targetA, .arrow baseB sourceB targetB =>
      teleTypeBeq baseA baseB && Nat.beq sourceA sourceB && Nat.beq targetA targetB
  | .star, .arrow _ _ _ => false
  | .arrow _ _ _, .star => false

/-- A **pasting telescope** — the entry at position `i` is the type of the de Bruijn LEVEL-`i` variable.
Appending a fresh entry at the end leaves every earlier level's meaning unchanged (levels are distance-from
base), so weakening is the trivial list extension, no index shift. -/
abbrev PsTelescope := List TeleType

/-! ## Extrinsic well-scopedness and the endpoint-typing discipline -/

/-- Whether a telescope type is **well-scoped** below `bound`: both endpoint levels are `< bound` and the base
type is recursively well-scoped at the same bound.  Extrinsic `Bool`, structural — propext-free. -/
def teleTypeWellScoped (bound : Nat) : TeleType → Bool
  | .star => true
  | .arrow base sourceLevel targetLevel =>
      Nat.blt sourceLevel bound && Nat.blt targetLevel bound && teleTypeWellScoped bound base

/-- **Look up** the type of a de Bruijn level in a telescope — a cons-recursive positional read, `none` past
the end.  Full enumeration, structural — propext-free (dodges `List.get?`-style library dependencies). -/
def telescopeLookup : PsTelescope → Nat → Option TeleType
  | [], _ => none
  | entryType :: _, 0 => some entryType
  | _ :: rest, level + 1 => telescopeLookup rest level

/-- **`Bool` equality of optional telescope types** — full enumeration, propext-free. -/
def teleTypeOptionBeq : Option TeleType → Option TeleType → Bool
  | some typeA, some typeB => teleTypeBeq typeA typeB
  | none, none => true
  | some _, none => false
  | none, some _ => false

/-- Whether a hom type's **endpoints carry its base type** in `full` — for `arrow base s t`, the level-`s` and
level-`t` variables must both have type `base` (the CaTT discipline that a hom's endpoints live at its base
type); `star` is trivially endpoint-typed. -/
def teleTypeEndpointsTyped (full : PsTelescope) : TeleType → Bool
  | .star => true
  | .arrow base sourceLevel targetLevel =>
      teleTypeOptionBeq (telescopeLookup full sourceLevel) (some base)
        && teleTypeOptionBeq (telescopeLookup full targetLevel) (some base)

/-- The **well-formedness walk** carrying the current level `index` and the full telescope for endpoint
lookups: every entry is well-scoped at its own level and endpoint-typed.  Structural on the suffix. -/
def telescopeWellFormedFrom (full : PsTelescope) : Nat → PsTelescope → Bool
  | _, [] => true
  | index, entryType :: rest =>
      teleTypeWellScoped index entryType
        && teleTypeEndpointsTyped full entryType
        && telescopeWellFormedFrom full (index + 1) rest

/-- ★ Whether a telescope is **well-formed**: each entry `i` is well-scoped at `i` (levels refer only to
earlier entries) and every hom's endpoints carry its base type.  The decidable typed-context predicate the
OMEGA-7 pasting engine types boundaries over. -/
def telescopeWellFormed (telescope : PsTelescope) : Bool :=
  telescopeWellFormedFrom telescope 0 telescope

/-! ## The typed elaborator — refine the r1 walk, tracking (telescope, level, type) -/

/-- A **ps-elaboration state** — the typed context built so far plus the current focus variable's LEVEL and
TYPE.  The r1 `psFocus` tracks only the dimension; this tracks the full focus. -/
structure PsElaboration where
  /-- The typed context accumulated so far (level `i` ↦ entry `i`). -/
  telescope : PsTelescope
  /-- The de Bruijn level of the current focus variable. -/
  focusLevel : Nat
  /-- The type of the current focus variable. -/
  focusType : TeleType
  deriving Repr

/-- The **`pse` step** (extend): from focus `(Γ, x@xLevel : A)` push a fresh target `y : A` (parallel to `x`)
at level `Γ.length` and the arrow `f : x ->_A y` at level `Γ.length + 1`; the focus moves UP to `f`. -/
def extendFocus (elaboration : PsElaboration) : PsElaboration :=
  { telescope := elaboration.telescope ++
      [elaboration.focusType,
       TeleType.arrow elaboration.focusType elaboration.focusLevel elaboration.telescope.length],
    focusLevel := elaboration.telescope.length + 1,
    focusType := TeleType.arrow elaboration.focusType elaboration.focusLevel elaboration.telescope.length }

/-- The **`psd` step** (drop): from focus `f@_ : (s ->_A t)` relocate the focus DOWN to the target `t : A`;
from focus type `star` this underflows (dropping below the base is not a ps-move) — `none`. -/
def dropFocus (elaboration : PsElaboration) : Option PsElaboration :=
  match elaboration.focusType with
  | TeleType.arrow baseType _ targetLevel =>
      some { telescope := elaboration.telescope, focusLevel := targetLevel, focusType := baseType }
  | TeleType.star => none

/-- ★ The **typed elaborator** — walk the r1 move sequence, tracking the full focus `(telescope, level, type)`.
`start` is the singleton object context `[*]` with focus `(0, *)`; `extend` is `Option.map extendFocus`;
`drop` is `Option.bind dropFocus` (underflow ↦ `none`).  Structural recursion on the prior row. -/
def elaboratePsContext : PsContextRow → Option PsElaboration
  | .start => some { telescope := [TeleType.star], focusLevel := 0, focusType := TeleType.star }
  | .extend prior => (elaboratePsContext prior).map extendFocus
  | .drop prior => (elaboratePsContext prior).bind dropFocus

/-- **Project the telescope** out of an elaboration result (`[]` on underflow) — the typed context object the
coh gate and OMEGA-7 consume. -/
def telescopeOf : Option PsElaboration → PsTelescope
  | some elaboration => elaboration.telescope
  | none => []

/-- ★ The **typed ps-judgment**: accept iff the elaboration's focus type is `star` (the CaTT ps-final rule, at
the type level).  Full enumeration on `Option` and `TeleType` — propext-free. -/
def psTypedCheck (row : PsContextRow) : Bool :=
  match elaboratePsContext row with
  | some elaboration =>
      match elaboration.focusType with
      | TeleType.star => true
      | TeleType.arrow _ _ _ => false
  | none => false

/-! ## The erasure commuting lemma — the typed check refines the r1 untyped check -/

/-- A telescope type of **dimension 0 is `star`** — the erasure map's fibre over 0.  Cases on the type. -/
theorem teleTypeDim_eq_zero : ∀ {telescopeType : TeleType}, teleTypeDim telescopeType = 0 →
    telescopeType = TeleType.star
  | .star, _ => rfl
  | .arrow _ _ _, hDim => Nat.noConfusion hDim

/-- ★ **The erasure coupling**: erasing the focus TYPE to its dimension (`teleTypeDim`) turns the typed
elaboration into the r1 `psFocus` walk.  Both recursions have identical shape (`extend` maps the focus up one
dimension, `drop` relocates it down, underflow at `star`), so `teleTypeDim ∘ focusType` transports the typed
result onto `psFocus` exactly.  Structural induction on the row. -/
theorem elaborate_focusDim_eq_psFocus (row : PsContextRow) :
    Option.map (fun elaboration => teleTypeDim elaboration.focusType) (elaboratePsContext row)
      = psFocus row := by
  induction row with
  | start => rfl
  | extend prior ih =>
      show Option.map (fun elaboration => teleTypeDim elaboration.focusType)
          ((elaboratePsContext prior).map extendFocus) = psFocus (PsContextRow.extend prior)
      cases hPrior : elaboratePsContext prior with
      | none =>
          have hFocus : psFocus prior = none := by rw [hPrior] at ih; exact ih.symm
          unfold psFocus; rw [hFocus]; rfl
      | some elaboration =>
          have hFocus : psFocus prior = some (teleTypeDim elaboration.focusType) := by
            rw [hPrior] at ih; exact ih.symm
          unfold psFocus; rw [hFocus]; rfl
  | drop prior ih =>
      show Option.map (fun elaboration => teleTypeDim elaboration.focusType)
          ((elaboratePsContext prior).bind dropFocus) = psFocus (PsContextRow.drop prior)
      cases hPrior : elaboratePsContext prior with
      | none =>
          have hFocus : psFocus prior = none := by rw [hPrior] at ih; exact ih.symm
          unfold psFocus; rw [hFocus]; rfl
      | some elaboration =>
          obtain ⟨telescope, focusLevel, focusType⟩ := elaboration
          have hFocus : psFocus prior = some (teleTypeDim focusType) := by
            rw [hPrior] at ih; exact ih.symm
          unfold psFocus; rw [hFocus]
          cases focusType with
          | star => rfl
          | arrow base sourceLevel targetLevel => rfl

/-- ★ **THE ERASURE COMMUTING LEMMA (B1).**  The typed ps-check IMPLIES the r1 untyped ps-check: whenever
`psTypedCheck row = true` (the elaboration's focus type is `star`), the r1 `psContextCheck row = true` (the
r1 focus walk ends at dimension 0).  Via the erasure coupling: the typed check forces
`elaboratePsContext row = some elaboration` with `elaboration.focusType = star`, whence
`psFocus row = some (teleTypeDim star) = some 0` — the r1 acceptance condition. -/
theorem psTypedCheck_implies_psContextCheck (row : PsContextRow) :
    psTypedCheck row = true → psContextCheck row = true := by
  intro hTyped
  cases hElab : elaboratePsContext row with
  | none =>
      unfold psTypedCheck at hTyped
      rw [hElab] at hTyped
      exact absurd hTyped (by decide)
  | some elaboration =>
      obtain ⟨telescope, focusLevel, focusType⟩ := elaboration
      cases focusType with
      | arrow base sourceLevel targetLevel =>
          have hFalse : psTypedCheck row = false := by unfold psTypedCheck; rw [hElab]
          rw [hFalse] at hTyped
          exact Bool.noConfusion hTyped
      | star =>
          have hCoupling := elaborate_focusDim_eq_psFocus row
          rw [hElab] at hCoupling
          have hFocusZero : psFocus row = some 0 := hCoupling.symm
          unfold psContextCheck
          rw [hFocusZero]

/-- ★ **The honest converse.**  On the bare move-sequence spine the types are FORCED, so the r1 untyped check
also implies the typed check — the two checkers are EQUIVALENT, and claiming the typed one is strictly
stronger would be an over-claim.  Via the coupling: `psContextCheck row = true` gives `psFocus row = some 0`,
forcing `elaboratePsContext row = some elaboration` whose focus type erases to dimension 0, hence `star`. -/
theorem psContextCheck_implies_psTypedCheck (row : PsContextRow) :
    psContextCheck row = true → psTypedCheck row = true := by
  intro hUntyped
  have hCoupling := elaborate_focusDim_eq_psFocus row
  cases hElab : elaboratePsContext row with
  | none =>
      rw [hElab] at hCoupling
      have hFocusNone : psFocus row = none := hCoupling.symm
      unfold psContextCheck at hUntyped
      rw [hFocusNone] at hUntyped
      exact absurd hUntyped (by decide)
  | some elaboration =>
      obtain ⟨telescope, focusLevel, focusType⟩ := elaboration
      cases focusType with
      | star =>
          unfold psTypedCheck
          rw [hElab]
      | arrow base sourceLevel targetLevel =>
          rw [hElab] at hCoupling
          have hFocusSucc : psFocus row = some (teleTypeDim base + 1) := hCoupling.symm
          have hFalse : psContextCheck row = false := by unfold psContextCheck; rw [hFocusSucc]
          rw [hFalse] at hUntyped
          exact Bool.noConfusion hUntyped

/-! ## Non-vacuity — the four telescope witnesses -/

/-- The **single-2-cell disk telescope** — elaborating `twoGlobePsContext` yields a genuine typed context
`[*, *, (0 ->_* 1), (0 ->_* 1), ((0 ->_* 1) ->_ 2 3)]` with focus type `star`. -/
def twoGlobeTelescope : Option PsElaboration := elaboratePsContext twoGlobePsContext

/-- The **horizontal-composite telescope** — elaborating `horizontalCompositePsContext` (the Godement /
interchange source) yields the 9-entry typed context with the shared middle object at level 1. -/
def horizontalCompositeTelescope : Option PsElaboration := elaboratePsContext horizontalCompositePsContext

#eval twoGlobeTelescope
#eval horizontalCompositeTelescope

/-- The disk ps-context CHECKS at the typed level. -/
theorem twoGlobePsContext_psTyped : psTypedCheck twoGlobePsContext = true := rfl

/-- The horizontal-composite ps-context CHECKS at the typed level. -/
theorem horizontalCompositePsContext_psTyped : psTypedCheck horizontalCompositePsContext = true := rfl

/-- A dangling context is REJECTED at the typed level (focus stuck on an arrow). -/
theorem danglingPsContext_psTypedFalse : psTypedCheck danglingPsContext = false := rfl

/-- An underflowing context is REJECTED at the typed level (the `drop` underflows to `none`). -/
theorem underflowPsContext_psTypedFalse : psTypedCheck underflowPsContext = false := rfl

/-- ★ The disk telescope is genuinely WELL-FORMED: every hom's endpoints carry its base type and every entry
is well-scoped at its level — the elaborator produces real typed contexts, not just checked shapes. -/
theorem twoGlobeTelescope_wellFormed :
    telescopeWellFormed (telescopeOf twoGlobeTelescope) = true := rfl

/-- ★ The horizontal-composite telescope is genuinely WELL-FORMED. -/
theorem horizontalCompositeTelescope_wellFormed :
    telescopeWellFormed (telescopeOf horizontalCompositeTelescope) = true := rfl

/-- ★ The commuting lemma witnessed on the disk (typed acceptance transports to r1 acceptance). -/
theorem twoGlobe_typed_implies_untyped :
    psContextCheck twoGlobePsContext = true :=
  psTypedCheck_implies_psContextCheck twoGlobePsContext twoGlobePsContext_psTyped

/-- ★ The equivalence witnessed on the disk (r1 acceptance transports back to typed acceptance). -/
theorem twoGlobe_untyped_implies_typed :
    psTypedCheck twoGlobePsContext = true :=
  psContextCheck_implies_psTypedCheck twoGlobePsContext twoGlobePsContext_checks

end FX1Poly.Polygraph.Omega
