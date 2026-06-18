import FX1Poly.Core.Rewriting.Reduction.Preservation.RawTermRenameInjective

/-! # FX1Poly/Core — higher-order PATTERN unification: the inversion engine (term-11)

General higher-order unification is UNDECIDABLE — Goldfarb (1981) reduces Hilbert's tenth problem to
SECOND-ORDER unification, and Huet's procedure is only a semi-decision.  Miller (1991) carved out the
decidable, most-general-unifier-bearing **pattern fragment** (`Lλ`, "higher-order patterns"): a flex term
is a pattern when every metavariable is applied to a spine of DISTINCT bound variables.  Every modern
dependently-typed elaborator (Coq, Agda, Lean, `smalltt`) lives in this fragment; its decidability rests on
one fact — a distinct-variable spine is an INVERTIBLE renaming, so the flex-rigid equation `?M [y1 … yk] ≐ t`
is solved by `?M := λ. t[ρ⁻¹]` and that solution is UNIQUE.

This file ships the genuine, kernel-level core of the pattern fragment over the real `RawTerm`:

  * the pattern predicate (`IsPatternSpine` = the de-Bruijn spine renaming is `Function.Injective`, i.e. the
    metavariable's argument variables are distinct), with the stability law that a pattern stays a pattern
    UNDER A BINDER (`patternSpine_lift`);
  * ★ **MGU uniqueness** (`patternSolution_unique`) — a metavariable applied to a distinct (injective) spine
    has at MOST ONE solution: `bodyA[ρ] = bodyB[ρ] ⟹ bodyA = bodyB`.  This is a direct corollary of the
    shipped term-level renaming-injectivity `RawTerm.rename_injective` — the genuine reason flex-rigid
    pattern solving is deterministic;
  * ★ **the inversion substitution** `ρ⁻¹` (`spineInverse`) with the two laws that make flex-rigid solving
    correct: SOUNDNESS (`spineInverse_sound`: the inverse only ever returns a genuine preimage — no spurious
    bindings) and the round-trip `ρ⁻¹ (ρ i) = some i` (`spineInverse_inverts`: `ρ⁻¹ ∘ ρ = id` on the spine,
    the existence/solve side that elaborators compute, Abel-Pientka "Higher-Order Dynamic Pattern
    Unification");
  * a concrete injective spine witness (`exampleSpine`) whose inversion round-trips.

## Honest scope

The pattern fragment's two pillars — unique solutions (uniqueness) + a computed inverse (existence).
DEFERRED:

  * the full pattern-unification ALGORITHM over arbitrary terms — flex-rigid PRUNING when `t` has variables
    outside the spine, the OCCURS-CHECK, and the flex-flex case of two patterns (intersection of spines);
  * general higher-order unification — Huet's pre-unification SEMI-decision procedure (the deferred
    capstone of the decidable half);
  * the **undecidability boundary** — Goldfarb's theorem that second-order unification is undecidable
    (the formalized Hilbert's-tenth reduction); here it is the documented mathematical boundary, not a
    mechanized negative result.

## Zero-axiom verification

`IsPatternSpine` is `Function.Injective`; uniqueness is `RawTerm.rename_injective`; stability is
`RawRenaming.lift_injective`.  The inverse is a structural Nat-bounded domain search (`findPreimageBelow`,
decreasing on the count), and its two laws are by induction on the bound with the clean `Nat`/`Fin` order
lemmas (`Nat.lt_of_lt_of_le`, `Nat.le_of_lt_succ`, `Nat.lt_of_le_of_ne`, `Fin.eq_of_val_eq`) and proof
irrelevance on the `Fin` bound — no `Nat.add_comm`, no `Fin.cases`, no `Option`-iff lemmas.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCoreUnification.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Tier0.Syntax

/-! ## The pattern predicate + MGU uniqueness (real `RawTerm`) -/

/-- A **higher-order pattern spine** (Miller): the de-Bruijn renaming recording which bound variables the
metavariable is applied to is INJECTIVE — i.e. the argument variables `y1 … yk` are DISTINCT.  Distinctness
is exactly what makes the spine renaming invertible, hence the metavariable solvable. -/
def IsPatternSpine {arity scope : Nat} (spine : RawRenaming arity scope) : Prop :=
  Function.Injective spine

/-- A pattern spine stays a pattern UNDER A BINDER: lifting an injective renaming keeps it injective, so the
metavariable's arguments remain distinct as elaboration descends under a binder (Abel-Pientka). -/
theorem patternSpine_lift {arity scope : Nat} (spine : RawRenaming arity scope)
    (spineIsPattern : IsPatternSpine spine) : IsPatternSpine (RawRenaming.lift spine) :=
  RawRenaming.lift_injective spineIsPattern

/-- ★ **Pattern-fragment MGU uniqueness.**  A metavariable applied to a distinct (injective) spine has at
most one solution: if two candidate bodies instantiate (rename along the spine) to the same term, they are
equal.  The deterministic core of flex-rigid pattern solving — a direct corollary of the term-level
renaming-injectivity `RawTerm.rename_injective`. -/
theorem patternSolution_unique {arity scope : Nat} (spine : RawRenaming arity scope)
    (spineIsPattern : IsPatternSpine spine) (bodyA bodyB : RawTerm arity)
    (instantiationsAgree : RawTerm.rename spine bodyA = RawTerm.rename spine bodyB) :
    bodyA = bodyB :=
  RawTerm.rename_injective spine spineIsPattern bodyA bodyB instantiationsAgree

/-! ## The inversion substitution `ρ⁻¹` -/

/-- Search the domain positions `[0, count)` of an `arity`-many spine for a preimage of `target` — the
construction of the inverse renaming `ρ⁻¹`.  Structural on `count` (no `Fin.cases`; the candidate index is
built directly as `⟨count, _⟩`). -/
def findPreimageBelow {arity scope : Nat} (spine : Fin arity → Fin scope) (target : Fin scope) :
    (count : Nat) → count ≤ arity → Option (Fin arity)
  | 0, _ => none
  | count + 1, hbound =>
      if (spine ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) hbound⟩).val = target.val then
        some ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) hbound⟩
      else
        findPreimageBelow spine target count (Nat.le_of_succ_le hbound)

/-- The **inversion substitution** `ρ⁻¹`: the partial left inverse of a spine renaming, searching the whole
domain. -/
def spineInverse {arity scope : Nat} (spine : Fin arity → Fin scope) (target : Fin scope) :
    Option (Fin arity) :=
  findPreimageBelow spine target arity (Nat.le_refl arity)

/-- The search is SOUND: any preimage it returns genuinely maps to the target (so substituting via `ρ⁻¹`
introduces no spurious binding). -/
theorem findPreimageBelow_sound {arity scope : Nat} (spine : Fin arity → Fin scope) (target : Fin scope) :
    (count : Nat) → (hbound : count ≤ arity) → (preimage : Fin arity) →
      findPreimageBelow spine target count hbound = some preimage → spine preimage = target
  | 0, _, _, hsome => by simp only [findPreimageBelow] at hsome; nomatch hsome
  | count + 1, hbound, preimage, hsome => by
      simp only [findPreimageBelow] at hsome
      split at hsome
      case isTrue hcond =>
        have candidateEqPreimage :
            (⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) hbound⟩ : Fin arity) = preimage :=
          Option.some.inj hsome
        rw [← candidateEqPreimage]
        exact Fin.eq_of_val_eq hcond
      case isFalse _ =>
        exact findPreimageBelow_sound spine target count (Nat.le_of_succ_le hbound) preimage hsome

/-- The search FINDS an existing preimage: if `target = spine probe` and the bound reaches `probe`, the
search returns `probe` — injectivity guarantees it is the unique match. -/
theorem findPreimageBelow_finds {arity scope : Nat} (spine : Fin arity → Fin scope)
    (spineInjective : Function.Injective spine) (probe : Fin arity) :
    (count : Nat) → (hbound : count ≤ arity) → probe.val < count →
      findPreimageBelow spine (spine probe) count hbound = some probe
  | 0, _, probeBelowZero => absurd probeBelowZero (Nat.not_lt_zero probe.val)
  | count + 1, hbound, probeBelowSucc => by
      simp only [findPreimageBelow]
      split
      case isTrue hcond =>
        exact congrArg some (spineInjective (Fin.eq_of_val_eq hcond))
      case isFalse hcond =>
        have probeNeCount : probe.val ≠ count := by
          intro probeEqCount
          have candidateEqProbe :
              (⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) hbound⟩ : Fin arity) = probe :=
            Fin.eq_of_val_eq (Eq.symm probeEqCount)
          exact hcond (congrArg (fun index => (spine index).val) candidateEqProbe)
        exact findPreimageBelow_finds spine spineInjective probe count (Nat.le_of_succ_le hbound)
          (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ probeBelowSucc) probeNeCount)

/-- The inverse only ever returns a genuine preimage — `ρ⁻¹` introduces no spurious binding. -/
theorem spineInverse_sound {arity scope : Nat} (spine : Fin arity → Fin scope) (target : Fin scope)
    (preimage : Fin arity) (inverted : spineInverse spine target = some preimage) :
    spine preimage = target :=
  findPreimageBelow_sound spine target arity (Nat.le_refl arity) preimage inverted

/-- ★ **The inversion round-trip `ρ⁻¹ ∘ ρ = id`**: for an injective (pattern) spine, inverting an applied
variable recovers it.  This is the existence/solve side of flex-rigid pattern unification — the inverse
substitution that produces the metavariable's value. -/
theorem spineInverse_inverts {arity scope : Nat} (spine : Fin arity → Fin scope)
    (spineInjective : Function.Injective spine) (probe : Fin arity) :
    spineInverse spine (spine probe) = some probe :=
  findPreimageBelow_finds spine spineInjective probe arity (Nat.le_refl arity) probe.isLt

/-! ## A concrete pattern spine -/

/-- A concrete injective spine `Fin 2 → Fin 3` (the shift `0 ↦ 1`, `1 ↦ 2` — a genuine renaming of two
distinct variables). -/
def exampleSpine : RawRenaming 2 3 :=
  fun position => ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩

/-- The example spine is a pattern (its variables are distinct). -/
theorem exampleSpine_isPattern : IsPatternSpine exampleSpine := by
  intro leftIndex rightIndex spineEqual
  exact Fin.eq_of_val_eq (Nat.succ.inj (congrArg Fin.val spineEqual))

/-- ★ The inversion round-trips on the concrete spine: every applied variable is recovered. -/
theorem exampleInversion_roundTrips (index : Fin 2) :
    spineInverse exampleSpine (exampleSpine index) = some index :=
  spineInverse_inverts exampleSpine exampleSpine_isPattern index

end FX1Poly.Core
