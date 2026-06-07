import FX1Poly.Tier0.FxBaseRenamingVecCategory

/-! # FX1Poly/Tier0/FxBaseRenamingVecTabulate
    — the reification ≅ function-space bijection + decidable equality for `RenamingVec`

`FxBaseRenamingVecCategory.lean` reified a renaming as the product-recursive `RenamingVec target source` and gave
`lookup : RenamingVec target source → (Fin source → Fin target)`.  This file supplies the CONSTRUCTIVE companion
`tabulate` (build a `RenamingVec` from an image function) and shows `tabulate`/`lookup` are mutually inverse — so
`RenamingVec target source` IS the function space `Fin source → Fin target`, reified as inspectable data.  It also
ships a structural, zero-axiom `DecidableEq (RenamingVec target source)`.

These are the foundational substrate for the finite-bijectivity iso-decider (SN-085a, #914): the candidate inverse
of an iso renaming is `tabulate` of its preimage function, and the two round-trip checks are `RenamingVec`
equalities decided by the `DecidableEq` instance.  They are also generally useful (the constructive reification +
decidable equality the eventual CwR pipeline over the Vec base will want).

## What lands here (all zero-axiom)

  * `RenamingVec.tabulate` — build a `RenamingVec target length` from an image function `Fin length → Fin target`,
    by recursion on `length` into the product structure.
  * `RenamingVec.tabulate_lookup` — `lookup ∘ tabulate = id` pointwise: `(tabulate f).lookup i = f i`.
  * `RenamingVec.tabulate_lookup_self` — `tabulate ∘ lookup = id`: `tabulate vec.lookup = vec`, via `ext`.  With
    `tabulate_lookup` this exhibits `RenamingVec target source ≅ (Fin source → Fin target)`.
  * `RenamingVec.decEq` + `instDecidableEqRenamingVec` — structural decidable equality: recursion on `source`,
    `PUnit` proof-irrelevance at the base, head decided by `Nat.decEq` on the `Fin` value (via `Fin.eq_of_val_eq`,
    dodging any `Fin.decEq` propext risk) and tail recursively.

## Zero-axiom verification

`tabulate` is structural recursion on `length`; `tabulate_lookup` matches the index `⟨0,_⟩`/`⟨_+1,_⟩` directly
(no `Fin.cases`), the successor case closing by `rw [tabulate_lookup]` + `Fin` proof-irrelevance; `tabulate_
lookup_self` goes through the shipped `RenamingVec.ext`.  `decEq` decides the head via `Nat.decEq` on `.val` and
lifts with `Fin.eq_of_val_eq` + `Prod.ext`, refuting via `congrArg`.  No `funext`, no `Fin.decEq`/`Fin.cases`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- **Build a `RenamingVec` from its image function** — the constructive companion to `lookup`, by recursion on
the length into the product structure. -/
def RenamingVec.tabulate {target : Nat} :
    {length : Nat} → (Fin length → Fin target) → RenamingVec target length
  | 0, _imageOf => PUnit.unit
  | _length + 1, imageOf =>
      (imageOf ⟨0, Nat.succ_pos _⟩,
        RenamingVec.tabulate (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩))

/-- `lookup ∘ tabulate = id` (pointwise): tabulating an image function then looking up recovers it. -/
theorem RenamingVec.tabulate_lookup {target : Nat} :
    {length : Nat} → (imageOf : Fin length → Fin target) → (index : Fin length) →
      (RenamingVec.tabulate imageOf).lookup index = imageOf index
  | 0, _imageOf, index => index.elim0
  | _length + 1, _imageOf, ⟨0, _⟩ => rfl
  | _length + 1, imageOf, ⟨position + 1, isLt⟩ => by
      show (RenamingVec.tabulate
          (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩)).lookup
            ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ = imageOf ⟨position + 1, isLt⟩
      rw [tabulate_lookup]

/-- `tabulate ∘ lookup = id` (on vectors), via `ext`.  With `tabulate_lookup` this exhibits the reification
`RenamingVec target source ≅ (Fin source → Fin target)` as a `tabulate`/`lookup` bijection. -/
theorem RenamingVec.tabulate_lookup_self {target source : Nat} (vec : RenamingVec target source) :
    RenamingVec.tabulate vec.lookup = vec :=
  RenamingVec.ext _ _ (fun index => RenamingVec.tabulate_lookup vec.lookup index)

/-- **Structural decidable equality** for `RenamingVec`.  Recursion on `source`: `PUnit` proof-irrelevance at the
base; at a successor, decide the head via `Nat.decEq` on the `Fin` value (lifted by `Fin.eq_of_val_eq`, avoiding
any `Fin.decEq`/`Fin.cases` propext leak) and the tail recursively, refuting through `congrArg`. -/
def RenamingVec.decEq {target : Nat} :
    {source : Nat} → (vecA vecB : RenamingVec target source) → Decidable (vecA = vecB)
  | 0, PUnit.unit, PUnit.unit => isTrue rfl
  | _source + 1, vecA, vecB =>
      match Nat.decEq vecA.1.val vecB.1.val with
      | isFalse headValDiffers => isFalse (fun vecsEqual =>
          headValDiffers (congrArg (fun pair => Fin.val (Prod.fst pair)) vecsEqual))
      | isTrue headValEqual =>
          match RenamingVec.decEq vecA.2 vecB.2 with
          | isFalse tailDiffers => isFalse (fun vecsEqual => tailDiffers (congrArg Prod.snd vecsEqual))
          | isTrue tailEqual => isTrue (Prod.ext (Fin.eq_of_val_eq headValEqual) tailEqual)

/-- The decidable-equality instance for `RenamingVec`, delegating to the structural `decEq`. -/
instance instDecidableEqRenamingVec {target source : Nat} :
    DecidableEq (RenamingVec target source) := RenamingVec.decEq

end FX1Poly.Tier0
