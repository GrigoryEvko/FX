/-! # FX1Poly/Modal/VersionCategoryDimension — the VERSION dimension as the first CATEGORY-structured dimension

The dimension-classification track (`DIM-CLASS-*`) has now spanned the order-theoretic structural classes:
ordered semirings (usage / security / complexity), bounded join-semilattices (effect / trust / clock /
provenance), the partial PCM (fractional permission), total-order chains (mutation), the M3 diamond
(overflow), the infinite lattice M_omega (provenance), and the bare preorder (lifetime).  Every one of
those is POSET-LIKE: the dimension's algebra is a relation `≤` (or operations) ON the grades, carrying no
data BETWEEN distinct grades.

The Version dimension (§1.1 "Evolution"; §6.3 "Tier V — lattice of version labels with adapter edges,
checked via `refines` / `migration`"; §15) is structurally DIFFERENT, and this file pins that difference:
its algebra is a genuine **category**.  The objects are version labels; the morphisms are the §15
adapter/migration edges — TOTAL transformations of the version data (§14.2 proves each migration total).
Migrations COMPOSE (the §15 multi-version upgrade), with an identity migration and the category laws.
This morphism data is exactly what the order-only dimensions lack: between two versions there can be MANY
adapters, and they compose — version is the first dimension whose grades are connected by composable
morphisms rather than a bare order.

  * **`VersionData`** — version-N data: a record with N `Nat` fields (each version adds one field on the
    front), the concrete carrier the adapters transform.
  * **`Migration` / `Migration.identity` / `Migration.compose`** — the adapter edges as total functions,
    the identity, and composition; the **category laws** (`identity_compose`, `compose_identity`,
    `compose_assoc`) hold by `rfl` (function composition).
  * **`migrateAddField` + the `migrateUserV1toV2 / V2toV3 / V1toV3` chain** — the §14.1 `UserApi`
    v1 → v2 → v3 example: each adapter adds one field with a default (`add F default D`, §14.2), and the
    composite adapter fills BOTH new fields (`migrateUserV1toV3_apply`).
  * **`Refines` (+ `refl` / `trans`)** — `refines` is the reachability PREORDER the migration category
    induces: reflexive via the identity migration, transitive via composition (§1.1).
    `userApiV3_refines_v1` is the concrete `v3 ⊒ v1` along the chain.
  * **`migrateDropField` + `migrateDropField_addField`** — `add F` / `remove F` (§14.2) are a RETRACTION
    pair: dropping a freshly-added field round-trips, so every forward adapter is a split monomorphism.
  * **`migrateAddField_injective_inDefault`** — two adapters `1 → 2` with different defaults are DISTINCT
    morphisms: the hom-sets are proof-relevant, so this is a GENUINE (non-thin) category, not a preorder
    in disguise — the structural novelty over every prior poset/lattice dimension.

**Honest scope.**  This models the migration CATEGORY (composition structure).  Semantic backward
INcompatibility (§14.1 `v3 -> v1 : not_compatible`) is a SEPARATE layer — a `compatibility` predicate
over adapters, not modeled here; in the pure-function model a backward adapter exists (field-drop), so
directedness is about contract preservation, not morphism existence.

## Zero-axiom verification

`VersionData` is type-valued structural recursion on the version number (no `Fin`, no `List` — avoiding
their `propext` landmines); the migrations are plain functions with composition `g ∘ f`, so the category
laws are `rfl`; `Refines` is `Nonempty` of a migration with `refl`/`trans` by identity/composition; the
non-thinness is `congrFun` + `injection` + `Nat` `decide`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (every declaration probed with `#print axioms` before landing).
Per-declaration audit-gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Version-N data: a record with N natural-number fields (each version adds one field on the front).
`VersionData 1 = Nat × Unit`, `VersionData 3 = Nat × Nat × Nat × Unit`. -/
def VersionData : Nat → Type
  | 0 => Unit
  | n + 1 => Nat × VersionData n

/-- A migration (the §15 adapter edge) from version `sourceVersion` to version `targetVersion`: a TOTAL
transformation of the version data (§14.2 proves each migration total — a Lean function IS total). -/
def Migration (sourceVersion targetVersion : Nat) : Type :=
  VersionData sourceVersion → VersionData targetVersion

/-- The identity migration: a version migrates to itself unchanged (the category's identity morphism). -/
def Migration.identity (version : Nat) : Migration version version := id

/-- Composition of migrations: migrate `a → b` then `b → c` (the category's composition). -/
def Migration.compose {a b c : Nat} (first : Migration a b) (second : Migration b c) :
    Migration a c := fun data => second (first data)

/-! ## The CATEGORY laws — what makes version composition-structured, not a bare poset -/

/-- Left identity: composing with the identity migration on the left changes nothing. -/
theorem Migration.identity_compose {a b : Nat} (migration : Migration a b) :
    Migration.compose (Migration.identity a) migration = migration := rfl

/-- Right identity: composing with the identity migration on the right changes nothing. -/
theorem Migration.compose_identity {a b : Nat} (migration : Migration a b) :
    Migration.compose migration (Migration.identity b) = migration := rfl

/-- Associativity of migration composition (the §15 multi-version upgrade is path-independent). -/
theorem Migration.compose_assoc {a b c d : Nat}
    (first : Migration a b) (second : Migration b c) (third : Migration c d) :
    Migration.compose (Migration.compose first second) third =
      Migration.compose first (Migration.compose second third) := rfl

/-! ## Concrete adapters — the §14.1 UserApi v1 → v2 → v3 chain -/

/-- The forward adapter version `n → n+1`: add one field with a default value (§14.2 `add F default D`). -/
def migrateAddField (defaultValue : Nat) (n : Nat) : Migration n (n + 1) :=
  fun data => (defaultValue, data)

/-- v1 → v2: add `role` with default `0`. -/
def migrateUserV1toV2 : Migration 1 2 := migrateAddField 0 1

/-- v2 → v3: add `created` with default epoch `100`. -/
def migrateUserV2toV3 : Migration 2 3 := migrateAddField 100 2

/-- v1 → v3: the composite adapter (migration paths compose, the §15 multi-version upgrade). -/
def migrateUserV1toV3 : Migration 1 3 := Migration.compose migrateUserV1toV2 migrateUserV2toV3

/-- The composite migration fills BOTH new fields with their defaults — the §14.2 multi-step upgrade
computes the same result as the path through v2. -/
theorem migrateUserV1toV3_apply (idField : Nat) :
    migrateUserV1toV3 (idField, ()) = (100, 0, idField, ()) := rfl

/-! ## `refines` is the reachability PREORDER induced by the migration category (§1.1) -/

/-- `laterVersion` refines `earlierVersion` iff there is an adapter migrating the earlier data forward. -/
def Refines (laterVersion earlierVersion : Nat) : Prop :=
  Nonempty (Migration earlierVersion laterVersion)

/-- Reflexivity of `refines` — via the identity migration. -/
theorem Refines.refl (version : Nat) : Refines version version :=
  ⟨Migration.identity version⟩

/-- Transitivity of `refines` — via migration composition.  Reflexive + transitive ⟹ `refines` is the
preorder the migration category generates by reachability. -/
theorem Refines.trans {a b c : Nat} (refinesEarlier : Refines b a) (refinesLater : Refines c b) :
    Refines c a := by
  obtain ⟨adapterEarlier⟩ := refinesEarlier
  obtain ⟨adapterLater⟩ := refinesLater
  exact ⟨Migration.compose adapterEarlier adapterLater⟩

/-- The UserApi version chain `v3 ⊒ v1`: version 3 refines version 1 via the composite adapter. -/
theorem userApiV3_refines_v1 : Refines 3 1 := ⟨migrateUserV1toV3⟩

/-! ## Add/remove are a retraction pair (§14.2): every forward adapter is a SPLIT MONO -/

/-- The backward adapter version `n+1 → n`: drop the most-recently-added field (§14.2 `remove F`). -/
def migrateDropField (n : Nat) : Migration (n + 1) n := fun fields => fields.2

/-- Dropping a freshly-added field is the identity — `add F default; remove F` round-trips, so every
forward `migrateAddField` is a split monomorphism (the field-drop is its retraction).  The §14.2
`add`/`remove` operations are a retraction pair in the migration category. -/
theorem migrateDropField_addField (defaultValue : Nat) (n : Nat) :
    Migration.compose (migrateAddField defaultValue n) (migrateDropField n) =
      Migration.identity n := rfl

/-! ## Non-thinness: the hom-sets carry DATA (≥2 distinct adapters) — a GENUINE category -/

/-- Two adapters `1 → 2` with different defaults are DISTINCT morphisms: the migration hom-set is
proof-relevant.  This is what distinguishes the version dimension (a real category) from the order-only
dimensions (usage / security / mutation / lifetime / …), whose `≤` carries no morphism data. -/
theorem migrateAddField_injective_inDefault :
    migrateAddField 0 1 ≠ migrateAddField 5 1 := by
  intro adaptersEqual
  have appliedEqual := congrFun adaptersEqual (7, ())
  injection appliedEqual with headEqual _
  exact absurd headEqual (by decide)

end FX1Poly.Modal
