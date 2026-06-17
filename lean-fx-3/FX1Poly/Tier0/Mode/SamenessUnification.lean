import FX1Poly.Tier0.Mode.MultiplierStructureClass

/-! # mode-19 — SAP = SIP = SRP: nominal = univalence = parametricity (arity = multiplier)

Nominal type theory (fresh names), parametricity (relational abstraction), and univalence (the structure identity
principle) are the SAME construction at different MULTIPLIER ARITIES (Nuyts–Devriese; Cavallo–Harper "parametric
quantifiers").  The sharp, decidable core: each is governed by a `mode-2` MULTIPLIER, and the distinction is
exactly REFLEXIVITY = the multiplier's DIAGONAL (`supportsDiagonal`):

  * **nominal** (SAP) — the affine arity; freshness is APARTNESS (irreflexive — NO diagonal);
  * **parametricity** (SRP) — the affine arity; a BRIDGE / binary relation (need not be reflexive — no diagonal);
  * **univalence** (SIP) — the cartesian arity; a PATH / reflexive relation (the diagonal IS reflexivity).

A path is a BRIDGE with a degeneracy; univalence is the FINEST reflexive parametricity.  `mode-19` ships the
arity↔multiplier classification, the shared binary "sameness" machinery (parametricity, with univalence its
reflexive instance), the abstraction-theorem category (`Respects`), and the SIP transport, all funext-free.

## What this file ships (each piece zero-axiom)

  * **`SamenessArity`** (`nominal` / `parametric` / `univalent`) + `multiplierClass` (→ `mode-2` affine / affine /
    cartesian) + `hasReflexivity` + ★ `samenessArity_reflexivity_eq_diagonal` (reflexivity = `supportsDiagonal`
    — the "arity = multiplier" identity).
  * **`Sameness`** (a binary relatedness) + `identitySameness` (univalence's `Eq`) / `relationalSameness`
    (parametricity's) + ★ `identity_is_relational_at_Eq` (univalence = parametricity at `Eq`) + the reflexivity
    classification + ★ `identity_finest_reflexive` (univalence = the finest reflexive sameness).
  * **`Respects`** (the abstraction theorem) — the category `id_respects` / `comp_respects`, with
    `identity_respects` (SIP transport / congruence) and `const_respects_of_reflexive`.
  * **`freshness`** + `freshness_irreflexive` — the nominal (affine) apartness, its irreflexivity = no diagonal.

## What is DEFERRED (markers)

  * the genuine TRANSPENSION-arity unification — `Ξ` (`mode-11`) at each multiplier realizing SAP / SIP / SRP via
    the presheaf-over-multiplier construction (`hasTranspensionArityUnification`);
  * the PROOF-RELEVANT sameness (`Type`-valued paths / bridges, not the `Prop` shadow here)
    (`hasProofRelevantSameness`);
  * arities beyond {1, 2} — n-ary relations / higher parametricity (`hasNAryArity`);
  * the kernel's `Id` / bridge / fresh formers unified (cross-axis, `fib`) (`hasKernelSamenessConnection`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The arity ↔ multiplier classification -/

/-- The three SAMENESS principles, classified by their arity / multiplier: nominal (SAP), parametric (SRP),
univalent (SIP). -/
inductive SamenessArity where
  /-- Nominal freshness — the affine arity (apartness, irreflexive). -/
  | nominal
  /-- Parametricity — the affine arity (a bridge / binary relation, need not be reflexive). -/
  | parametric
  /-- Univalence — the cartesian arity (a path / reflexive relation; the diagonal is reflexivity). -/
  | univalent
  deriving DecidableEq

/-- ★ The MULTIPLIER (`mode-2` structure class) governing each principle: nominal and parametricity are AFFINE
(no diagonal — bridges); univalence is CARTESIAN (has the diagonal — paths).  This is "arity = multiplier". -/
def SamenessArity.multiplierClass : SamenessArity → MultiplierStructureClass
  | .nominal => .affine
  | .parametric => .affine
  | .univalent => .cartesian

/-- Whether the principle's relatedness is REFLEXIVE — `false` for nominal / parametric, `true` for univalent. -/
def SamenessArity.hasReflexivity : SamenessArity → Bool
  | .nominal => false
  | .parametric => false
  | .univalent => true

/-- ★ **The unification identity** — a sameness principle is REFLEXIVE exactly when its multiplier has the
DIAGONAL (`mode-2` `supportsDiagonal`).  Reflexivity (paths vs bridges, univalence vs parametricity) IS the
multiplier's diagonal: "arity = multiplier". -/
theorem samenessArity_reflexivity_eq_diagonal (arity : SamenessArity) :
    arity.hasReflexivity = arity.multiplierClass.supportsDiagonal := by
  cases arity <;> rfl

/-! ## The shared binary "sameness" machinery -/

/-- A **sameness** on a type — a binary RELATEDNESS (a relation).  Univalence instantiates it at `Eq` (paths),
parametricity at an arbitrary relation (bridges); they share this structure. -/
structure Sameness (Carrier : Type) where
  /-- The relatedness relation. -/
  related : Carrier → Carrier → Prop

/-- The **identity sameness** — univalence's, `related = Eq` (paths). -/
def identitySameness (Carrier : Type) : Sameness Carrier where
  related := Eq

/-- A **relational sameness** — parametricity's, an arbitrary binary relation (a bridge). -/
def relationalSameness {Carrier : Type} (relation : Carrier → Carrier → Prop) : Sameness Carrier where
  related := relation

/-- ★ **Univalence IS parametricity at `Eq`** — the identity sameness is the relational sameness instantiated at
the equality relation.  The two principles are one construction; univalence is the `Eq`-instance. -/
theorem identity_is_relational_at_Eq (Carrier : Type) :
    identitySameness Carrier = relationalSameness (Eq : Carrier → Carrier → Prop) := rfl

/-- A sameness is **reflexive** when everything is related to itself (the diagonal / a degeneracy). -/
def Sameness.IsReflexive {Carrier : Type} (sameness : Sameness Carrier) : Prop :=
  ∀ point, sameness.related point point

/-- The identity sameness (univalence) IS reflexive — paths have the diagonal `refl`. -/
theorem identitySameness_reflexive (Carrier : Type) : (identitySameness Carrier).IsReflexive :=
  fun _point => rfl

/-- ★ A parametric sameness need NOT be reflexive — the empty relation is a valid bridge but has no diagonal, so
parametricity is strictly more general than univalence. -/
theorem relational_not_reflexive :
    ¬ (relationalSameness (fun _ _ : Bool => False)).IsReflexive :=
  fun reflexive => reflexive true

/-- ★ **Univalence is the FINEST reflexive sameness** — the identity relation is contained in EVERY reflexive
sameness (a `refl` transports into any reflexive relation).  Paths are the initial / finest bridges-with-a-
diagonal: the precise sense in which univalence sits inside reflexive parametricity. -/
theorem identity_finest_reflexive {Carrier : Type} (sameness : Sameness Carrier)
    (reflexive : sameness.IsReflexive) {first second : Carrier}
    (identified : (identitySameness Carrier).related first second) : sameness.related first second := by
  cases identified
  exact reflexive first

/-! ## The abstraction theorem (parametricity) + SIP transport -/

/-- A map **respects** two samenesses when related inputs give related outputs — the abstraction theorem shape
(parametricity) / the congruence (univalence). -/
def Respects {Source Target : Type} (sourceSameness : Sameness Source) (targetSameness : Sameness Target)
    (mapFunction : Source → Target) : Prop :=
  ∀ first second, sourceSameness.related first second →
    targetSameness.related (mapFunction first) (mapFunction second)

/-- The identity map respects any sameness (the abstraction theorem's identity). -/
theorem id_respects {Carrier : Type} (sameness : Sameness Carrier) :
    Respects sameness sameness (fun element => element) :=
  fun _first _second related => related

/-- Respecting composes (the abstraction theorem's composition) — `Respects` is a category. -/
theorem comp_respects {Source Middle Target : Type}
    {sourceSameness : Sameness Source} {middleSameness : Sameness Middle} {targetSameness : Sameness Target}
    {firstMap : Source → Middle} {secondMap : Middle → Target}
    (firstRespects : Respects sourceSameness middleSameness firstMap)
    (secondRespects : Respects middleSameness targetSameness secondMap) :
    Respects sourceSameness targetSameness (fun element => secondMap (firstMap element)) :=
  fun first second related => secondRespects _ _ (firstRespects first second related)

/-- ★ **SIP transport** — EVERY map respects the IDENTITY sameness (congruence: `a = b → f a = f b`).  This is
the structure identity principle's transport, the univalence (`Eq`) instance of the abstraction theorem. -/
theorem identity_respects {Source Target : Type} (mapFunction : Source → Target) :
    Respects (identitySameness Source) (identitySameness Target) mapFunction :=
  fun _first _second related => congrArg mapFunction related

/-- A constant map respects any source sameness into a REFLEXIVE target (a constant is trivially parametric — it
lands on the diagonal). -/
theorem const_respects_of_reflexive {Source Target : Type} {sourceSameness : Sameness Source}
    {targetSameness : Sameness Target} (reflexive : targetSameness.IsReflexive) (point : Target) :
    Respects sourceSameness targetSameness (fun _element => point) :=
  fun _first _second _related => reflexive point

/-! ## Nominal freshness (the affine, irreflexive case) -/

/-- **Freshness** — the nominal relatedness: an atom is fresh for another when it is APART (distinct).  The
affine / arity-1 principle. -/
def freshness {Atom : Type} (atom avoided : Atom) : Prop := atom ≠ avoided

/-- ★ Freshness is IRREFLEXIVE — nothing is fresh for itself.  This is the nominal "no diagonal" (the affine
multiplier lacks the diagonal), dual to univalence's reflexive paths. -/
theorem freshness_irreflexive {Atom : Type} (atom : Atom) : ¬ freshness atom atom :=
  fun apart => apart rfl

/-- Nominal sits at the AFFINE multiplier (no diagonal), like parametricity — matching `freshness`'s
irreflexivity. -/
theorem nominal_is_affine :
    SamenessArity.nominal.multiplierClass = MultiplierStructureClass.affine := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The genuine TRANSPENSION-arity unification — the universal modality `Ξ` (`mode-11`) at
EACH multiplier, realizing SAP / SIP / SRP via the presheaf-over-multiplier construction (Nuyts) — beyond the
classification + the binary shadow here, is deferred.  `= false`. -/
def fxMode_hasTranspensionArityUnification : Bool := false

/-- **Honesty marker.**  The PROOF-RELEVANT sameness — `Type`-valued paths / bridges (the genuine identification
and bridge SPACES), beyond the `Prop`-valued relatedness shadow here — is deferred.  `= false`. -/
def fxMode_hasProofRelevantSameness : Bool := false

/-- **Honesty marker.**  Arities beyond {1, 2} — n-ary relations / higher (cubical) parametricity — are deferred.
`= false`. -/
def fxMode_hasNAryArity : Bool := false

/-- **Honesty marker.**  The connection to the kernel's `gen_Id` / bridge / fresh-name formers unified under one
arity-indexed former is cross-axis (`fib`), deferred.  `= false`. -/
def fxMode_hasKernelSamenessConnection : Bool := false

end FX1Poly.Tier0
