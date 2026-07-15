import FX1Poly.Axis.Context.ContextDefinitionalUnivalence

/-! # context-32 — the STRUCTURE IDENTITY PRINCIPLE for contexts + observational substitution

`context-32` is the L4 context-univalence SIP rung — the SYMMETRIC-univalence complement of the DIRECTED
line (`context-34`..`context-37`).  It ships the **structure identity principle** (SIP) at the context
category: TRANSPORT OF STRUCTURE along a context-equivalence, plus OBSERVATIONAL SUBSTITUTION (the
action-on-observations characterization).  It is the context-level mirror of the TYPE-axis `type-8`
(the structure identity principle, transport of structure along an equivalence), and is built DIRECTLY on
the `context-30`/`context-31` univalent universe object — the funext-free, symmetric `CategoryIso` and the
`Id_U ↝ Equiv` reduction.

## The SIP, and why the funext-free fragment is zero-axiom

The structure identity principle (Coquand; Escardó; Aczel) says ISOMORPHIC STRUCTURES ARE EQUAL: an
equivalence between two carriers transports any structure (a group law, an order, a typing verdict) from one
to the other, and isomorphic structures satisfy the same properties.  The FULL homotopy SIP — transport along
a HOMOTOPY equivalence with structure-preservation up to higher coherence — rests on the univalence axiom
`UA`, which entails function extensionality (Voevodsky); that is the `×type` / type-axis wall the cubical and
groupoid context models defer (`fxContextUniverse_hasUnivalenceAxiom = false`).

`context-32` ships the funext-free fragment, exactly as `context-30` ships categorical (not homotopy)
univalence.  The equivalence is `context-30`'s `CategoryIso` (inverses up to EQUALITY), whose univalence
datum `IsUnivalentUniverseObject` supplies `isoToId : (A ≅ B) → (A = B)`.  Transport of structure along the
iso is then `Eq.rec` along that recovered path — no funext, no `Quot.sound`.  Read at the set-level
(discrete) universe object, every iso IS an identity, so SIP holds with genuine zero-axiom content
(`discreteUniverseObject_isUnivalent`, `context-30`).

## What lands here (all zero-axiom)

  * **`transportStructureAlongContextIso`** — ★ the SIP transport: an element of a structure family on
    `objectA`, carried to `objectB` along a categorical iso `objectA ≅ objectB`, by `Eq.rec` along the
    univalent universe's `isoToId` (explicit motive; no funext).
  * **`isoToId_identityIso`** + **`transportStructureAlongContextIso_identityIso`** — SIP REFLEXIVITY: the
    univalence datum sends the identity iso to `rfl` (forced by the two round-trips), so transport along the
    identity iso is the identity.  The coherence certifying this is genuine transport.
  * **`discreteUniverseObject_isoImpliesObjectEqual`** — ★ the SIP statement PROVEN at the discrete witness:
    isomorphic objects of the set-level context universe ARE EQUAL — so they carry identical structure.
  * **`discreteUniverseObject_transportStructure`** — SIP transport specialised to the zero-axiom discrete
    witness.
  * **`ContextObservation`** + **`contextIso_observationallyIndistinguishable`** — OBSERVATIONAL SUBSTITUTION
    (set-level): a categorical iso identifies the value of EVERY observation (a query into a result type) on
    its two endpoints — iso-contexts are observationally indistinguishable, by `congrArg` along `isoToId`.
  * **`definitionalUnivalence_observationsAgree`** — observational substitution realized BY COMPUTATION
    (bridge to `context-31`): any normalization-invariant observation cannot distinguish `Id_U(A, B)` from
    `Equiv(A, B)`, since the `Id_U ↝ Equiv` reduction equates their normal forms.

## What is deferred (the honest wall)

  * The FULL HOMOTOPY SIP — transport along a HOMOTOPY equivalence, structure-preservation up to higher
    coherence — rests on the univalence axiom and so needs `funext` / `Quot.sound`, the `×type` / type-axis
    wall (`fxContextStructureIdentity_hasFullHomotopySIP = false`).
  * The SIP transport here is the SELF-CONTAINED Axis analog, NOT a Core `StepOverTable` iota row
    (`fxContextStructureIdentity_isOverCoreIotaTable = false`).

Imports only `ContextDefinitionalUnivalence` (its `context-31` sibling, which re-exports `context-30`).  A
Axis design-lock must not import up into `Core/` / `Typed/`.  Zero external dependencies — raw Lean 4 +
Init only.

Reference: the `type-8` structure identity principle (type axis); Coquand–Danielsson, "Isomorphism is
equality"; Escardó's SIP; Cavallo & Höfer, "Univalence without function extensionality", MFPS 2026,
arXiv:2605.00812; the `context-30`/`context-31` univalent universe object.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## Transport of structure along a context iso (the SIP transport) -/

/-- ★ **The SIP transport.**  Given the categorical-univalence datum on a wild category (= a universe object
of the context category) and a categorical iso `objectA ≅ objectB`, carry an element of a STRUCTURE FAMILY
on `objectA` to one on `objectB` — by `Eq.rec` along the path `isoToId iso : objectA = objectB` the
univalence datum recovers.  This is "transport of structure along a context-equivalence": isomorphic
contexts carry the same structure.  Path transport via `Eq.rec` with an EXPLICIT motive (the implicit-motive
`▸` casts the wrong occurrence) — no funext, no `Quot.sound`. -/
def transportStructureAlongContextIso {category : RawCategory}
    (univalence : IsUnivalentUniverseObject category)
    {structureFamily : category.Object → Type}
    {objectA objectB : category.Object}
    (iso : CategoryIso category objectA objectB)
    (structureElement : structureFamily objectA) : structureFamily objectB :=
  Eq.rec (motive := fun target _ => structureFamily target) structureElement
    (univalence.isoToId iso)

/-- The univalence datum sends the IDENTITY iso to `rfl`.  Forced by the round-trips: `isoToId (idToIso rfl)
= rfl` (`isoToId_idToIso`), and `idToIso rfl` IS the identity iso (definitionally, the `Eq.rec` base) — so
`isoToId (identityIso) = rfl`.  No assumption on the witness beyond being a two-sided equivalence. -/
theorem isoToId_identityIso {category : RawCategory}
    (univalence : IsUnivalentUniverseObject category) (object : category.Object) :
    univalence.isoToId (CategoryIso.identityIso category object) = rfl :=
  univalence.isoToId_idToIso (rfl : object = object)

/-- ★ **SIP reflexivity.**  Transport of structure along the IDENTITY iso is the identity — the coherence
certifying `transportStructureAlongContextIso` is genuine path transport.  Reduces to `isoToId_identityIso`
(the identity iso's recovered path is `rfl`, along which `Eq.rec` is the identity). -/
theorem transportStructureAlongContextIso_identityIso {category : RawCategory}
    (univalence : IsUnivalentUniverseObject category)
    {structureFamily : category.Object → Type} {object : category.Object}
    (structureElement : structureFamily object) :
    transportStructureAlongContextIso univalence
        (CategoryIso.identityIso category object) structureElement
      = structureElement := by
  show Eq.rec (motive := fun target _ => structureFamily target) structureElement
      (univalence.isoToId (CategoryIso.identityIso category object)) = structureElement
  rw [isoToId_identityIso univalence object]

/-! ## SIP at the discrete (set-level) witness -/

/-- ★ **The structure identity principle PROVEN at the discrete witness.**  In the set-level context universe
object, every categorical iso is the image of an equality (`Morphism a b = PLift (a = b)`), so isomorphic
objects ARE EQUAL — and therefore carry IDENTICAL structure.  This is the zero-axiom SIP content: "iso-contexts
have equal structure", with no funext, no `Quot.sound`. -/
theorem discreteUniverseObject_isoImpliesObjectEqual {carrier : Type} {objectA objectB : carrier}
    (iso : CategoryIso (discreteUniverseObject carrier) objectA objectB) : objectA = objectB :=
  (discreteUniverseObject_isUnivalent carrier).isoToId iso

/-- The SIP transport specialised to the zero-axiom discrete witness: carry a structure along an iso of
set-level context objects. -/
def discreteUniverseObject_transportStructure {carrier : Type}
    {structureFamily : carrier → Type} {objectA objectB : carrier}
    (iso : CategoryIso (discreteUniverseObject carrier) objectA objectB)
    (structureElement : structureFamily objectA) : structureFamily objectB :=
  transportStructureAlongContextIso (discreteUniverseObject_isUnivalent carrier) iso structureElement

/-! ## Observational substitution (the action on observations) -/

/-- An **observation** on the objects of the context category: a query returning a value in a result type
for each context (a field projection, a length, a typing verdict).  Observational substitution is the action
of a context-equivalence on these. -/
abbrev ContextObservation (category : RawCategory) (Result : Type) := category.Object → Result

/-- ★ **Observational substitution (set-level).**  A categorical iso `objectA ≅ objectB` IDENTIFIES the value
of EVERY observation on its two endpoints — `observation objectA = observation objectB` — because the iso
yields a path `objectA = objectB` (`isoToId`) along which the observation is constant (`congrArg`).  This is
the action-on-observations characterization: iso-contexts are OBSERVATIONALLY INDISTINGUISHABLE.  Funext-free. -/
theorem contextIso_observationallyIndistinguishable {category : RawCategory}
    (univalence : IsUnivalentUniverseObject category) {Result : Type}
    (observation : ContextObservation category Result)
    {objectA objectB : category.Object} (iso : CategoryIso category objectA objectB) :
    observation objectA = observation objectB :=
  congrArg observation (univalence.isoToId iso)

/-- ★ **Observational substitution BY COMPUTATION** (bridge to `context-31`).  Any observation that is
INVARIANT under normalization cannot distinguish `Id_U(A, B)` from `Equiv(A, B)` — because the `Id_U ↝ Equiv`
reduction (`context-31`) equates their normal forms (`idOverUniverseObject_normalize_eq`).  So the
context-level definitional univalence realizes observational substitution operationally: the identity and
equivalence formers are observationally the same. -/
theorem definitionalUnivalence_observationsAgree {Result : Type}
    (observation : ContextUnivCode → Result)
    (observationRespectsNormalize : ∀ code, observation code = observation code.normalize)
    (codeLeft codeRight : ContextUnivCode) :
    observation (.idForm .universeObj codeLeft codeRight)
      = observation (.equivForm codeLeft codeRight) := by
  rw [observationRespectsNormalize (.idForm .universeObj codeLeft codeRight),
      observationRespectsNormalize (.equivForm codeLeft codeRight),
      ContextUnivCode.idOverUniverseObject_normalize_eq]

/-! ## Honesty markers -/

/-- **Honesty marker.**  The STRUCTURE IDENTITY PRINCIPLE for contexts is shipped at the funext-free /
discrete level: transport of structure along a categorical iso (`transportStructureAlongContextIso`), its
reflexivity coherence (`transportStructureAlongContextIso_identityIso`), and the SIP statement proven at the
set-level witness (`discreteUniverseObject_isoImpliesObjectEqual`: iso-contexts are equal, hence carry equal
structure).  The context-level mirror of the `type-8` SIP.  `= true`. -/
def fxContextStructureIdentity_hasStructureIdentityPrinciple : Bool := true

/-- **Honesty marker.**  OBSERVATIONAL SUBSTITUTION (set-level) is shipped: a categorical iso identifies the
value of every observation on its endpoints (`contextIso_observationallyIndistinguishable`), realized BY
COMPUTATION via the `context-31` `Id_U ↝ Equiv` reduction (`definitionalUnivalence_observationsAgree`).
`= true`. -/
def fxContextStructureIdentity_hasObservationalSubstitution : Bool := true

/-- **Honesty marker.**  The FULL HOMOTOPY SIP — transport along a HOMOTOPY equivalence with
structure-preservation up to higher coherence — rests on the univalence axiom `UA`, which entails function
extensionality (Voevodsky); that needs `funext` / `Quot.sound`, the `×type` / type-axis wall the cubical and
groupoid context models also defer.  `= false`. -/
def fxContextStructureIdentity_hasFullHomotopySIP : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis analog of a Core table-native SIP row; a Axis
design-lock cannot import the Core engine, so the transport and observational substitution are re-shipped
here over the `context-30`/`context-31` universe object.  Gluing the Axis and Core forms is cross-axis
`×type`.  `= false`. -/
def fxContextStructureIdentity_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: at the discrete witness, transport of structure along the identity iso is the identity — SIP
reflexivity, concrete at the set-level context universe object. -/
theorem discreteUniverseObject_transportStructure_identity_smoke {carrier : Type}
    {structureFamily : carrier → Type} {object : carrier} (structureElement : structureFamily object) :
    discreteUniverseObject_transportStructure
        (CategoryIso.identityIso (discreteUniverseObject carrier) object) structureElement
      = structureElement :=
  transportStructureAlongContextIso_identityIso (discreteUniverseObject_isUnivalent carrier) structureElement

/-- Smoke: at the discrete witness, an iso identifies the value of any observation on its endpoints — the
concrete observational-substitution content at a set-level context. -/
theorem discreteUniverseObject_observation_smoke {carrier : Type} {Result : Type}
    (observation : ContextObservation (discreteUniverseObject carrier) Result)
    {objectA objectB : carrier}
    (iso : CategoryIso (discreteUniverseObject carrier) objectA objectB) :
    observation objectA = observation objectB :=
  contextIso_observationallyIndistinguishable (discreteUniverseObject_isUnivalent carrier) observation iso

end FX1Poly.Axis
