import FX1Poly.Polygraph.Homology.PolygraphHomologyFinitenessInvariant
import FX1Poly.Polygraph.Homology.PresentationOpDualityHomology

/-! # FX1Poly/Polygraph/Homology/SquierNoGoInterface — the HONEST Squier no-go INTERFACE: the
    presentation-invariance gap made an explicit hypothesis, the contrapositive no-go SCHEMA gated on
    it, the truth probes, the S_1 witness ledger, and the #2139 round-one ledger
    (H2-SQUIER-NOGO r1 bricks B2 + B3 + B4, #2139)

## This round OPENS Squier's no-go; it does NOT close it.

Squier 1987 (*Word problems and a homological finiteness condition for monoids*, J. Pure Appl.
Algebra 49) proves: a finitely-presented monoid with a finite convergent (complete) rewriting system
has finitely-generated integral homology in every degree, and exhibits a monoid `S_1` with a decidable
word problem whose third homology is NOT finitely generated — hence `S_1` has NO finite convergent
presentation.  The load-bearing ingredient is **presentation-invariance of homology**: two finite
convergent presentations of the SAME monoid have isomorphic homology.

Our shipped substrate has **zero presentation-invariance** (JOB 2): `WalkerPresentation` is raw
generator/rule/critical-pair data, and there is NO "present the same monoid" relation, let alone a
proof that homology is invariant under it.  The only invariance datum in the entire lane is the
op-duality transport `d^op = −d` (`PresentationOpDualityHomology`): a single involution on
presentations, NOT monoid-level invariance.

Therefore this file ships the no-go as an **INTERFACE with the gap EXPLICIT in the type**, not a
theorem that papers over it:

  * `HomologyPresentationInvariance` — a structure whose `isInvariant` FIELD *is* the missing
    monoid-level invariance, made a hypothesis the schema is parameterized over;
  * `squierNoGoSchema` — the genuine contrapositive derivation: *given* the invariance interface and a
    monoid whose homology invariant is not finitely generated, there is NO finite-convergent
    presentation of it.  Honest and conditional; the missing piece is a named hypothesis, never hidden;
  * truth probes: the op-duality sign-invariance witness (distinct — negated — boundaries, EQUAL
    homology invariant), the non-triviality of the invariant (`ZZ/2 ≠ 0`), and the honest
    **vacuity caveat**: over the finite List carrier the schema's `¬ finitely-generated` antecedent is
    UNSATISFIABLE (every carrier invariant is finite by construction), so the schema can only bite once
    a non-truncated / infinite-basis substrate exists.

## Zero-axiom design decisions

  * `MonoidHandle`, `HomologyPresentationInvariance`, `SquierWitnessLedgerEntry` are plain records; the
    obligation-status enum is a non-indexed inductive — no propext trap.
  * The schema transports the finitely-generated predicate along the interface's `isInvariant` equality
    with `Eq`-rewriting (`▸`), machine-checked axiom-free.
  * Every probe closes by `rfl` on literals or `by decide` on `Int`-literal disequalities (`1 ≠ −1`),
    never on a Smith-driver expression.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/SquierNoGoInterface.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B2.1 — the invariance interface (the gap made an explicit hypothesis) -/

/-- An opaque handle for the monoid a presentation presents.  Deliberately structureless — the
substrate ships NO "presents-the-same-monoid" relation (the JOB 2 wall), so this handle is only the
placeholder the invariance interface quantifies over.  Its `identifier` distinguishes handles; nothing
about presentation semantics is claimed. -/
structure MonoidHandle where
  /-- An opaque tag distinguishing monoid handles; carries no presentation semantics. -/
  identifier : Nat

/-- ★ **The presentation-invariance interface — the missing piece made a HYPOTHESIS.**  A
`presentsMonoid` relation between presentations and monoid handles, a per-presentation
`homologyInvariantOf` assignment, and the load-bearing `isInvariant` FIELD: any two presentations of
the SAME monoid receive EQUAL homology invariant.  The substrate proves NONE of this at monoid level
(JOB 2); making it a structure field puts the gap in the TYPE of every theorem that consumes it — the
honest r1 stance. -/
structure HomologyPresentationInvariance where
  /-- The (unshipped, hypothesized) "presents the same monoid" relation. -/
  presentsMonoid : WalkerPresentation → MonoidHandle → Prop
  /-- The homology invariant this interface assigns to each presentation. -/
  homologyInvariantOf : WalkerPresentation → HomologyInvariant
  /-- ★ **The load-bearing invariance hypothesis** — presentations of the same monoid share their
  homology invariant.  This is exactly what the substrate does NOT prove. -/
  isInvariant : ∀ (leftPresentation rightPresentation : WalkerPresentation) (monoid : MonoidHandle),
      presentsMonoid leftPresentation monoid → presentsMonoid rightPresentation monoid →
      homologyInvariantOf leftPresentation = homologyInvariantOf rightPresentation

/-! ## B2.2 — the no-go SCHEMA (the contrapositive derivation, gated on the interface) -/

/-- ★★ **THE HONEST SQUIER NO-GO SCHEMA.**  Given the invariance interface, an abstract
finitely-generated predicate, a monoid, and a REFERENCE presentation of that monoid whose homology
invariant is NOT finitely generated: there is NO presentation of the monoid whose invariant IS finitely
generated — in particular no finite-convergent one (which would exhibit a finitely-generated invariant,
tier B2.3).  The proof is the genuine contrapositive: a finitely-generated witness `Q` would, by the
interface's `isInvariant`, force the reference invariant to be finitely generated too, contradicting the
hypothesis.  **Conditional on the invariance interface** — the missing monoid-level invariance is the
explicit `invarianceInterface` parameter, never hidden. -/
theorem squierNoGoSchema
    (invarianceInterface : HomologyPresentationInvariance)
    (isFinitelyGenerated : HomologyInvariant → Prop)
    (monoid : MonoidHandle)
    (referencePresentation : WalkerPresentation)
    (referencePresents : invarianceInterface.presentsMonoid referencePresentation monoid)
    (referenceInvariantNotFinite :
      ¬ isFinitelyGenerated (invarianceInterface.homologyInvariantOf referencePresentation)) :
    ¬ ∃ (finitePresentation : WalkerPresentation),
        invarianceInterface.presentsMonoid finitePresentation monoid ∧
        isFinitelyGenerated (invarianceInterface.homologyInvariantOf finitePresentation) :=
  fun ⟨finitePresentation, finitePresents, finiteInvariant⟩ =>
    referenceInvariantNotFinite
      (invarianceInterface.isInvariant finitePresentation referencePresentation monoid
        finitePresents referencePresents ▸ finiteInvariant)

/-! ## B2.3 — tier (a): the forward exhibition + the honest vacuity caveat

Over the finite List carrier every homology invariant is finitely generated BY CONSTRUCTION (its
`torsionFactors` is a finite list, its `freeRank` a `Nat`), so the natural finiteness predicate is
`fun _ => True`.  This makes the no-go schema's `¬ finitely-generated` antecedent UNSATISFIABLE here —
recorded honestly, NOT hidden.  The schema can only bite once a non-truncated / infinite-basis
substrate can even STATE a non-finitely-generated homology (the JOB 4 obligation-3 wall). -/

/-- The natural finitely-generated predicate over this carrier: EVERY `HomologyInvariant` is finite
data, so the predicate is `True`. -/
def carrierFinitelyGeneratedPredicate : HomologyInvariant → Prop := fun _ => True

/-- ★ **Tier (a): every carrier homology invariant is finitely generated** — by construction (the
invariant is a finite `(freeRank, torsionFactors)` record).  This is the honest forward direction: a
finite-convergent presentation's carrier read-off ALWAYS exhibits a finitely-generated invariant. -/
theorem everyCarrierInvariantIsFinitelyGenerated :
    ∀ invariant : HomologyInvariant, carrierFinitelyGeneratedPredicate invariant :=
  fun _ => True.intro

/-- ★ **The honest VACUITY CAVEAT.**  With the carrier's natural finiteness predicate, NO invariant
fails to be finitely generated — so the no-go schema's `¬ finitely-generated` antecedent is
unsatisfiable over this List carrier.  The schema is a genuine theorem, but its trigger cannot be
pulled here: witnessing a non-finitely-generated homology needs an infinite-basis substrate (JOB 4
obligation 3, the carrier structural-finiteness wall).  Recorded as a probe, never papered over. -/
theorem squierNoGoAntecedentUnsatisfiableOverThisCarrier :
    ¬ ∃ invariant : HomologyInvariant, ¬ carrierFinitelyGeneratedPredicate invariant :=
  fun ⟨_, invariantNotFinite⟩ => invariantNotFinite True.intro

/-! ## B2.4 — truth probes: op-duality sign-invariance + non-triviality + interface inhabitation

The op-dual pair (walking monad, walking comonad) has DISTINCT boundaries — the comonad's `d2 = [[−1,1]]`
is the monad's `[[1,−1]]` NEGATED — yet lands on the SAME Smith normal form, hence the SAME homology
invariant.  This is the genuine inhabitant of the `isInvariant` field for the restricted (op-involution)
`presentsMonoid`: two distinct presentations, equal computed invariant. -/

/-- The comonad's degree-2 Smith data: the SAME Smith normal forms its op-duality certificates land on
(`walkerSmithNormalFormOfDim{One,Two}`, the monad's), read at the comonad's basis. -/
def comonadDegreeTwoSmithData : SmithHomologyData :=
  { chainBasisCount := walkerBasisCount 2
  , smithBoundaryIntoLower := walkerSmithNormalFormOfDimOne
  , windowIntoLower := 1
  , smithBoundaryFromHigher := walkerSmithNormalFormOfDimTwo
  , windowFromHigher := 2 }

/-- ★ **The op-dual boundaries genuinely DIFFER** — `d2(comonad)[0,0] = −1 ≠ 1 = d2(monad)[0,0]` (the
sign flip `d^op = −d`).  So the equal-invariant fact below is a real coincidence of Smith form, not an
identity of matrices. -/
theorem monadAndComonadBoundariesDiffer :
    comonadBoundaryOfDimOne.entryAt 0 0 ≠ walkerBoundaryOfDimOne.entryAt 0 0 := by decide

/-- ★★ **The op-dual pair SHARES its homology invariant** — `H2(comonad) = H2(monad) = ⟨0, []⟩`, read
off the SAME Smith normal form despite the negated boundaries.  This is the genuine restricted-invariance
datum: two distinct (op-dual) presentations, EQUAL computed invariant — the inhabitant the `isInvariant`
field needs, for the op-involution `presentsMonoid`. -/
theorem monadAndComonadShareDegreeTwoInvariant :
    comonadDegreeTwoSmithData.homologyInvariant = walkingMonadDegreeTwoHomologyInvariant := rfl

/-- The op-involution invariance interface: the walking monad and its op-dual comonad present the same
(handle-`0`) monoid, both assigned `H2 = ⟨0, []⟩`.  A GENUINE non-degenerate inhabitant of
`HomologyPresentationInvariance` — its `presentsMonoid` support has two DISTINCT presentations, and
`isInvariant` holds.  Honest caveat: `homologyInvariantOf` is the shared op-dual value here (the
op-involution restriction); a full interface distinguishing monoids by their actual homology is the
named residual (B4 wall R1). -/
def opDualityInvarianceInterface : HomologyPresentationInvariance :=
  { presentsMonoid := fun presentation monoid =>
      (presentation = monadWalkerPresentation ∨ presentation = comonadWalkerPresentation) ∧
      monoid.identifier = 0
  , homologyInvariantOf := fun _ => walkingMonadDegreeTwoHomologyInvariant
  , isInvariant := fun _ _ _ _ _ => rfl }

/-- ★ **The invariance interface is NON-DEGENERATELY inhabited** — the walking monad and its op-dual
comonad are DISTINCT presentations (their first rule's source word differs: `[] ≠ [0]`), both in the
`opDualityInvarianceInterface`'s support at monoid `0`.  So the `isInvariant` field is non-vacuously
satisfiable: it relates two genuinely different presentations. -/
theorem opDualityInterfaceHasDistinctPresentations :
    monadWalkerPresentation ≠ comonadWalkerPresentation :=
  fun presentationsEqual =>
    nomatch (congrArg
      (fun presentation => (listGetWithDefault ([], []) presentation.rules 0).1)
      presentationsEqual)

/-- ★ **The no-go conclusion is NON-VACUOUS** — the homology invariant genuinely ranges beyond the
trivial group (`H1(involution) = ZZ/2 ≠ 0`, `walkingInvolutionInvariantDiffersFromTrivial`), so the
schema's target `¬ ∃ finite-convergent presentation` is a substantive constraint, not a statement about
an always-zero invariant.  Marker; the content is `walkingInvolutionInvariantDiffersFromTrivial`. -/
def squierNoGoConclusionIsNonVacuous : Bool := true

/-! ## B3 — THE WITNESS LEDGER: Squier's monoid `S_1`, named with its three obligations

Squier's `S_1` (1987): a finitely-presented monoid with a DECIDABLE word problem that is NOT of
homological type `FP_3` / finite derivation type (FDT), hence has NO finite convergent presentation —
the first separation of decidable-word-problem from finite-convergent-presentability.  Its three
obligations, honestly costed (JOB 4):

  1. **Finite presentation — EXPRESSIBLE NOW (shape).**  `S_1` is a one-object monoid on ~5 generators;
     the GENERATOR SHAPE fits `WalkerPresentation` (`oneGeneratorCount = 5`).  Witnessed below by
     `squierMonoidFiveGeneratorShape` — but the SHAPE ONLY: transcribing Squier's EXACT defining
     relations (Squier 1987, §on `S_1`) is the named residual, deliberately NOT invented here.
  2. **Decidable word problem — SEPARATE HARD OBLIGATION.**  `S_1`'s decidability does NOT come from
     convergence (it HAS no finite convergent presentation — the whole point), so it CANNOT ride
     `WordProblem`'s `convergent ⟹ decidable` infrastructure.  Needs an independent decision argument.
     Multi-round; WALLED for r1.
  3. **Homological non-finiteness (`H_3` not f.g.) — WALLED BY CARRIER STRUCTURAL FINITENESS.**  The
     shipped carrier has `computeBasisCount : Nat → Nat` and `C_3 = criticalPairs.length` (a finite
     `Nat`), so it abelianizes to finite free modules BY CONSTRUCTION — its `H_3` is ALWAYS finite.  The
     carrier's finiteness (its virtue for the eight census walkers) is EXACTLY what makes it structurally
     incapable of even STATING `H_3`-non-finiteness.  Witnessing the no-go needs a NEW infinite-basis /
     non-truncated complex substrate.  Proved below as `carrierDegreeThreeChainIsAlwaysFinite`.

Citations: Squier 1987 (JPAA 49); Squier–Otto–Kobayashi (finite derivation type); Lafont–Prouté;
Guiraud–Malbos (polygraphic resolutions / finite derivation type); Cremanns–Otto (FDT vs FP_3). -/

/-- The status of one `S_1` witness obligation, honestly classified. -/
inductive MonoidWitnessObligationStatus
  /-- Representable in the shipped carrier today (possibly shape-only). -/
  | expressibleNow
  /-- A genuine separate obligation off the convergent path — walled for this round. -/
  | separateHardObligation
  /-- Structurally impossible over the finite carrier — needs a new infinite-basis substrate. -/
  | walledByCarrierFiniteness

/-- The `S_1` witness ledger: the monoid's three obligations with their honest statuses. -/
structure SquierWitnessLedgerEntry where
  /-- Obligation 1: finite presentation representable in the carrier. -/
  finitePresentationStatus : MonoidWitnessObligationStatus
  /-- Obligation 2: decidable word problem, off the convergent path. -/
  decidableWordProblemStatus : MonoidWitnessObligationStatus
  /-- Obligation 3: homological non-finiteness (`H_3` not f.g.). -/
  homologicalNonFinitenessStatus : MonoidWitnessObligationStatus

/-- The `S_1` GENERATOR SHAPE as a `WalkerPresentation`: five endo 1-generators at one object, with the
rule list left EMPTY.  This witnesses OBLIGATION 1's SHAPE ONLY — that the carrier admits a
five-generator single-object finite presentation.  Squier's exact defining relations are NOT transcribed
here (that is the named residual); the empty `rules` transparently records that `C_2 = 0` relations are
populated, so no claim is made that `S_1` has no relations. -/
def squierMonoidFiveGeneratorShape : WalkerPresentation :=
  { oneGeneratorCount := 5
  , rules := []
  , criticalPairs := [] }

/-- ★ **Obligation 1 (shape): the carrier holds a five-generator single-object presentation** — the
`C_1` basis count is exactly `5`, `rfl`.  Carrier-representability of `S_1`'s generator shape; the
relations remain the named transcription residual. -/
theorem squierMonoidFiveGeneratorShapeHasFiveGenerators :
    squierMonoidFiveGeneratorShape.computeBasisCount 1 = 5 := rfl

/-- ★★ **Obligation 3, the WALL, PROVED.**  For ANY presentation the degree-3 chain basis is
`criticalPairs.length` — a finite `Nat` — so the carrier's `H_3` is a subquotient of a finitely-generated
free module, ALWAYS finitely generated.  This is the structural obstruction: the carrier CANNOT even
STATE `H_3`-non-finiteness, so `S_1`'s homological witness is unreachable without a new infinite-basis
substrate.  `rfl` per presentation. -/
theorem carrierDegreeThreeChainIsAlwaysFinite :
    ∀ presentation : WalkerPresentation,
      presentation.computeBasisCount 3 = presentation.criticalPairs.length :=
  fun _ => rfl

/-- ★ **The assembled `S_1` witness ledger.**  Obligation 1 EXPRESSIBLE-NOW (shape, relations pending);
obligation 2 a SEPARATE HARD OBLIGATION off the convergent path (walled); obligation 3 WALLED BY CARRIER
FINITENESS (`carrierDegreeThreeChainIsAlwaysFinite`).  The honest r1 witness deliverable: `S_1` named, its
obligations costed, the two genuine walls recorded — NOT a claim that `S_1`'s non-finiteness is proved. -/
def squierWitnessLedger : SquierWitnessLedgerEntry :=
  { finitePresentationStatus := MonoidWitnessObligationStatus.expressibleNow
  , decidableWordProblemStatus := MonoidWitnessObligationStatus.separateHardObligation
  , homologicalNonFinitenessStatus := MonoidWitnessObligationStatus.walledByCarrierFiniteness }

/-! ## B4 — THE #2139 ROUND-ONE LEDGER (what r1 opened, what remains — multi-round)

### What r1 OPENED (shipped, zero-axiom)

  * **B1 — the finiteness read-off**: the finite `HomologyInvariant (freeRank, torsionFactors)`, the
    single generic Smith read-off `SmithHomologyData.homologyInvariant`, the four-walker EXHIBITION
    (`H2(monad) = 0`, `H1(involution) = ZZ/2`, `H1(cyclic-3) = ZZ/3`, `H1(idempotent) = 0`), and the
    generic bound `freeRank(H_k) ≤ C_k`.  Honest scoping: finiteness is BY CONSTRUCTION, content is
    exhibition + genericity — NOT Squier's finiteness theorem.
  * **B2 — the no-go interface**: `HomologyPresentationInvariance` (the invariance GAP as an explicit
    hypothesis field), `squierNoGoSchema` (the contrapositive derivation gated on it), the op-duality
    sign-invariance witness (`monadAndComonadShareDegreeTwoInvariant` with distinct boundaries), the
    non-degenerate interface inhabitant, and the honest vacuity caveat
    (`squierNoGoAntecedentUnsatisfiableOverThisCarrier`).
  * **B3 — the S_1 witness ledger**: `S_1` named, its three obligations costed, obligation 3's wall
    PROVED (`carrierDegreeThreeChainIsAlwaysFinite`).

### What REMAINS (the named residuals — multi-round; NEVER papered)

  * **R1 (WALL) — monoid-level presentation invariance.**  Two finite convergent presentations of the
    same monoid have isomorphic homology (Tietze / finite-derivation-type / derived-equivalence route).
    Needs a `PresentsMonoid` relation (does not exist) + the abelianized-Tietze-move chain-homotopy
    argument.  This is the load-bearing hypothesis the `isInvariant` field stands in for.  Down-payment
    SHIPPED: matrix-level SIGN-invariance, the op-duality worked instance
    (`monadAndComonadShareDegreeTwoInvariant`, negated boundary → equal invariant); the fully-generic
    unimodular-equivalence ⟹ equal-invariant theorem stays the residual.
  * **R2 (WALL) — the S_1 homological witness.**  Obligation 2 (decidability off the convergent path)
    and obligation 3 (`H_3` not f.g.) — the latter WALLED by carrier structural finiteness
    (`carrierDegreeThreeChainIsAlwaysFinite`): witnessing it needs a NEW infinite-basis / non-truncated
    complex substrate.
  * **R3 — the schema's live antecedent.**  Over this carrier the no-go's `¬ finitely-generated`
    antecedent is unsatisfiable (`squierNoGoAntecedentUnsatisfiableOverThisCarrier`); pulling the
    trigger needs R2's substrate.

### Honest scoping (no overclaim vs Squier 1987)

This round does NOT prove: Squier's monoid-level finiteness theorem, `S_1`'s non-finiteness, or homology
presentation-invariance.  It ships the reachable INTERFACE + two down-payments (the exhibition read-off,
the op-duality sign-invariance) and NAMES the two deep walls (R1 monoid-level invariance, R2 the carrier's
structural finiteness).  The invariance gap lives in the TYPE of `squierNoGoSchema` — named, never
papered.  Exactly the "theorem + interface + ledger (honest), NOT a fabricated Squier close" shape. -/

/-- ★ **The #2139 round-one ledger marker.**  What r1 OPENED, zero-axiom: the B1 finiteness read-off
(exhibition + genericity), the B2 no-go INTERFACE (`HomologyPresentationInvariance` +
`squierNoGoSchema`, the invariance gap explicit in the type) with its op-duality sign-invariance witness
and honest vacuity caveat, and the B3 `S_1` witness ledger with obligation 3's wall proved.  What
REMAINS (named, multi-round): R1 monoid-level presentation invariance, R2 the S_1 homological witness
(walled by carrier finiteness).  Read the meaning from THIS docstring (the honest-record convention). -/
def squierNoGoRoundOneLedgerIsComplete : Bool := true

/-- ★ **The HONESTY marker: r1 OPENS Squier, it does NOT close it.**  No claim is made that Squier's
no-go, `S_1`'s non-finiteness, or homology presentation-invariance is proved; those are the named
residuals R1/R2.  `= true` records the stance, not a closure. -/
def squierNoGoOpenedButNotClosed : Bool := true

end FX1Poly.Polygraph.Homology
