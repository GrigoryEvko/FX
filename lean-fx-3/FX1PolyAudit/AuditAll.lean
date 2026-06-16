import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.AuditCore
import FX1PolyAudit.AuditCoreSubstrate
import FX1PolyAudit.AuditTier0ContextRoot
import FX1PolyAudit.AuditTier0ContextInclusion
import FX1PolyAudit.AuditTier0ContextComprehension
import FX1PolyAudit.AuditTier0ContextLaws
import FX1PolyAudit.AuditTier0ContextSliceCategory
import FX1PolyAudit.AuditTier0ContextColimits
import FX1PolyAudit.AuditTier0ContextModalLock
import FX1PolyAudit.AuditTier0ContextInitiality
import FX1PolyAudit.AuditTier0ContextBiequivalence
import FX1PolyAudit.AuditTier0ContextStrictification
import FX1PolyAudit.AuditTier0ContextExplicitSubstitution
import FX1PolyAudit.AuditTier0ContextSubstitutionFree
import FX1PolyAudit.AuditTier0ContextComprehensionCategory
import FX1PolyAudit.AuditTier0ContextBeckChevalleyCoherence
import FX1PolyAudit.AuditTier0ContextGlobalSections
import FX1PolyAudit.AuditTier0ContextPushoutContexts
import FX1PolyAudit.AuditTier0ContextSubstitutionTwoGroupoid
import FX1PolyAudit.AuditTier0ContextSconing
import FX1PolyAudit.AuditTier0ContextMultimodalNormalization
import FX1PolyAudit.AuditTier0ContextSimplicialModel
import FX1PolyAudit.AuditTier0ContextInftyOneCwF
import FX1PolyAudit.AuditTier0ContextFibrationCategory
import FX1PolyAudit.AuditTier0ContextDemocracyLCC
import FX1PolyAudit.AuditTier0ContextStandaloneModalRMC
import FX1PolyAudit.AuditTier0ContextCubicalModel
import FX1PolyAudit.AuditTier0ContextGroupoidModel
import FX1PolyAudit.AuditTier0ContextRealizability
import FX1PolyAudit.AuditTier0ContextPresheafModel
import FX1PolyAudit.AuditTier0ContextForcing
import FX1PolyAudit.AuditSyntaxAction
import FX1PolyAudit.AuditGen
import FX1PolyAudit.AuditProfile
import FX1PolyAudit.AuditFXProfile
import FX1PolyAudit.AuditNbE
import FX1PolyAudit.AuditUniverse
import FX1PolyAudit.AuditTyped
import FX1PolyAudit.AuditOmegacE
import FX1PolyAudit.AuditModal
import FX1PolyAudit.AuditFX0Poly
import FX1PolyAudit.CapstoneSignoff

/-! # FX1PolyAudit/AuditAll — the authoritative zero-axiom audit umbrella

Pure-import umbrella over every required audit gate module.  This is the
single reviewer- and CI-facing entry point for the strict zero-axiom
sweep: building `FX1PolyAudit.AuditAll` runs the full per-declaration
`#assert_no_axioms` gate set plus the per-namespace axiom sweeps.  It
names ONLY the genuinely-required gates — see the exclusion note below.

## Why an explicit umbrella in addition to the `.submodules` glob

`lake build FX1PolyAudit` builds every file under `FX1PolyAudit/` via the
lakefile's `globs := #[.submodules `FX1PolyAudit]`.  That guarantees every
gate file that EXISTS compiles — but its coverage set is "whatever files
are on disk."  Delete a gate file and the glob silently builds the
remainder and still reports success: the dropped coverage is invisible.

This umbrella inverts that: it names the REQUIRED gate modules explicitly,
so removing a gate file (without also editing this list) becomes a
missing-import build error.  The two mechanisms compose:

* glob      ⟹ "everything present compiles" (no orphaned-but-broken gate),
* umbrella  ⟹ "everything required is present" (no silently-dropped gate).

The second invariant is the one a release gate actually needs.

## Required coverage (the gate modules)

* `DependencyAudit`    — defines the `#assert_no_axioms` primitive (the
  build-failing transitive-dependency axiom check).  Every gate below
  imports it; listed first so the primitive itself is a named dependency.
* `AuditCore`          — `FX1Poly.Core` cell-calculus spine (CellSort …)
  + the native cells-classify-cells typing markers.
* `AuditCoreSubstrate` — `FX1Poly.Core` / `FX1Poly.Tier0.Syntax` per-namespace
  axiom sweeps (the broad coverage over decls without an explicit gate).
* `AuditTier0ContextRoot` — the `context-0` axis root: the modal
  representable-map-category interface (`ContextAxis`) + the `fxContextAxis`
  L0 witness wiring the renaming RMC + substitution category + global sections.
* `AuditTier0ContextInclusion` — the `context-1` two-category connector: the
  renaming ⊂ substitution inclusion functor (`renamingInclusion`) + the two
  PROVED functor laws, connecting the `context-0` bundle's two categories.
* `AuditTier0ContextComprehension` — the `context-1` LEFT/Σ leg: the
  Beck–Chevalley substitution-stability square (`SubstVec.cons_compose`, the
  Frobenius-Σ content) + the gathered comprehension witness
  `fxContextComprehension`.
* `AuditTier0ContextLaws` — the `context-1` earned CwF laws: inclusion
  faithfulness (earning the `⊂`), the comprehension η-law, the lift functor +
  display-map naturality, the comprehension representability bijection, and the
  inclusion's display-preservation.
* `AuditTier0ContextSliceCategory` — the `context-2` context-side residue: the slice
  category `C/U` as a genuine `RawCategory` (the three laws PROVED via slice-morphism
  extensionality) + the generic display (the universal natural transformation whose
  naturality square is the slice triangle's commute), wired over the FX context axis.
  The Uemura bijection proper (`×type`) is deferred to `fib-1`.
* `AuditTier0ContextColimits` — the `context-3` RIGHT/colimits leg: the FINITE COPRODUCTS of the
  context category — the INITIAL object (scope 0, the empty context; uniqueness by `PUnit` eta) and
  the binary COPRODUCT (scope addition; both β-laws via the append-lookup laws, η/uniqueness via the
  `append_split` law), each a PROVED categorical universal property.  The dimensional adjoint
  quadruple (transpension proper, `×mode`) is deferred to `fib-4`.
* `AuditSyntaxAction`  — `FX1Poly.Tier0.Syntax` action / raw-subst gates.
* `AuditGen`           — `Generator` table gates.
* `AuditProfile`       — `PolyProfile` / Tier-0 sconing / profile-extension.
* `AuditFXProfile`     — FX profile certified-views soundness.
* `AuditNbE`           — normalizer / quote contract gates.
* `AuditUniverse`      — `LevelExpr` / `UniverseFlag` normalization +
  serialization (the largest per-decl gate set).
* `AuditTyped`         — the typed layer: `TypingContext` / `HasType` /
  weakening / substitution / validity / SN / inversion / uniqueness /
  decidable `IsType` + decidable `HasType` + decidable typed `Conv`,
  plus the honesty (0-FP) and decider (0-FN-per-fragment) corpora.
* `AuditOmegacE`        — the ωcE / Makkai word-problem leg (Path B): the
  dimension-1 free-monoid structure on scaffold words (the word-equality
  recursion base).
* `AuditModal`          — the resource-graded doctrine (the SECOND graded
  dimension): the usage `{0, 1, ω}` and security ordered-semiring substrate
  + the `IsLawfulOrderedGradeSemiring fxUsageSemiring` verified-semiring witness.

## Deliberately EXCLUDED — do NOT re-add

`Gates*` budget-ratchet / import-census / naming / parity / debt-dashboard
files and `Summary*` full-namespace-walk reports are deliberately absent.
That machinery is slow, fragile (the namespace sweep silently passes an
under-imported namespace as "ok 0 declarations"; the dependency walk
truncates at a fuel cap with no error), and largely ceremonial.  The
genuine guarantee — "no declaration depends on an axiom" — is delivered by
the per-decl `#assert_no_axioms` gates above, which are both faster and
harder to fool than a coverage-count ratchet.  Do NOT reintroduce the
`Gates*` / `Summary*` infrastructure; add per-decl gates instead.
-/
