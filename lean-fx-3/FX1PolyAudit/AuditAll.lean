import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.AuditCore
import FX1PolyAudit.AuditCoreSubstrate
import FX1PolyAudit.AuditFoundation
import FX1PolyAudit.AuditGen
import FX1PolyAudit.AuditProfile
import FX1PolyAudit.AuditFXProfile
import FX1PolyAudit.AuditNbE
import FX1PolyAudit.AuditUniverse
import FX1PolyAudit.AuditTyped

/-! # FX1PolyAudit/AuditAll — the authoritative zero-axiom audit umbrella

Pure-import umbrella over every required audit gate module.  This is the
single reviewer- and CI-facing entry point for the strict zero-axiom
sweep: building `FX1PolyAudit.AuditAll` runs the full per-declaration
`#assert_no_axioms` gate set plus the per-namespace axiom sweeps.

Mirrors lean-fx-2's `LeanFX2.Tools.AuditAll` (the pure-import umbrella
whose siblings carry the assertions), with one structural simplification:
lean-fx-3 keeps ONLY what is genuinely required — see the exclusion note
below.

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

The second invariant is the one a release gate actually needs, and it was
absent until this file.

## Required coverage (the gate modules)

* `DependencyAudit`    — defines the `#assert_no_axioms` primitive (the
  build-failing transitive-dependency axiom check).  Every gate below
  imports it; listed first so the primitive itself is a named dependency.
* `AuditCore`          — `FX1Poly.Core` cell-calculus spine (CellSort …)
  + the native cells-classify-cells typing markers.
* `AuditCoreSubstrate` — `FX1Poly.Core` / `FX1Poly.Foundation` per-namespace
  axiom sweeps (the broad coverage over decls without an explicit gate).
* `AuditFoundation`    — `FX1Poly.Foundation` action / raw-subst gates.
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

## Deliberately EXCLUDED — do NOT re-add

lean-fx-2's `Tools/AuditAll` accreted 17 `Gates*` budget-ratchet / import-
census / naming / parity / debt-dashboard files and 3 `Summary*` full-
namespace-walk reports.  That machinery was slow, fragile (the namespace
sweep silently passes an under-imported namespace as "ok 0 declarations";
the dependency walk truncates at a fuel cap with no error), and largely
ceremonial.  It is intentionally NOT carried into lean-fx-3.  The genuine
guarantee — "no declaration depends on an axiom" — is delivered by the
per-decl `#assert_no_axioms` gates above, which are both faster and harder
to fool than a coverage-count ratchet.  A future agent must NOT reintroduce
the `Gates*` / `Summary*` infrastructure; add per-decl gates instead.
-/
