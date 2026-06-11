import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/LogRelSpec
    — SN-006: contingency spec for the Adjedj derivation-indexed logical relation (fallback-only)

This file is a committed DESIGN SPEC, not a proof development.  It records the fallback reducibility model
to use IF the SN-005-locked primary route (classifier-universe-level, `denote`-keyed, predicative-WF
reducibility) stalls.  The primary route is GO (SN-004 / SN-005); this fallback is reserved for two
situations:

* a hypothetical SN-004 NO-GO (did NOT occur — recorded for completeness), or
* the IMPREDICATIVE `limax` fragment (tracker #472), where SN-003's predicative strict decrease
  `denote e < denote (lsucc e)` is unavailable because `limax` collapses value-dependently and the numeric
  level measure no longer descends.

## The Adjedj reference skeleton (arXiv:2310.06376, "Martin-Löf à la Coq")

Adjedj–Lennon-Bertrand–Maillard–Pédrot–Pujet mechanize decidable conversion for MLTT-with-inductives by a
logical relation indexed NOT by an external numeric level but by the TYPING/VALIDITY DERIVATION itself:

* `LRTy Γ A` — an inductive family witnessing "`A` is reducibly a type in `Γ`", whose constructors mirror the
  type formers (universe, Π, Σ, Nat, …), each carrying the recursive reducibility data of its components.
* `LRTm Γ A t` (relative to an `LRTy Γ A` witness) — membership, defined by RECURSION ON THE `LRTy` WITNESS:
  at the Π witness it is the usual "maps reducible arguments to reducible results", at the universe witness
  it is "the code is itself reducibly a type", etc.

This is inductive-RECURSIVE and lives in `Type` (large), so it can carry semantic value data.  The crucial
property: the recursion is on the LogRel/derivation STRUCTURE, which is strictly smaller at every step
REGARDLESS of universe size — so it is impredicativity-robust where a numeric universe-level measure is not.

## Mapping onto FX

FX already has the typing derivation as a first-class `Prop` inductive — `HasTypeDescPi` (this module's
import), with exactly five derivation constructors plus the `DescTelescopePi` premise vector:

* `ofFormation` — a formation/leaf term typed by the cell engine `HasTypeDesc`;
* `conv` — conversion (re-typing the classifier up to `Conv`);
* `piIntro` — λ-introduction (domain + codomain + body sub-derivations);
* `piElim` — application (function + argument sub-derivations), classifier `subst0`-substituted;
* `genFormationPi` — the GENERIC former, typed from one `typingRuleDescOf` row + a `DescTelescopePi`
  child telescope (the §5-endgame cascade-free formation rule);
* `DescTelescopePi.{nil,cons}` — the cumulative dependent telescope of child types, mutual with
  `HasTypeDescPi`, referencing it only positively in `cons.headTyped`.

So "index the logical relation by the derivation" is NATIVE in FX: the fallback reducibility predicate
recurses on a `HasTypeDescPi` derivation via its auto-generated mutual recursor — no separate `LRTy`
inductive needs to be reintroduced; `HasTypeDescPi` already IS the `LRTy`-shaped derivation index.

## Lean-4 feasibility (Init-only, zero-axiom) — three encodings assessed

1. **Full `Type`-valued induction-recursion (Adjedj `LRTy`/`LRTm` verbatim).**  Lean 4 supports IR natively,
   but a `Type`-valued logical relation over the 203-generator table is heavy and risks positivity /
   equation-compiler axiom leaks (the indexed-match propext traps catalogued in this project).  RESERVED as
   the deepest fallback — needed ONLY if reducibility must carry `Type`-level semantic VALUE data (e.g. for
   the `Type`-valued NbE values; there the already-shipped `Ty` well-foundedness measure of tracker #383
   supplies the structural descent without IR).

2. **`Nat` derivation-size + well-founded recursion.**  BLOCKED.  `HasTypeDescPi` is `Prop`-valued, so there
   is no large elimination from it into `Nat` (subsingleton elimination only) — one cannot extract a numeric
   size from a `Prop` derivation.  The naive "well-founded-on-derivation-size" encoding is therefore not
   available for the `Prop` derivation; this is the key technical finding of SN-006.

3. **`Prop`-motive structural recursion on the derivation.**  RECOMMENDED.  The SN/reducibility conclusion is
   itself a `Prop` (`IsStronglyNormalizing`, reducibility membership), so the recursion motive is
   `Prop`-valued and `HasTypeDescPi.rec` into it is ordinary small elimination — no IR, no `Nat` size, no
   large elimination.  The sub-derivations are structurally smaller, and because the recursion descends on
   derivation STRUCTURE rather than on universe levels, the `limax` impredicativity that defeats SN-003's
   numeric `denote` measure is IRRELEVANT here.  This is precisely the scheme the PRIMARY route's
   `ValidTyping.fundamental` already uses (`ValidTyping.rec`, `Prop → Prop`): the fallback differs from the
   primary only in the reducibility MOTIVE (swap the `denote`-keyed motive for a derivation-structural one),
   not in the recursion skeleton — which is exactly why this fallback de-risks the predicative assumption at
   low cost.

## Verdict

Fallback encoding = **option 3** (`Prop`-motive structural recursion on `HasTypeDescPi`), with option 1
(full `Type`-valued IR) reserved only for a `Type`-valued reducibility carrying semantic value data.  Option
2 is impossible.  This stays FALLBACK-ONLY: the primary syntactic SN path remains the SN-005-locked
classifier-level validity route (GO).  No proof obligations are discharged in this file (SN-006 is a spec);
the single marker below records the fallback's TARGET statement as a checked `Prop`, deferring its proof.

## Zero-axiom verification

The marker is a plain `Prop`-valued `def` (a quantified implication, no recursion or match), so it depends on
no axioms.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per
declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Foundation

/-- **SN-006 fallback target (deferred): derivation-indexed strong normalization.**  The statement the
Adjedj-style derivation-indexed logical relation would discharge if the predicative primary route stalls:
every grown typing derivation has a strongly normalizing subject.  This is the SAME proposition as the
primary SN goal (SN-043 / tracker #498), so EITHER route closes it — the fallback's distinctive content is
the PROOF STRATEGY (recommended option 3 of the module docstring: `Prop`-motive structural recursion on the
`HasTypeDescPi` derivation via its mutual recursor, impredicativity-robust because it descends on derivation
structure, not on universe levels), not the statement.  Stated here as a checked `Prop` with NO proof
obligation: SN-006 is a contingency spec, fallback-only; the primary classifier-level route is GO. -/
def DerivationIndexedStrongNormalizationFallback (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
    HasTypeDescPi profile context subject classifier →
      IsStronglyNormalizing subject

end FX1Poly.Typed
