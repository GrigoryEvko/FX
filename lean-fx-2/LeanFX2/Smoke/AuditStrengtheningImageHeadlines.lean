import LeanFX2.Term.StrengtheningImage

/-! # Smoke/AuditStrengtheningImageHeadlines

Reviewer-facing `#print axioms` gate for the zero-axiom
strengthening-image *headlines* in `Term/StrengtheningImage/`.

These eight headlines are the load-bearing surface of the Phase A
image-theorem foundation per `purrfect-bubbling-platypus.md`:

Source-direction (aggregator-sound, image):

* `isAggregatorSound_universal` — universal aggregator composition
  over all 78 Term ctors via structural induction;
* `weaken_inv_of_strengthenTyped?_some` — right-inverse soundness:
  if `partialStrengthenTyped?` returns `some result`, the
  re-rename equals the source (HEq form);
* `rename_image_iff_strengthenTyped?_some` — bidirectional
  headline: typed-renaming image iff strengthening succeeds;
* `strengthenTyped?_weaken_eq` — T1 specialized to newest-slot
  weakening: deterministic equation form;
* `weaken_image_totality` — consumer-facing existence package
  combining `unweaken?_weaken` with `strengthenTyped?_weaken_eq`.

Target-direction (totality predicates, residual surface):

* `IsAggregatorTotal` — the arbitrary-strengthening totality
  predicate retained for the few consumers that quantify over any
  `ContextStrengthening` (renaming-image API is strictly narrower
  and preferred);
* `IsTotalOnWeaken` — the newest-slot-weakening totality
  predicate, the canonical instance of `IsAggregatorTotal` at
  `RawRenaming.weaken`;
* `isTotalOnWeaken_universal` — universal closure of
  `IsTotalOnWeaken`, the T1-backed weaken-image companion to
  `isAggregatorSound_universal`.

Per-arm `_rename_isSome` and `_weaken_inv` smoke entries live in
`AuditTermWeakenInverse.lean` and the audit gates at
`Tools/AuditAll/AuditTerm/StrengtheningImage.lean`; this file
covers only the consumer-facing headlines.

Each `#print axioms` line below must report
"does not depend on any axioms" — strict Layer K gate. -/

namespace LeanFX2.Smoke.AuditStrengtheningImageHeadlines

-- Source-direction (aggregator-sound + image).
#print axioms LeanFX2.Term.isAggregatorSound_universal
#print axioms LeanFX2.Term.weaken_inv_of_strengthenTyped?_some
#print axioms LeanFX2.Term.rename_image_iff_strengthenTyped?_some
#print axioms LeanFX2.Term.strengthenTyped?_weaken_eq
#print axioms LeanFX2.Term.weaken_image_totality

-- Target-direction (totality predicates + universal closure).
#print axioms LeanFX2.Term.IsAggregatorTotal
#print axioms LeanFX2.Term.IsTotalOnWeaken
#print axioms LeanFX2.Term.isTotalOnWeaken_universal

-- Per-Ty `weaken_inv_<Ty>` family — 28 zero-axiom corollaries
-- packaging weakening-image strengthening at every Ty shape (see
-- strength-T4-{closed,binder,parametric,id-family,cubical,
-- advanced} task family and `Tools/AuditAll/AuditTerm/
-- StrengtheningImage.lean:18-44, 172).

-- Special: secondary right-inverse forms.
#print axioms LeanFX2.Term.weaken_inv_of_unweaken?_some

-- Closed Ty (6): primitive types with no payload structure.
#print axioms LeanFX2.Term.weaken_inv_unit
#print axioms LeanFX2.Term.weaken_inv_bool
#print axioms LeanFX2.Term.weaken_inv_nat
#print axioms LeanFX2.Term.weaken_inv_empty
#print axioms LeanFX2.Term.weaken_inv_interval
#print axioms LeanFX2.Term.weaken_inv_universe

-- Binder Ty (4): types that bind a new variable in their body.
#print axioms LeanFX2.Term.weaken_inv_pi
#print axioms LeanFX2.Term.weaken_inv_sigma
#print axioms LeanFX2.Term.weaken_inv_path
#print axioms LeanFX2.Term.weaken_inv_refine

-- Universe-poly + function-arrow specializations.
#print axioms LeanFX2.Term.weaken_inv_tyVar
#print axioms LeanFX2.Term.weaken_inv_arrow

-- Parametric Ty (3): single-argument inductive type formers.
#print axioms LeanFX2.Term.weaken_inv_listType
#print axioms LeanFX2.Term.weaken_inv_optionType
#print axioms LeanFX2.Term.weaken_inv_eitherType

-- Identity-family Ty (4): HoTT identity + observational + strict.
#print axioms LeanFX2.Term.weaken_inv_id
#print axioms LeanFX2.Term.weaken_inv_oeq
#print axioms LeanFX2.Term.weaken_inv_idStrict
#print axioms LeanFX2.Term.weaken_inv_equiv

-- Cubical Ty (1): glue type at cubical-mode binders.
#print axioms LeanFX2.Term.weaken_inv_glue

-- Advanced Ty (4): record / codata / session / effect.
#print axioms LeanFX2.Term.weaken_inv_record
#print axioms LeanFX2.Term.weaken_inv_codata
#print axioms LeanFX2.Term.weaken_inv_session
#print axioms LeanFX2.Term.weaken_inv_effect

-- Modal Ty (1): modality-shifted carrier.
#print axioms LeanFX2.Term.weaken_inv_modal

end LeanFX2.Smoke.AuditStrengtheningImageHeadlines
