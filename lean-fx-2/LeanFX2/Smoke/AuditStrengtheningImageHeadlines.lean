import LeanFX2.Term.StrengtheningImage

/-! # Smoke/AuditStrengtheningImageHeadlines

Reviewer-facing `#print axioms` gate for the zero-axiom
strengthening-image *headlines* in `Term/StrengtheningImage/`.

These five headlines are the load-bearing surface of the Phase A
image-theorem foundation per `purrfect-bubbling-platypus.md`:

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

Per-arm `_rename_isSome` and `_weaken_inv` smoke entries live in
`AuditTermWeakenInverse.lean` and the audit gates at
`Tools/AuditAll/AuditTerm/StrengtheningImage.lean`; this file
covers only the consumer-facing headlines.

Each `#print axioms` line below must report
"does not depend on any axioms" — strict Layer K gate. -/

namespace LeanFX2.Smoke.AuditStrengtheningImageHeadlines

#print axioms LeanFX2.Term.isAggregatorSound_universal
#print axioms LeanFX2.Term.weaken_inv_of_strengthenTyped?_some
#print axioms LeanFX2.Term.rename_image_iff_strengthenTyped?_some
#print axioms LeanFX2.Term.strengthenTyped?_weaken_eq
#print axioms LeanFX2.Term.weaken_image_totality

end LeanFX2.Smoke.AuditStrengtheningImageHeadlines
