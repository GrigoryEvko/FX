import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.TypedNormalizer

/-! # FX1Poly/Typed/FuzzCorpusNormalizes — the verified SN-normalizer computes the L2 fuzz corpus to Type@0

`TypedNormalizer.lean` (SN-112) builds `HasTypeDescPi.normalForm` — the term-layer normalizer keyed directly on
a grown typing derivation, with SN-043 discharging termination — and `reachedNormalForm_eq_normalForm`: any
normal form a closed grown-well-typed subject REACHES equals the computed `normalForm` (it is THE unique normal
form, by raw confluence #420 + open SN).  `MetatheoryFuzz.lean` ships the two §27.3-L2 fuzz families, each member
typed and proven to `*_reducesToType0`.  This file composes the two: the verified normalizer does not merely
exist for the corpus — it COMPUTES every member of both families to the canonical value `Type@0`.  This is the
computational sharpening of `FuzzCorpusConvertibility` (firing-prior): there the members were shown mutually
`Conv`; here the actual normalizer OUTPUT is pinned to a single value.

  * `metatheoryFuzzFamily_normalizesToType0` / `metatheoryFuzzConstantFamily_normalizesToType0` — the normalizer
    keyed on each member's typing derivation returns `Type@0`.  `reachedNormalForm_eq_normalForm` fed the shipped
    reduction `*_reducesToType0` (the witnessed reduction reaches `Type@0`) plus `Type@0`'s structural normality
    (`by decide`); the computed normal form IS the reached one, so it equals `Type@0`.
  * **`metatheoryFuzz_normalFormsAgree`** — ★ the two families' computed normal forms COINCIDE (both `Type@0`).
    Since `conv_iff_normalForm_eq` makes normal-form equality the COMPLETE conversion invariant for the typed
    fragment, this is the decidable witness underlying the cross-family convertibility: the substitute-path and
    erase-path are identified not just by `Conv` but by the normalizer producing the very same output cell.

## Zero-axiom verification

`HasTypeDescPi.reachedNormalForm_eq_normalForm` (which composes the unconditional `closedHasUniqueNormalForm` =
open SN + raw confluence #420) on the shipped `*_reducesToType0` chains, with `by decide` for `Type@0`'s
normality and `Eq.trans`/`Eq.symm` to chain.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (every declaration probed with `#print axioms` before landing).  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The verified SN-normalizer computes every identity-tower member to `Type@0`: the member reaches `Type@0`
(`metatheoryFuzzFamily_reducesToType0`), `Type@0` is normal, so it IS the computed normal form
(`reachedNormalForm_eq_normalForm`). -/
theorem metatheoryFuzzFamily_normalizesToType0 {profile : PolyProfile} (n : Nat) :
    (metatheoryFuzzFamily_typed (profile := profile) n).normalForm
      = universeCodeCell LevelExpr.lzero UniverseFlag.standard :=
  ((metatheoryFuzzFamily_typed (profile := profile) n).reachedNormalForm_eq_normalForm
    (metatheoryFuzzFamily_reducesToType0 n) rfl).symm

/-- The verified SN-normalizer computes every constant-tower member to `Type@0` — the argument-discarding twin,
each member reaching `Type@0` in a single β-step. -/
theorem metatheoryFuzzConstantFamily_normalizesToType0 {profile : PolyProfile} (n : Nat) :
    (metatheoryFuzzConstantFamily_typed (profile := profile) n).normalForm
      = universeCodeCell LevelExpr.lzero UniverseFlag.standard :=
  ((metatheoryFuzzConstantFamily_typed (profile := profile) n).reachedNormalForm_eq_normalForm
    (metatheoryFuzzConstantFamily_reducesToType0 n) rfl).symm

/-- ★ **The two fuzz families' computed normal forms coincide.**  The normalizer keyed on an identity-tower
member's derivation and on a constant-tower member's derivation produce the SAME output cell (`Type@0`).  Via
`conv_iff_normalForm_eq` (normal-form equality is the complete conversion invariant), this is the decidable
witness underlying the cross-family convertibility — the substitute-path and erase-path are identified by the
normalizer's actual output, not merely by `Conv`. -/
theorem metatheoryFuzz_normalFormsAgree {profile : PolyProfile} (identityDepth constantDepth : Nat) :
    (metatheoryFuzzFamily_typed (profile := profile) identityDepth).normalForm
      = (metatheoryFuzzConstantFamily_typed (profile := profile) constantDepth).normalForm :=
  (metatheoryFuzzFamily_normalizesToType0 identityDepth).trans
    (metatheoryFuzzConstantFamily_normalizesToType0 constantDepth).symm

end FX1Poly.Typed
