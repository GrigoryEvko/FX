import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/FuzzCorpusConvertibility — the §27.3-L2 fuzz corpus is ONE proper Conv class

`MetatheoryFuzz.lean` ships the two §27.3-Layer-2 property-based fuzz families and proves each member
well-typed / SN / progressing / evaluating to `Type@0`: the IDENTITY tower `metatheoryFuzzFamily` (the
argument-SUBSTITUTING β-path, peeling one redex per step) and the CONSTANT tower
`metatheoryFuzzConstantFamily` (the argument-DISCARDING β-path, erasing the whole redex stack in one
step).  Both families were verified independently.  This file draws the relation BETWEEN them: under
definitional equality (`Conv`) the two β-paths are indistinguishable — the entire fuzz corpus (both
families, all depths) collapses to a SINGLE `Conv` class, and that class is PROPER (it does not swallow
every term).

The bridge is `Conv.fromStepStar` against the shipped `*_reducesToType0` reductions: every member
converts to `Type@0`, so any two members convert to each other by `Conv.sym`/`Conv.trans` (the
unconditional raw-confluence equivalence package, #420/#714).

  * `metatheoryFuzzFamily_convToType0` / `metatheoryFuzzConstantFamily_convToType0` — every member of
    each family is convertible to the canonical value `Type@0`.
  * `metatheoryFuzzFamily_intraConvertible` — any two identity-tower members are convertible (regardless
    of depth): the family is one `Conv` class.
  * **`metatheoryFuzz_crossFamilyConvertible`** — ★ the headline: ANY identity-tower member is
    convertible to ANY constant-tower member.  The substitute-path and the erase-path produce
    definitionally-equal results — the metatheory does not distinguish the two β-paths, even though they
    reduce with different step counts (the identity tower in `n` steps, the constant tower in one).
  * **`metatheoryFuzzFamily_notConvToType1`** — ★ the class is PROPER: no fuzz member is convertible to
    `Type@1`.  Were it, transitivity would give `Conv Type@0 Type@1`, which `universeCodeCell_inj_of_conv`
    collapses to `lzero = lsucc lzero` — refuted by `LevelExpr` no-confusion.  So the corpus's `Conv`
    class is a genuine equivalence class, not the degenerate everything-converts collapse — the
    non-vacuity that makes the convertibility content meaningful.

## Zero-axiom verification

`Conv.fromStepStar` on the shipped `*_reducesToType0` chains, `Conv.sym`/`Conv.trans` (unconditional, via
raw confluence #420), and `universeCodeCell_inj_of_conv` + `LevelExpr.noConfusion` for properness.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (every declaration
probed with `#print axioms` before landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Every identity-tower member converts to the canonical value `Type@0` — `Conv.fromStepStar` on the
shipped depth-many β-reduction `metatheoryFuzzFamily_reducesToType0`. -/
theorem metatheoryFuzzFamily_convToType0 (n : Nat) :
    Conv (metatheoryFuzzFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  Conv.fromStepStar (metatheoryFuzzFamily_reducesToType0 n)

/-- Every constant-tower member converts to `Type@0` — `Conv.fromStepStar` on the shipped single-step
β-reduction `metatheoryFuzzConstantFamily_reducesToType0`. -/
theorem metatheoryFuzzConstantFamily_convToType0 (n : Nat) :
    Conv (metatheoryFuzzConstantFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  Conv.fromStepStar (metatheoryFuzzConstantFamily_reducesToType0 n)

/-- Any two identity-tower members are convertible regardless of depth — the family is a single `Conv`
class (both endpoints convert to `Type@0`; chain by `Conv.sym`/`Conv.trans`). -/
theorem metatheoryFuzzFamily_intraConvertible (firstDepth secondDepth : Nat) :
    Conv (metatheoryFuzzFamily firstDepth) (metatheoryFuzzFamily secondDepth) :=
  Conv.trans (metatheoryFuzzFamily_convToType0 firstDepth)
    (Conv.sym (metatheoryFuzzFamily_convToType0 secondDepth))

/-- ★ **Cross-family convertibility.**  Any identity-tower member (the argument-SUBSTITUTING β-path) is
convertible to any constant-tower member (the argument-DISCARDING β-path).  Definitional equality does
not distinguish the two β-paths, despite their different reduction lengths — the whole fuzz corpus is one
`Conv` class. -/
theorem metatheoryFuzz_crossFamilyConvertible (identityDepth constantDepth : Nat) :
    Conv (metatheoryFuzzFamily identityDepth) (metatheoryFuzzConstantFamily constantDepth) :=
  Conv.trans (metatheoryFuzzFamily_convToType0 identityDepth)
    (Conv.sym (metatheoryFuzzConstantFamily_convToType0 constantDepth))

/-- ★ **The corpus `Conv` class is PROPER.**  No fuzz member is convertible to `Type@1`: that would give
`Conv Type@0 Type@1` (transitivity), which `universeCodeCell_inj_of_conv` collapses to `lzero = lsucc
lzero`, refuted by `LevelExpr` no-confusion.  So the convertibility is non-degenerate — `Conv` genuinely
discriminates `Type@0` from `Type@1`, and the corpus class does not swallow every term. -/
theorem metatheoryFuzzFamily_notConvToType1 (n : Nat) :
    ¬ Conv (metatheoryFuzzFamily n)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) := by
  intro convToType1
  have type0ConvType1 : Conv (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    Conv.trans (Conv.sym (metatheoryFuzzFamily_convToType0 n)) convToType1
  obtain ⟨levelEq, _flagEq⟩ := universeCodeCell_inj_of_conv type0ConvType1
  exact LevelExpr.noConfusion levelEq

end FX1Poly.Typed
