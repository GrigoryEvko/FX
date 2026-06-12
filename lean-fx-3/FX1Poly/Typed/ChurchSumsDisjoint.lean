import FX1Poly.Typed.ChurchSums
import FX1Poly.Typed.ClosedNonConvertibility
import FX1Poly.Core.ConvCongruence
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/ChurchSumsDisjoint — the Church-sum injections are DISJOINT (the coproduct capstone)

`ChurchSums` (#1019) showed that `case` SELECTS the correct handler by tag (`case (inl I) l r ↝* l I`,
`case (inr I) l r ↝* r I`).  Selection alone, however, does not make a coproduct: the defining property of a
sum type is that its two injections are **DISJOINT** — `inl` and `inr` tag their payloads distinguishably, so no
left injection is ever equal to a right injection.  This file proves exactly that faithfulness fact, the dual of
the Church-pair injectivity (#1018):

  **`leftInjection_not_conv_rightInjection` (★)** — `¬ Conv (inl I) (inr I)`: the two injections of the same
  payload are NOT convertible.  The argument is purely operational — it is the coproduct universal property read
  backwards.  If `inl I` and `inr I` were convertible, then applying both to two DISTINGUISHING handlers and
  reducing (via the shipped `caseLeft_selectsLeftHandler` / `caseRight_selectsRightHandler`, #1019) would force
  the two distinct handler-results to be convertible.  Choosing `handlerToUniverse = λx. (a universe code)` and
  `handlerToIdentity = λx. I`, the left case lands on a universe code and the right case lands on the identity
  λ — and a universe code is provably NOT convertible to the identity (`closedUniverseCode_not_conv_identity`,
  `ClosedNonConvertibility.lean`, since they are distinct closed normal forms with different head generators).
  Contradiction.

  **`rightInjection_not_conv_leftInjection`** — the symmetric corollary (`¬ Conv (inr I) (inl I)`), immediate by
  `Conv.sym`.

Together with `caseSelectsByTag` (#1019), the Church sum is a FAITHFUL coproduct encoding: it tags each payload,
selects the matching handler, and never conflates the two tags — the coproduct universal property realized
syntactically in the pure Π-fragment, with no primitive sum type.  This is the exact sum-side analogue of #983
(`churchTrue ≢ churchFalse`): two closed values that the calculus keeps operationally apart.

Like #1019, the disjointness is stated at the concrete stored payload `combinatorI` (the case reductions it
consumes are proved there); the tags differ regardless of payload, but the symbolic-payload generalization waits
on the same weaken/subst commutation lemma deferred in #1019.

Everything is the raw `Conv` / `Step` relations; no typing derivation is consulted.

## Zero-axiom verification

The two distinguishing-handler reductions are each a single `Step.beta` whose contractum is rewritten by a named
`subst0`-typed `RawTerm.weaken_subst_singleton` cancellation, closed by `StepStar.refl`.  The headline composes
`Conv.app_cong` (×2, `ConvCongruence.lean`) over `hConv`, the two shipped case reductions chained with the
handler reductions via `StepStar.trans_compose`, `Conv.fromStepStar`/`Conv.trans`/`Conv.sym` to the common shape,
and the shipped `closedUniverseCode_not_conv_identity` for the final refutation.  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `handlerToUniverse = λx. (Type@0)` — a constant handler returning a universe code (head `gen_universeCode`).
Paired with `handlerToIdentity`, it makes the two `case` branches land on terms with DIFFERENT head generators. -/
def handlerToUniverse : RawTerm 0 :=
  lamCell combinatorDomainAnn (RawTerm.weaken (universeCodeCell LevelExpr.lzero UniverseFlag.standard))

/-- `handlerToIdentity = λx. (λy.y)` — a constant handler returning the identity λ (head `gen_lam`). -/
def handlerToIdentity : RawTerm 0 :=
  lamCell combinatorDomainAnn (RawTerm.weaken combinatorI)

/-- `handlerToUniverse I ↝* Type@0` — the constant handler discards its argument and yields the universe code,
the stored value re-emerging through the `subst0 (weaken ·) I = ·` cancellation. -/
theorem handlerToUniverse_app_I :
    StepStar (appCell handlerToUniverse combinatorI)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) := by
  have beta : Step (appCell handlerToUniverse combinatorI)
      (RawTerm.subst0 (RawTerm.weaken (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) combinatorI) :=
    HeadStep.beta.toStep
  have cancel :
      RawTerm.subst0 (RawTerm.weaken (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) combinatorI
        = universeCodeCell LevelExpr.lzero UniverseFlag.standard :=
    RawTerm.weaken_subst_singleton (universeCodeCell LevelExpr.lzero UniverseFlag.standard) combinatorI
  rw [cancel] at beta
  exact StepStar.trans beta (StepStar.refl _)

/-- `handlerToIdentity I ↝* I` — the dual constant handler yields the identity λ. -/
theorem handlerToIdentity_app_I :
    StepStar (appCell handlerToIdentity combinatorI) combinatorI := by
  have beta : Step (appCell handlerToIdentity combinatorI)
      (RawTerm.subst0 (RawTerm.weaken combinatorI) combinatorI) := HeadStep.beta.toStep
  have cancel : RawTerm.subst0 (RawTerm.weaken combinatorI) combinatorI = combinatorI :=
    RawTerm.weaken_subst_singleton combinatorI combinatorI
  rw [cancel] at beta
  exact StepStar.trans beta (StepStar.refl _)

/-- ★ **The two Church-sum injections are DISJOINT.**  `¬ Conv (inl I) (inr I)` — the coproduct faithfulness
capstone.  Were they convertible, applying both to `handlerToUniverse` and `handlerToIdentity` and reducing via
the shipped case selections (#1019) would force `Conv (Type@0) I`; but a universe code and the identity λ are
distinct closed normal forms with different head generators, so they are not convertible
(`closedUniverseCode_not_conv_identity`).  Coproducts are realized faithfully in the pure Π-fragment: the tags
are kept operationally apart, exactly as #983 keeps `churchTrue` and `churchFalse` apart. -/
theorem leftInjection_not_conv_rightInjection :
    ¬ Conv (leftInjection combinatorI) (rightInjection combinatorI) := by
  intro hConv
  have congApplied :
      Conv (appCell (appCell (leftInjection combinatorI) handlerToUniverse) handlerToIdentity)
           (appCell (appCell (rightInjection combinatorI) handlerToUniverse) handlerToIdentity) :=
    Conv.app_cong (Conv.app_cong hConv (Conv.refl handlerToUniverse)) (Conv.refl handlerToIdentity)
  have leftReduces :
      StepStar (appCell (appCell (leftInjection combinatorI) handlerToUniverse) handlerToIdentity)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
    StepStar.trans_compose (caseLeft_selectsLeftHandler handlerToUniverse handlerToIdentity)
      handlerToUniverse_app_I
  have rightReduces :
      StepStar (appCell (appCell (rightInjection combinatorI) handlerToUniverse) handlerToIdentity)
        combinatorI :=
    StepStar.trans_compose (caseRight_selectsRightHandler handlerToUniverse handlerToIdentity)
      handlerToIdentity_app_I
  have convValues : Conv (universeCodeCell LevelExpr.lzero UniverseFlag.standard) combinatorI :=
    Conv.trans (Conv.sym (Conv.fromStepStar leftReduces))
      (Conv.trans congApplied (Conv.fromStepStar rightReduces))
  exact closedUniverseCode_not_conv_identity LevelExpr.lzero UniverseFlag.standard convValues

/-- The symmetric corollary: `¬ Conv (inr I) (inl I)`, immediate from `leftInjection_not_conv_rightInjection` by
`Conv.sym`. -/
theorem rightInjection_not_conv_leftInjection :
    ¬ Conv (rightInjection combinatorI) (leftInjection combinatorI) :=
  fun hConv => leftInjection_not_conv_rightInjection (Conv.sym hConv)

end FX1Poly.Typed
