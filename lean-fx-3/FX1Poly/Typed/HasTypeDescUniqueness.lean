import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.HasTypeInversion

/-! # FX1Poly/Typed/HasTypeDescUniqueness — uniqueness of typing (P7) for the
    description engine.

polycell.md §11.8.5 P7 ("uniqueness of typing"): any two classifiers a cell receives
are convertible.  P7 disciplines the design (it makes `infer` well-defined) and is
consumed by the typechecker's conv-check and by canonicity.

## What is intrinsic here, and what is not (honest scope)

`HasTypeDesc.uniqueness` is a recursion on `HasTypeDesc` ITSELF (the propext-free
term-mode `match`, since the mutual `HasTypeDesc` rejects `induction`).  Its `var` /
`universeFormation` arms use the INTRINSIC leaf inversions and its `conv` arm recurses
INTRINSICALLY on the premise — those three arms are genuinely DECOUPLED from the
bespoke `HasType` (they would survive a new `gen` row).

The `genFormation` arm is, for now, the ONE coupled arm: it settles the two classifiers
through the `⟺` equivalence (`HasTypeDesc.toHasType` into the verified bespoke
`HasType.uniqueness`).  The fully intrinsic `genFormation` requires a MUTUAL
`uniqueness`/telescope-agreement recursion (the `HasTypeDesc.toHasType` /
`DescTelescope.toHasTypeTelescope` shape) so the formation children recurse into the
intrinsic uniqueness directly; two Lean-engineering obstacles block the naive form and
are the decouple's next target:

* the mutual structural-recursion inference fails to eliminate the
  `uniqueness → telescopeAgree premises` cross-call (the `scope` vs `scope + 0`
  telescope index needs the careful phrasing of the shipped soundness pair); and
* deconstructing the SECOND telescope (whose children index is FORCED to
  `childCons head rest`, and whose `flag` reuses the goal's implicit) makes `cases` /
  `rcases` field alignment unpredictable — it wants the equation-motive recipe (free
  children + threaded `children = childCons …`), not a direct `cases`.

On the CURRENT fragment (`HasTypeDesc ⟺ HasType`) the bespoke-routed `genFormation`
arm is sound and total; only the formation SPINE stays coupled, the leaf/conv arms are
intrinsic.

## Zero-axiom

Term-mode recursion on `HasTypeDesc` + the shipped propext-free leaf inversions + the
verified `Conv.trans_of_typedMiddle` / `HasType.uniqueness` / `HasTypeDesc.toHasType`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Uniqueness of typing (P7).**  Any two classifiers a description-engine cell
receives are convertible.  Recursion on the FIRST derivation: `var` /
`universeFormation` invert the SECOND derivation (INTRINSIC leaf inversions) and `.sym`;
`conv` forwards its premise's recursive result through the converted classifier (a type
by validity — a legal `Conv.trans_of_typedMiddle` middle); `genFormation` settles the
two classifiers through the `⟺` equivalence into the verified bespoke
`HasType.uniqueness` (the intrinsic formation arm awaits the mutual telescope-agreement
recursion — see the module docstring). -/
theorem HasTypeDesc.uniqueness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject firstClassifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject firstClassifier)
    (wellFormed : WfContext context) :
    ∀ {secondClassifier : RawTerm scope},
      HasTypeDesc profile context subject secondClassifier →
        Conv firstClassifier secondClassifier :=
  match derivation with
  | .var _context _index => fun secondDerivation =>
      (HasTypeDesc.inversionVariable secondDerivation wellFormed).sym
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      fun secondDerivation =>
        Conv.trans_of_typedMiddle
          (HasType.classifierIsType wellFormed (HasTypeDesc.toHasType typedPremise))
          converts.sym
          (HasTypeDesc.uniqueness typedPremise wellFormed secondDerivation)
  | .universeFormation _context _levelExpr _flag => fun secondDerivation =>
      (HasTypeDesc.inversionUniverseCode secondDerivation wellFormed).sym
  | .genFormation context generator payload children levels flag rule
      isFormation premises => fun secondDerivation =>
      HasType.uniqueness wellFormed
        (HasTypeDesc.toHasType
          (.genFormation context generator payload children levels flag rule
            isFormation premises))
        (HasTypeDesc.toHasType secondDerivation)

end FX1Poly.Typed
