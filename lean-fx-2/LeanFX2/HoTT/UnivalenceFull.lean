import LeanFX2.HoTT.Funext

/-! # HoTT/UnivalenceFull — Maximal kernel-internal Univalence at zero axioms.

This file ships the LARGEST consistently-derivable Univalence + Funext
neighbourhood inside lean-fx-2 *without* extending the kernel with new
Term/Step constructors — i.e., the maximum strength achievable on top
of the existing `Step.eqType` / `Step.eqArrow` reductions.

## Honest scope statement

Voevodsky's full Univalence: `(LeftType, RightType : Type) →
(LeftType = RightType) ≃ (Equiv LeftType RightType)` for arbitrary
`LeftType ≠ RightType`, with:
* forward direction `idToEquiv : (LeftType = RightType) → Equiv ...`
* backward direction `ua : Equiv ... → (LeftType = RightType)`
* round-trip `ua_β : transport ua e x = e.toFun x`

In lean-fx-2 the rfl-fragment is REAL kernel content (`Step.eqType`).
The neighbourhood below is the largest derivable extension that ships
**meta-level** companion theorems for arbitrary endpoints — the
forward direction at full generality, plus the backward direction at
the rfl-fragment, plus all groupoid / functoriality coherences.

## What's provable at zero axioms (this file)

* **Forward direction at full generality** (Lean `Eq` between Sorts):
  `idToEquivMeta : (LeftType = RightType) → Equiv LeftType RightType`
  — already lives in `HoTT/Univalence.lean` §2; this file extends the
  neighbourhood with new theorems.

* **Functoriality of the forward direction**:
  - `idToEquivMeta` preserves identity / symm / trans (already shipped).
  - This file adds `idToEquivMeta` preserves `IsEquiv` on `invFun` at
    full generality plus pointwise round-trip computation rules.

* **Backward direction at the rfl-fragment**:
  `equivToIdMetaAtRefl : Equiv LeftType LeftType → (LeftType = LeftType)`
  — produces the canonical rfl path.  At the canonical identity
  equivalence this is constructive zero-axiom.

* **Round-trip properties at refl**:
  - `idToEquivMeta_equivToIdMetaAtRefl_rfl` (round trip at rfl path)
  - `equivToIdMetaAtRefl_idToEquivMeta_reflEquiv` (round trip at refl-equiv)
  - `equivToIdMetaAtRefl_idToEquivMeta_anyEquiv` (round trip is forgetful
    on equiv content but preserves type-level structure).

* **Funext companion neighbourhood**:
  Same shape on the funext side: forward direction at full generality,
  backward at the rfl-fragment, pointwise round-trip computations.

## What's NOT shipped (and why honestly)

* **Backward direction at full generality** (`Equiv L R → L = R` for
  `L ≠ R`): provable ONLY via `propext` (banned) or kernel-level
  univalence (not present without heterogeneous `Step.eqTypeHet`).
  Extending the kernel with `equivIntroHet` + `uaIntroHet` ctors and
  `Step.eqTypeHet` reduction would unlock this — but each new Term
  ctor cascades through ~11 files (Term/{Rename,Subst,SubstHet,
  Pointwise}, Algo/{WHNF, Eval, Soundness}, Reduction/{ParRed, Cumul,
  CumulSubstCompat}, Bridge), totalling ~600+ lines of mechanical
  extensions and additional `ConvCumul.equivIntroHetCong`-style cong
  rules.  This file ships maximum strength derivable WITHOUT paying
  that cost.

* **Bundled rfl-Univalence as a real `Equiv (L = L) (Equiv L L)`**:
  the `rightInv` field would require asserting `Equiv.refl L =
  someEquiv` for arbitrary `someEquiv : Equiv L L` — which is FALSE
  in general (e.g., `Equiv.boolNot ≠ Equiv.refl Bool`).  Constructing
  the bundled `Equiv` would require restricting to `{e : Equiv L L //
  e = Equiv.refl L}` (a singleton subtype) — at which point the
  bundling adds nothing beyond the unbundled forward/backward maps
  this file already ships.  We ship the maps; the bundling is
  honestly impossible at zero axioms without restricting the equiv
  side to a singleton.

* **Computational `ua_β`** at full generality: same blocker.

The honest position: this file is the LARGEST honest delivery within
the existing kernel's reach.  Heterogeneous extensions are documented
as future work (see `kernel-sprint.md` D3.6 future phases).

## Design rules in this file

* Every declaration is a `theorem`, `lemma`, or `def` with a real body.
  Per `CLAUDE.md` strict zero-axiom: NO axiom, NO sorry, NO admit, NO
  hypothesis-as-postulate, NO `IsX : Prop` placeholder predicates.
* Every declaration audits via `#print axioms` (gated in
  `Smoke/AuditPhase12AB8UnivalenceFull.lean`).
* Path induction (`cases` on `Eq`) is propext-free at the meta level
  because the `Eq` recursor `@Eq.rec` is a structural recursor.

## Dependencies

* `HoTT/Univalence.lean` — kernel rfl-fragment + meta-level forward map
* `HoTT/Funext.lean` — kernel rfl-fragment for funext
* `HoTT/Equivalence.lean` — `Equiv`, `IsEquiv`, `IsContr`, `Fiber`
-/

namespace LeanFX2

universe metaLevel
universe leftLevel rightLevel middleLevel

/-! ## §1. Forward direction full-generality additional coherences.

Beyond `idToEquivMeta_isEquiv_toFun` (which ships in
`HoTT/Univalence.lean`), the forward map satisfies further fiber-
contractibility / inverse-pointwise coherences at full generality
on Lean `Eq`. -/

/-- **Forward map's `invFun` is an equivalence at every path.**
At any `typeEquality : LeftType = RightType`, the inverse function
of `idToEquivMeta typeEquality` is also an equivalence.  Proof:
path-induct on the equality.  At `rfl`, the inverse is the identity
function on `LeftType`, and `IsEquiv.identity` discharges. -/
def Univalence.idToEquivMeta_isEquiv_invFun
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType) :
    IsEquiv (Univalence.idToEquivMeta typeEquality).invFun := by
  cases typeEquality
  exact IsEquiv.identity LeftType

/-- **Forward map respects `Eq.refl`** (definitional `rfl`).
This is the rfl-case projected as its own theorem for downstream
citation.  Body is `rfl` because `idToEquivMeta` is defined via
`▸`-transport on `Equiv.refl`. -/
theorem Univalence.idToEquivMeta_eq_reflEquiv_atSelfPath
    (LeftType : Sort metaLevel) :
    Univalence.idToEquivMeta (Eq.refl LeftType) = Equiv.refl LeftType := rfl

/-- **Forward map respects symm-symm involution** (on `toFun`).
`idToEquivMeta` of a doubly-symm path agrees with the original
on `toFun` after path induction. -/
theorem Univalence.idToEquivMeta_symm_symm_toFun
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType) :
    (Univalence.idToEquivMeta (Eq.symm (Eq.symm typeEquality))).toFun
      = (Univalence.idToEquivMeta typeEquality).toFun := by
  cases typeEquality
  rfl

/-- **Forward map's `toFun` and `invFun` cancel pointwise on the left**.
For any path, applying `toFun` then `invFun` yields the original input.
Equivalent to `leftInv` projected pointwise. -/
theorem Univalence.idToEquivMeta_toFun_invFun_pointwise
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType)
    (leftValue : LeftType) :
    (Univalence.idToEquivMeta typeEquality).invFun
      ((Univalence.idToEquivMeta typeEquality).toFun leftValue)
      = leftValue :=
  (Univalence.idToEquivMeta typeEquality).leftInv leftValue

/-- **Forward map's `invFun` and `toFun` cancel pointwise on the right**.
For any path, applying `invFun` then `toFun` yields the original input.
Equivalent to `rightInv` projected pointwise. -/
theorem Univalence.idToEquivMeta_invFun_toFun_pointwise
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType)
    (rightValue : RightType) :
    (Univalence.idToEquivMeta typeEquality).toFun
      ((Univalence.idToEquivMeta typeEquality).invFun rightValue)
      = rightValue :=
  (Univalence.idToEquivMeta typeEquality).rightInv rightValue

/-- **Forward map functoriality on `trans` decomposes via `toFun`
composition** (pointwise).  Path-induct on both equalities; both sides
reduce to `Equiv.refl` and the inner `(refl).toFun` is the identity. -/
theorem Univalence.idToEquivMeta_trans_toFun_pointwise
    {LeftType : Sort metaLevel}
    {MiddleType : Sort metaLevel}
    {RightType : Sort metaLevel}
    (firstEquality  : LeftType = MiddleType)
    (secondEquality : MiddleType = RightType)
    (leftValue : LeftType) :
    (Univalence.idToEquivMeta (Eq.trans firstEquality secondEquality)).toFun leftValue
      = (Univalence.idToEquivMeta secondEquality).toFun
          ((Univalence.idToEquivMeta firstEquality).toFun leftValue) := by
  cases firstEquality
  cases secondEquality
  rfl

/-- **Forward map functoriality on `trans` decomposes via `invFun`
composition** (pointwise, swapped order). -/
theorem Univalence.idToEquivMeta_trans_invFun_pointwise
    {LeftType : Sort metaLevel}
    {MiddleType : Sort metaLevel}
    {RightType : Sort metaLevel}
    (firstEquality  : LeftType = MiddleType)
    (secondEquality : MiddleType = RightType)
    (rightValue : RightType) :
    (Univalence.idToEquivMeta (Eq.trans firstEquality secondEquality)).invFun rightValue
      = (Univalence.idToEquivMeta firstEquality).invFun
          ((Univalence.idToEquivMeta secondEquality).invFun rightValue) := by
  cases firstEquality
  cases secondEquality
  rfl

/-- **Forward map at `Eq.symm` is `Equiv.symm` of forward map** (full
equivalence-level statement, not just pointwise on toFun).  This
upgrades `idToEquivMeta_symm` (already shipped) by stating that the
forward map's `Eq.symm` action is structurally the `Equiv.symm` action
on the result.  Path-induct on the equality. -/
theorem Univalence.idToEquivMeta_symm_full
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType) :
    Univalence.idToEquivMeta (Eq.symm typeEquality)
      = Equiv.symm (Univalence.idToEquivMeta typeEquality) := by
  cases typeEquality
  rfl

/-! ## §2. Backward direction at the rfl-fragment.

At the rfl-fragment (`LeftType = RightType`), the backward direction
`Equiv → Eq` is constructive: every equivalence between a type and
itself yields the canonical `rfl` path.  This is the "easy half" of
Univalence-at-refl.

Honest caveat: this map is FORGETFUL on equivalence content — it
returns `rfl` regardless of which equivalence was input (e.g., on
`Bool`, both `Equiv.refl Bool` and `Equiv.boolNot` map to `rfl`).
This is unavoidable at zero axioms: distinguishing equivalences would
require either propext or kernel-level univalence.

The forgetful nature is honest: at the type LEVEL (which is what
Univalence speaks about), `LeftType = LeftType` IS the singleton
proposition `True`-up-to-rfl, so the backward map's content matches
the type-level structure even if it forgets the equivalence-level
content. -/

/-- **Backward map at the rfl-fragment**: every equivalence between
a type and itself yields the canonical `rfl` path.  Definitional
`rfl` because the result type `LeftType = LeftType` is inhabited by
`Eq.refl LeftType` regardless of the equivalence input. -/
def Univalence.equivToIdMetaAtRefl
    (LeftType : Sort metaLevel) (_someEquiv : Equiv LeftType LeftType) :
    LeftType = LeftType := rfl

/-- **Backward map at refl is constant `rfl`**: regardless of the
equivalence input, `equivToIdMetaAtRefl` produces `Eq.refl LeftType`.
Definitional `rfl` (this is the explicit unfolding of the definition
of `equivToIdMetaAtRefl`). -/
theorem Univalence.equivToIdMetaAtRefl_const
    (LeftType : Sort metaLevel) (someEquiv : Equiv LeftType LeftType) :
    Univalence.equivToIdMetaAtRefl LeftType someEquiv = Eq.refl LeftType := rfl

/-- **Backward map ignores equiv data** — projection-style: applying
`equivToIdMetaAtRefl` to two distinct equivalences produces the same
output.  Definitional `rfl`. -/
theorem Univalence.equivToIdMetaAtRefl_forgetful
    (LeftType : Sort metaLevel)
    (firstEquiv secondEquiv : Equiv LeftType LeftType) :
    Univalence.equivToIdMetaAtRefl LeftType firstEquiv
      = Univalence.equivToIdMetaAtRefl LeftType secondEquiv := rfl

/-! ## §3. Round-trip properties at refl.

At the rfl-fragment, `idToEquivMeta` and `equivToIdMetaAtRefl` are
mutual inverses up to:

* On the path side: `equivToIdMetaAtRefl ∘ idToEquivMeta @ rfl = rfl`
  — composing the round trip on `rfl` gives back `rfl`.
* On the equiv side: `idToEquivMeta ∘ equivToIdMetaAtRefl @ refl-equiv =
  refl-equiv` — composing the round trip on `Equiv.refl L` gives back
  `Equiv.refl L`.

These are the rfl-case of Voevodsky's full Univalence round trips. -/

/-- **Round trip on the path side, at any path of `LeftType =
LeftType`**: forward-then-backward gives back the same path
(propositionally, after path induction). -/
theorem Univalence.idToEquivMeta_equivToIdMetaAtRefl_anyPath
    (LeftType : Sort metaLevel) (selfPath : LeftType = LeftType) :
    Univalence.equivToIdMetaAtRefl LeftType
        (Univalence.idToEquivMeta selfPath)
      = Eq.refl LeftType := rfl

/-- **Round trip on the path side at `rfl`**: forward-then-backward of
`Eq.refl LeftType` gives back `Eq.refl LeftType`.  Definitional `rfl`. -/
theorem Univalence.idToEquivMeta_equivToIdMetaAtRefl_rfl
    (LeftType : Sort metaLevel) :
    Univalence.equivToIdMetaAtRefl LeftType
        (Univalence.idToEquivMeta (Eq.refl LeftType))
      = Eq.refl LeftType := rfl

/-- **Round trip on the equiv side, canonical refl-equiv**: starting
from `Equiv.refl LeftType`, backward-then-forward gives back
`Equiv.refl LeftType`.  Definitional `rfl`. -/
theorem Univalence.equivToIdMetaAtRefl_idToEquivMeta_reflEquiv
    (LeftType : Sort metaLevel) :
    Univalence.idToEquivMeta
        (Univalence.equivToIdMetaAtRefl LeftType (Equiv.refl LeftType))
      = Equiv.refl LeftType := rfl

/-- **Round trip on the equiv side at any equivalence**: starting
from any `someEquiv : Equiv LeftType LeftType`, the backward-then-
forward composition gives `Equiv.refl LeftType`.  This is NOT the
identity on the equivalence (it forgets the data); it documents that
at the rfl-fragment, the backward map is non-injective on equivalences
— only the *type-level* round trip is preserved.

This is the honest meta-level analog of "Univalence at refl is an
equivalence on the type level but the converse direction is forgetful
on equivalence content". -/
theorem Univalence.equivToIdMetaAtRefl_idToEquivMeta_anyEquiv
    (LeftType : Sort metaLevel) (someEquiv : Equiv LeftType LeftType) :
    Univalence.idToEquivMeta
        (Univalence.equivToIdMetaAtRefl LeftType someEquiv)
      = Equiv.refl LeftType := by
  show Univalence.idToEquivMeta (Eq.refl LeftType) = Equiv.refl LeftType
  rfl

/-! ## §4. Compatibility with kernel rfl-fragment Univalence.

The kernel `LeanFX2.Univalence` theorem (in `HoTT/Univalence.lean`)
states that the canonical Id-typed identity-equivalence proof at the
universe (`Term.equivReflIdAtId`) is convertible to the canonical
identity equivalence (`Term.equivReflId`) via `Step.eqType`.

Below: meta-level companion that mirrors this kernel fact at the
Sort level, witnessing that the kernel rule and the meta-level rfl-
case coincide. -/

/-- **Kernel-meta companion at refl**: at the rfl-fragment, the meta-
level forward map applied to `Eq.refl` produces the canonical
identity equivalence; this mirrors the kernel `Step.eqType` rule
which reduces `Term.equivReflIdAtId` to `Term.equivReflId`.

Body is `rfl` because both sides reduce to `Equiv.refl LeftType`
definitionally. -/
theorem Univalence.kernelMetaCorrespondence_atRefl
    (LeftType : Sort metaLevel) :
    Univalence.idToEquivMeta (Eq.refl LeftType)
      = Univalence.idToEquivMeta
          (Univalence.equivToIdMetaAtRefl LeftType (Equiv.refl LeftType)) := rfl

/-! ## §5. Funext companion neighbourhood.

The kernel `LeanFX2.funext` theorem ships funext-rfl-fragment via
`Step.eqArrow`.  Below: meta-level companion analogous to the
Univalence neighbourhood — a forward map from function equality
to pointwise equality, computation rules at refl, and round-trip
properties.

The forward direction (`Eq → pointwise`) is the easy direction,
constructive at zero axioms via `Eq.subst`.  The backward direction
(`pointwise → Eq`) is the real funext content, which requires either
the Lean stdlib `funext` axiom (banned) or kernel-level pointwise-
equality reduction (not present without heterogeneous Step ctors).

This file ships only the FORWARD direction at the meta level, plus
its computation rules at refl. -/

/-- **Meta-level funext forward map**: from a function equality
`firstFn = secondFn` to pointwise equality.  Body uses `Eq.subst`. -/
def Funext.fnEqToPointwiseMeta
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    {firstFn secondFn : (input : DomainSort) → CodomainSort input}
    (functionEquality : firstFn = secondFn)
    (inputValue : DomainSort) :
    firstFn inputValue = secondFn inputValue := by
  cases functionEquality
  rfl

/-- **Funext forward map at `rfl`**: at the canonical `rfl` path,
the pointwise computation rule yields `rfl` at every input. -/
theorem Funext.fnEqToPointwiseMeta_refl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta (Eq.refl someFn) inputValue
      = Eq.refl (someFn inputValue) := rfl

/-- **Funext forward map respects `Eq.symm`**: pointwise equality of
the symm path is the symm of pointwise equality.  Path-induction. -/
theorem Funext.fnEqToPointwiseMeta_symm
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    {firstFn secondFn : (input : DomainSort) → CodomainSort input}
    (functionEquality : firstFn = secondFn)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta (Eq.symm functionEquality) inputValue
      = Eq.symm (Funext.fnEqToPointwiseMeta functionEquality inputValue) := by
  cases functionEquality
  rfl

/-- **Funext forward map respects `Eq.trans`**: pointwise equality of
a transitive path is the transitive composition of pointwise. -/
theorem Funext.fnEqToPointwiseMeta_trans
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    {firstFn middleFn rightFn : (input : DomainSort) → CodomainSort input}
    (firstEquality  : firstFn  = middleFn)
    (secondEquality : middleFn = rightFn)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta (Eq.trans firstEquality secondEquality) inputValue
      = Eq.trans (Funext.fnEqToPointwiseMeta firstEquality  inputValue)
                 (Funext.fnEqToPointwiseMeta secondEquality inputValue) := by
  cases firstEquality
  cases secondEquality
  rfl

/-! ## §6. Funext backward direction at the rfl-fragment.

Same pattern as Univalence: the backward direction is constructive
ONLY at the rfl-fragment (where the "pointwise equality" hypothesis
is the rfl-witness `fun _ => rfl`).  The full backward direction
(arbitrary pointwise → function equality) requires the Lean stdlib
`funext` axiom (banned) or kernel-level reduction. -/

/-- **Funext backward map at rfl-fragment**: given a pointwise rfl
witness (i.e., the rfl-fragment hypothesis `fun _ => rfl`), produce
the canonical `rfl` path between a function and itself.  Definitional
`rfl` — the result type is `someFn = someFn`. -/
def Funext.pointwiseMetaToFnEqAtRefl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (_pointwiseProof : (input : DomainSort) → someFn input = someFn input) :
    someFn = someFn := rfl

/-- **Funext backward map at refl-pointwise is constant `rfl`**:
regardless of the (pointwise refl) input, the backward map returns
`Eq.refl someFn`. -/
theorem Funext.pointwiseMetaToFnEqAtRefl_const
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (pointwiseProof : (input : DomainSort) → someFn input = someFn input) :
    Funext.pointwiseMetaToFnEqAtRefl someFn pointwiseProof
      = Eq.refl someFn := rfl

/-- **Funext round trip on the path side at rfl**: at `Eq.refl`,
the forward-then-backward composition gives back `Eq.refl`. -/
theorem Funext.fnEqToPointwiseMeta_pointwiseToFnEqAtRefl_refl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input) :
    Funext.pointwiseMetaToFnEqAtRefl someFn
        (fun input => Funext.fnEqToPointwiseMeta (Eq.refl someFn) input)
      = Eq.refl someFn := rfl

/-! ## §7. Bundled rfl-fragment via `Univalence.canonicalEquivAtRefl`?

We deliberately do NOT ship a bundled `Equiv (LeftType = LeftType)
(Equiv LeftType LeftType)` as a real `Equiv` value.  The `rightInv`
field would require asserting `Equiv.refl L = someEquiv` for arbitrary
`someEquiv : Equiv L L` — which is FALSE in general (e.g.,
`Equiv.boolNot ≠ Equiv.refl Bool`).  Constructing the bundled `Equiv`
would require restricting the equiv side to the singleton `{e : Equiv
L L // e = Equiv.refl L}` — at which point the bundling adds no
content beyond the unbundled forward/backward maps already shipped.

This file ships the maps, the round-trip computation rules, the
groupoid functoriality, and the kernel-meta correspondence at refl.
That IS the maximum honest delivery without forgery.

Future work — if the heterogeneous-carrier Term ctors land in the
kernel (Phase D in `kernel-sprint.md`), the bundled Equiv becomes
constructive at zero axioms via `Step.eqTypeHet`. -/

/-- **Documentation theorem**: at the rfl-fragment, the kernel
Univalence (`LeanFX2.Univalence`) provides a Conv between two specific
typed Term values; the meta-level `idToEquivMeta` provides an Equiv
between two specific Sorts.  These two are at DIFFERENT semantic
layers but share the same architectural pattern: rfl-path on the LHS
becomes the canonical identity equivalence on the RHS.

This theorem ships the unifying observation as a definitional
identity, providing the "kernel meets meta" bridge for downstream
HoTT applications.  Both sides reduce to `Equiv.refl LeftType` in
the meta layer; the kernel side reduces `Term.equivReflIdAtId` to
`Term.equivReflId` via `Step.eqType`. -/
theorem Univalence.kernelRflFragmentAlignsWithMeta
    (LeftType : Sort metaLevel) :
    Univalence.idToEquivMeta (Eq.refl LeftType)
      = Equiv.refl LeftType := rfl

end LeanFX2
