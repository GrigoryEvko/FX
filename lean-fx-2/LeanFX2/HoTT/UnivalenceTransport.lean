import LeanFX2.HoTT.UnivalenceFull

/-! # HoTT/UnivalenceTransport — `ua_β` computation rule at the meta level.

The full Voevodsky Univalence axiom comes packaged with a critical
computational rule:

```
ua_beta : transport (ua e) x = e.toFun x
```

i.e., transporting along a path-from-equivalence is the same as
applying the equivalence's forward function.  This is the rule that
makes Univalence COMPUTATIONAL — without it, `ua` is just a black-
box equality.

In lean-fx-2's strict zero-axiom regime, the FULL `ua_β` rule
requires either propext (banned) or kernel-level heterogeneous
Univalence reduction (Phase E in `kernel-sprint.md` D3.6).  This
file ships the rule at maximum strength derivable WITHOUT those
extensions:

* **Meta-level `ua_β` at the rfl-fragment**: when the equivalence is
  the canonical `Equiv.refl L`, transport along its `idToEquivMeta`
  image is the identity, matching `e.toFun = id`.  Constructive `rfl`.

* **Meta-level transport-via-toFun pointwise rule**: at any path
  `pathProof : LeftType = RightType`, transport along the path
  agrees with the forward function of `idToEquivMeta pathProof`.
  This IS the meta-level `ua_β` for the Lean-`Eq` flavor; it ships
  here because it's path-induction-provable.

* **Symmetric rule for `invFun` / inverse path**: same pattern on
  the inverse direction.

* **Composition law**: transport along `Eq.trans` decomposes via
  the `Equiv.trans` of the corresponding equivalences.

* **Rfl-fragment computation laws**: explicit `rfl`-tagged unfoldings
  for downstream definitional reasoning.

## Honest scope

The full `ua_β` for arbitrary equivalences (not just refl-fragment
ones) requires the `ua` direction `Equiv → Eq` at full generality —
which is the unprovable backward direction documented in
`HoTT/UnivalenceFull.lean` §7.  We ship the meta-level version on
Lean's `Eq` (where `ua` IS path-induction-derivable for "trivial"
paths but ships as `idToEquivMeta` rather than `ua` per se), plus
the rfl-fragment variant.

This file is FULLY constructive at zero axioms; every theorem ships
with a real body and audits clean. -/

namespace LeanFX2

universe metaLevel
universe leftLevel rightLevel middleLevel

/-! ## §1. Meta-level `ua_β` — transport equals equivalence-toFun.

The cornerstone rule of HoTT computational Univalence: at any path
between sorts, transport along the path coincides with the forward
function of the corresponding equivalence under `idToEquivMeta`. -/

/-- **Meta-level `ua_β`**: transport along `pathProof` equals the
forward function `(idToEquivMeta pathProof).toFun`.  Path-induction:
at `rfl`, both sides reduce to the identity function. -/
theorem Univalence.ua_beta_meta
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (leftValue : LeftType) :
    pathProof ▸ leftValue
      = (Univalence.idToEquivMeta pathProof).toFun leftValue := by
  cases pathProof
  rfl

/-- **`ua_β` at `rfl`**: at `Eq.refl LeftType`, transport is the
identity, and the corresponding equivalence's forward function is
also the identity.  Definitional `rfl`. -/
theorem Univalence.ua_beta_meta_refl
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Eq.refl LeftType) ▸ leftValue
      = (Univalence.idToEquivMeta (Eq.refl LeftType)).toFun leftValue := rfl

/-- **`ua_β` at `rfl` is the identity (LHS unfolding)**: explicit
`rfl`-tagged unfolding for downstream definitional reasoning. -/
theorem Univalence.ua_beta_meta_refl_lhs
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Eq.refl LeftType) ▸ leftValue = leftValue := rfl

/-- **`ua_β` at `rfl` is the identity (RHS unfolding)**: explicit
`rfl`-tagged unfolding showing the RHS reduces to the input. -/
theorem Univalence.ua_beta_meta_refl_rhs
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Univalence.idToEquivMeta (Eq.refl LeftType)).toFun leftValue
      = leftValue := rfl

/-! ## §2. Inverse `ua_β` — transport along symm equals invFun. -/

/-- **Meta-level inverse `ua_β`**: transport along `Eq.symm pathProof`
equals the inverse function `(idToEquivMeta pathProof).invFun`.  At
the rfl path, both reduce to the identity. -/
theorem Univalence.ua_beta_meta_symm
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (rightValue : RightType) :
    (Eq.symm pathProof) ▸ rightValue
      = (Univalence.idToEquivMeta pathProof).invFun rightValue := by
  cases pathProof
  rfl

/-- **Inverse `ua_β` at `rfl`** (constant case): `Eq.symm rfl ▸ x = x`
and `(idToEquivMeta rfl).invFun x = x`.  Definitional `rfl`. -/
theorem Univalence.ua_beta_meta_symm_refl
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Eq.symm (Eq.refl LeftType)) ▸ leftValue
      = (Univalence.idToEquivMeta (Eq.refl LeftType)).invFun leftValue := rfl

/-! ## §3. Composition law — transport along `Eq.trans`. -/

/-- **Meta-level transport-trans**: transport along `Eq.trans p q`
equals composing transport along `p` with transport along `q` (in
order).  Path-induction on `p` collapses to `q ▸ ...` then `cases q`
discharges. -/
theorem Univalence.transport_trans_meta
    {LeftType : Sort metaLevel}
    {MiddleType : Sort metaLevel}
    {RightType : Sort metaLevel}
    (firstEquality  : LeftType = MiddleType)
    (secondEquality : MiddleType = RightType)
    (leftValue : LeftType) :
    (Eq.trans firstEquality secondEquality) ▸ leftValue
      = secondEquality ▸ (firstEquality ▸ leftValue) := by
  cases firstEquality
  cases secondEquality
  rfl

/-- **Composition law via `idToEquivMeta`**: transport along
`Eq.trans p q` agrees with the forward function of
`Equiv.trans (idToEquivMeta p) (idToEquivMeta q)`.  This is the
composition law for the Univalence forward map at the
transport/equiv level. -/
theorem Univalence.ua_beta_meta_trans
    {LeftType : Sort metaLevel}
    {MiddleType : Sort metaLevel}
    {RightType : Sort metaLevel}
    (firstEquality  : LeftType = MiddleType)
    (secondEquality : MiddleType = RightType)
    (leftValue : LeftType) :
    (Eq.trans firstEquality secondEquality) ▸ leftValue
      = (Equiv.trans (Univalence.idToEquivMeta firstEquality)
                     (Univalence.idToEquivMeta secondEquality)).toFun leftValue := by
  cases firstEquality
  cases secondEquality
  rfl

/-! ## §4. Round-trip computation laws.

Beyond the toFun/invFun direction-specific rules, the round-trip
identities `e.invFun (e.toFun x) = x` and `e.toFun (e.invFun y) = y`
combine with `ua_β` to give explicit transport-round-trip rules. -/

/-- **Transport round trip via toFun-invFun**: transport along
`pathProof` then `Eq.symm pathProof` is the identity.  This combines
`ua_β` (forward direction) with the equivalence's `leftInv`. -/
theorem Univalence.transport_round_trip_toFun_invFun
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (leftValue : LeftType) :
    (Eq.symm pathProof) ▸ (pathProof ▸ leftValue) = leftValue := by
  cases pathProof
  rfl

/-- **Transport round trip via invFun-toFun**: transport along
`Eq.symm pathProof` then `pathProof` is the identity. -/
theorem Univalence.transport_round_trip_invFun_toFun
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (rightValue : RightType) :
    pathProof ▸ ((Eq.symm pathProof) ▸ rightValue) = rightValue := by
  cases pathProof
  rfl

/-! ## §5. Equivalence-pinning rule.

When the equivalence IS pinned to be `Equiv.refl _`, transport
along the corresponding path is the identity.  This is the rfl-
fragment computation rule that pairs with the kernel `Step.eqType`
reduction.  -/

/-- **Refl-equiv transport rule**: at the canonical refl-equiv,
transport via `idToEquivMeta` is the identity function (definitionally
a `rfl`-tagged result). -/
theorem Univalence.transport_via_reflEquiv
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Univalence.equivToIdMetaAtRefl LeftType (Equiv.refl LeftType)) ▸ leftValue
      = (Equiv.refl LeftType).toFun leftValue := rfl

/-- **Refl-equiv transport unfolds to identity**: spelled-out as a
single `rfl` fact so downstream proofs can chain through this lemma
without re-deriving the unfolding. -/
theorem Univalence.transport_via_reflEquiv_id
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Univalence.equivToIdMetaAtRefl LeftType (Equiv.refl LeftType)) ▸ leftValue
      = leftValue := rfl

/-! ## §6. `ua_β` in the canonical `Equiv` sense.

Combining everything: at any `someEquiv : Equiv L R` constructed via
`idToEquivMeta pathProof`, the toFun + transport agree (this IS
`ua_β`); same for invFun + transport-symm. -/

/-- **`ua_β` for forward function via toFun**: the toFun field of
`idToEquivMeta pathProof` equals (pointwise) transport along
`pathProof`.  Already shipped via `idToEquivMeta_toFun_eq_transport`
in `HoTT/Univalence.lean`; this re-states it for symmetric
presentation here. -/
theorem Univalence.ua_beta_toFun_pointwise
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (leftValue : LeftType) :
    (Univalence.idToEquivMeta pathProof).toFun leftValue
      = pathProof ▸ leftValue := by
  cases pathProof
  rfl

/-- **`ua_β` for inverse function via invFun**: the invFun field of
`idToEquivMeta pathProof` equals (pointwise) transport along
`Eq.symm pathProof`.  Companion to `ua_beta_toFun_pointwise`. -/
theorem Univalence.ua_beta_invFun_pointwise
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (rightValue : RightType) :
    (Univalence.idToEquivMeta pathProof).invFun rightValue
      = (Eq.symm pathProof) ▸ rightValue := by
  cases pathProof
  rfl

/-! ## §7. Equivalence-via-toFun computation: the canonical "ua-as-
transport" presentation.

Voevodsky's full Univalence makes `ua e` a path; when paired with
`ua_β`, transport along `ua e` IS `e.toFun`.  Below: the meta-level
analog — for any path, transport along it is determined by the
equivalence's forward function under `idToEquivMeta`. -/

/-- **Transport-as-equiv-application**: at any path between sorts,
transport along the path equals the equivalence-application of
`idToEquivMeta` of the path.  This is the strongest meta-level
statement of `ua_β` shippable at zero axioms. -/
theorem Univalence.transport_as_equivApp
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (leftValue : LeftType) :
    pathProof ▸ leftValue
      = (Univalence.idToEquivMeta pathProof).toFun leftValue :=
  Univalence.ua_beta_meta pathProof leftValue

/-- **Inverse transport-as-equiv-application**: companion using
`invFun`. -/
theorem Univalence.transport_symm_as_equivApp_invFun
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (rightValue : RightType) :
    (Eq.symm pathProof) ▸ rightValue
      = (Univalence.idToEquivMeta pathProof).invFun rightValue :=
  Univalence.ua_beta_meta_symm pathProof rightValue

/-! ## §8. Trans-via-Equiv-trans pointwise computation.

The composition law `transport (p · q) = transport q ∘ transport p`
specialises through `idToEquivMeta` to a pointwise statement about
`Equiv.trans`'s toFun. -/

/-- **Composition rule pointwise**: `(idToEquivMeta (Eq.trans p q)).toFun`
applied to `x` agrees with `(idToEquivMeta q).toFun
((idToEquivMeta p).toFun x)`.  Already shipped in
`HoTT/UnivalenceFull.lean` as
`idToEquivMeta_trans_toFun_pointwise`; re-stated here in this file's
canonical form for users navigating from the transport perspective. -/
theorem Univalence.idToEquivMeta_trans_toFun_via_transport
    {LeftType : Sort metaLevel}
    {MiddleType : Sort metaLevel}
    {RightType : Sort metaLevel}
    (firstEquality  : LeftType = MiddleType)
    (secondEquality : MiddleType = RightType)
    (leftValue : LeftType) :
    (Univalence.idToEquivMeta (Eq.trans firstEquality secondEquality)).toFun leftValue
      = secondEquality ▸ (firstEquality ▸ leftValue) := by
  cases firstEquality
  cases secondEquality
  rfl

end LeanFX2
