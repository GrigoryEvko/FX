import LeanFX2.HoTT.UnivalenceTransport

/-! # Smoke/AuditUnivalenceTransport — Audit gates for HoTT/UnivalenceTransport.

Verifies every shipped declaration in `HoTT/UnivalenceTransport.lean`
audits zero-axiom under `#print axioms`.

## Scope

* **§1 ua_β cornerstone** (4 decls):
  - `ua_beta_meta`
  - `ua_beta_meta_refl`
  - `ua_beta_meta_refl_lhs`
  - `ua_beta_meta_refl_rhs`

* **§2 inverse ua_β** (2 decls):
  - `ua_beta_meta_symm`
  - `ua_beta_meta_symm_refl`

* **§3 composition law** (2 decls):
  - `transport_trans_meta`
  - `ua_beta_meta_trans`

* **§4 round-trip computation laws** (2 decls):
  - `transport_round_trip_toFun_invFun`
  - `transport_round_trip_invFun_toFun`

* **§5 equivalence-pinning rule** (2 decls):
  - `transport_via_reflEquiv`
  - `transport_via_reflEquiv_id`

* **§6 ua_β in canonical Equiv sense** (2 decls):
  - `ua_beta_toFun_pointwise`
  - `ua_beta_invFun_pointwise`

* **§7 transport-as-equiv-application** (2 decls):
  - `transport_as_equivApp`
  - `transport_symm_as_equivApp_invFun`

* **§8 trans-via-Equiv-trans pointwise** (1 decl):
  - `idToEquivMeta_trans_toFun_via_transport`

Total: ~17 zero-axiom shipped declarations.
-/

namespace LeanFX2

/-! ## §1. ua_β cornerstone. -/

#print axioms LeanFX2.Univalence.ua_beta_meta
#print axioms LeanFX2.Univalence.ua_beta_meta_refl
#print axioms LeanFX2.Univalence.ua_beta_meta_refl_lhs
#print axioms LeanFX2.Univalence.ua_beta_meta_refl_rhs

/-! ## §2. Inverse ua_β. -/

#print axioms LeanFX2.Univalence.ua_beta_meta_symm
#print axioms LeanFX2.Univalence.ua_beta_meta_symm_refl

/-! ## §3. Composition law. -/

#print axioms LeanFX2.Univalence.transport_trans_meta
#print axioms LeanFX2.Univalence.ua_beta_meta_trans

/-! ## §4. Round-trip computation laws. -/

#print axioms LeanFX2.Univalence.transport_round_trip_toFun_invFun
#print axioms LeanFX2.Univalence.transport_round_trip_invFun_toFun

/-! ## §5. Equivalence-pinning rule. -/

#print axioms LeanFX2.Univalence.transport_via_reflEquiv
#print axioms LeanFX2.Univalence.transport_via_reflEquiv_id

/-! ## §6. ua_β in canonical Equiv sense. -/

#print axioms LeanFX2.Univalence.ua_beta_toFun_pointwise
#print axioms LeanFX2.Univalence.ua_beta_invFun_pointwise

/-! ## §7. Transport-as-equiv-application. -/

#print axioms LeanFX2.Univalence.transport_as_equivApp
#print axioms LeanFX2.Univalence.transport_symm_as_equivApp_invFun

/-! ## §8. Trans-via-Equiv-trans pointwise. -/

#print axioms LeanFX2.Univalence.idToEquivMeta_trans_toFun_via_transport

end LeanFX2
