import LeanFX2.Confluence.ConvBridge
import LeanFX2.Confluence.PreEtaStarInversion

/-! # Smoke/AuditConvCommonRawImage

Reviewer-facing `#print axioms` gate for the `Conv.*` raw-bridge
common-reduct + image-membership lemma family in
`Confluence/ConvBridge.lean`, mirroring
`Tools/AuditAll/AuditReduction.lean:800-826`.

Conv is defined as `∃ commonReduct, StepStar t1 commonReduct ∧
StepStar t2 commonReduct` (per project architectural commitment
in `lean-fx-2/CLAUDE.md`).  The lemmas below extract / transport
that common reduct under renaming and weakening, used as the raw
infrastructure layer below the typed Conv.rename_equivariant
headline (T6, #1962 / unblock-C.t6.*).

Three sub-families:

* **Image-membership transporters** (12) —
  `{renamed,weakened}_{left,right}_{commonRaw,toRawJoin}_in_{rename,weaken}_image`
  + the `_of_{source,target}Raw_eq` source/target variants.
  Each shows that the common reduct lives in the rename/weaken
  image of the appropriate side when the corresponding endpoint
  does.
* **Binder common-join lemmas** (3) —
  `{lam,lamPi,pathLam}_bodyRaw_common_join` extract a common
  reduct for the binder body from a Conv on the binder ctor.
* **Binder inversion congruence** (6) —
  `{lam,lamPi,pathLam}_{left,right}_commonRaw_inv_congr`
  recovers a sub-Conv on the bound body when the common reduct
  matches the corresponding binder ctor.
* **Top-level rename / weaken toRawJoin** (2) —
  `Conv.rename_toRawJoin` + `Conv.weaken_toRawJoin` lift the
  common-reduct existential through renaming / weakening at the
  Conv level.

Each `#print axioms` line below must report "does not depend on
any axioms" — strict Layer K gate. -/

namespace LeanFX2.Smoke.AuditConvCommonRawImage

-- Top-level rename / weaken toRawJoin.
#print axioms LeanFX2.Conv.rename_toRawJoin
#print axioms LeanFX2.Conv.weaken_toRawJoin

-- Binder left/right commonRaw inversion congruence.
#print axioms LeanFX2.Conv.lam_left_commonRaw_inv_congr
#print axioms LeanFX2.Conv.lamPi_left_commonRaw_inv_congr
#print axioms LeanFX2.Conv.pathLam_left_commonRaw_inv_congr
#print axioms LeanFX2.Conv.lam_right_commonRaw_inv_congr
#print axioms LeanFX2.Conv.lamPi_right_commonRaw_inv_congr
#print axioms LeanFX2.Conv.pathLam_right_commonRaw_inv_congr

-- Binder body common-join extraction.
#print axioms LeanFX2.Conv.lam_bodyRaw_common_join
#print axioms LeanFX2.Conv.lamPi_bodyRaw_common_join
#print axioms LeanFX2.Conv.pathLam_bodyRaw_common_join

-- Renamed / weakened left-side image membership transporters.
#print axioms LeanFX2.Conv.renamed_left_commonRaw_in_rename_image
#print axioms LeanFX2.Conv.weakened_left_commonRaw_in_weaken_image
#print axioms LeanFX2.Conv.renamed_left_toRawJoin_in_rename_image
#print axioms LeanFX2.Conv.weakened_left_toRawJoin_in_weaken_image
#print axioms LeanFX2.Conv.left_commonRaw_in_rename_image_of_sourceRaw_eq
#print axioms LeanFX2.Conv.left_commonRaw_in_weaken_image_of_sourceRaw_eq

-- Renamed / weakened right-side image membership transporters.
#print axioms LeanFX2.Conv.renamed_right_commonRaw_in_rename_image
#print axioms LeanFX2.Conv.weakened_right_commonRaw_in_weaken_image
#print axioms LeanFX2.Conv.renamed_right_toRawJoin_in_rename_image
#print axioms LeanFX2.Conv.weakened_right_toRawJoin_in_weaken_image
#print axioms LeanFX2.Conv.right_commonRaw_in_rename_image_of_targetRaw_eq
#print axioms LeanFX2.Conv.right_commonRaw_in_weaken_image_of_targetRaw_eq

-- Left/right toRawJoin source/target raw-equality image transporters.
#print axioms LeanFX2.Conv.left_toRawJoin_in_rename_image_of_sourceRaw_eq
#print axioms LeanFX2.Conv.left_toRawJoin_in_weaken_image_of_sourceRaw_eq
#print axioms LeanFX2.Conv.right_toRawJoin_in_rename_image_of_targetRaw_eq
#print axioms LeanFX2.Conv.right_toRawJoin_in_weaken_image_of_targetRaw_eq

end LeanFX2.Smoke.AuditConvCommonRawImage
