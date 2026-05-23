import LeanFX2.Reduction.ConvRenameParJoinExtra

/-! # Smoke/AuditConvBeta — `#print axioms` log for the rename parallel-join companions

Reviewer-facing zero-axiom certificate for the three forward-rename
parallel-join companion lemmas shipped in
`Reduction/ConvRenameParJoinExtra.lean` (unblock-C.t6 forward fragment).

Each lemma is a parallel-join flavor of the T6 forward rename equivariance,
composing only shipped infrastructure (`Conv.rename_equivariant_fwd_parJoin`
from #2029, `Conv.sym`, `Step.parStar.append`).  No new kernel ctor; no
single-step `StepStar` rename-compatibility (still the unshipped ~107-arm
blocker).

* `Conv.rename_equivariant_fwd_parJoin_sym` — target-first orientation of the
  forward rename join.
* `Conv.rename_equivariant_fwd_parJoin_extend` — common-reduct extension of the
  forward rename join along a further `Step.parStar` chain.
* `Conv.weaken_equivariant_fwd_parJoin_sym` — canonical-weaken specialization of
  the symmetric form.
* `Conv.rename_equivariant_fwd_parJoin_toRaw` — raw projection of both arms to
  `RawStep.parStar` via `Step.parStar.toRawBridge`.
* `Conv.weaken_equivariant_fwd_parJoin_extend` — canonical-weaken specialization
  of the extend companion (common-reduct chain extension at one-binder weakening).
* `Conv.weaken_equivariant_fwd_parJoin_toRaw` — canonical-weaken specialization
  of the raw projection (raw join under `RawRenaming.weaken`).

Every `#print axioms` below must print "does not depend on any axioms".

## Root status

Zero-axiom. -/

namespace LeanFX2.SmokeConvBeta

#print axioms LeanFX2.Conv.rename_equivariant_fwd_parJoin_sym
#print axioms LeanFX2.Conv.rename_equivariant_fwd_parJoin_extend
#print axioms LeanFX2.Conv.weaken_equivariant_fwd_parJoin_sym
#print axioms LeanFX2.Conv.rename_equivariant_fwd_parJoin_toRaw
#print axioms LeanFX2.Conv.weaken_equivariant_fwd_parJoin_extend
#print axioms LeanFX2.Conv.weaken_equivariant_fwd_parJoin_toRaw

end LeanFX2.SmokeConvBeta
