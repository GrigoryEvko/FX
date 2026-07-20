import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.OpenPetriCospan

/-! # FX1PolyAudit/Polygraph/Net/OpenPetriCospan — zero-axiom gate
    (NET-9 brick: open Petri nets as cospans)

Per-declaration zero-axiom gate for the open-Petri-net cospan kit: the Boolean
micro-kit, the carrier (`OcpTransition`/`OcpNet`/`OcpOpenNet`), the list/relabel
utilities, boundary-glued composition `openNetCompose` (the union-find pushout),
`canonicalizeOpenNet`, the structural decision `decideOpenNetEq` with soundness
`decideOpenNetEqSound`, the sound cospan congruence `OcpOpenNetConv` /
`ocpOpenNetConvSound`, the capability + wall markers, and the ground fires.

The *universal* cospan identity / associativity laws are WALLED
(`ocpHasUniversalIdentityLaw = false`, `ocpHasCospanAssociativity = false`): the
`openNetCompose` glue pattern-matches on the boundary ids, so no `rfl`/`simp`
reduction closes them uniformly — the honest proof needs the
`renameLinks_unionFindJoin` root transport whose stabilisation over an arbitrary
boundary rests on `WellFounded.fix`.  General net iso without the ordered boundary is
graph-isomorphism-hard (`ocpHasGeneralNetIsoDecision = false`); compositional
coverability is Karp–Miller = the NET-4 Dickson wall
(`ocpHasCompositionalCoverability = false`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Net.ocpBoth
#assert_no_axioms FX1Poly.Polygraph.Net.ocpBothElim
#assert_no_axioms FX1Poly.Polygraph.Net.OcpTransition
#assert_no_axioms FX1Poly.Polygraph.Net.OcpTransition.mk
#assert_no_axioms FX1Poly.Polygraph.Net.OcpNet
#assert_no_axioms FX1Poly.Polygraph.Net.OcpNet.mk
#assert_no_axioms FX1Poly.Polygraph.Net.OcpOpenNet
#assert_no_axioms FX1Poly.Polygraph.Net.OcpOpenNet.mk
#assert_no_axioms FX1Poly.Polygraph.Net.ocpMapId
#assert_no_axioms FX1Poly.Polygraph.Net.ocpMemBool
#assert_no_axioms FX1Poly.Polygraph.Net.ocpAllMem
#assert_no_axioms FX1Poly.Polygraph.Net.ocpListMax
#assert_no_axioms FX1Poly.Polygraph.Net.ocpDedupFrom
#assert_no_axioms FX1Poly.Polygraph.Net.ocpDedup
#assert_no_axioms FX1Poly.Polygraph.Net.ocpIndexOf
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransRelabel
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransListRelabel
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransNormalize
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransListNormalize
#assert_no_axioms FX1Poly.Polygraph.Net.ocpListLe
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransLe
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransInsert
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransSort
#assert_no_axioms FX1Poly.Polygraph.Net.ocpIsWellFormed
#assert_no_axioms FX1Poly.Polygraph.Net.ocpAllIds
#assert_no_axioms FX1Poly.Polygraph.Net.ocpOffset
#assert_no_axioms FX1Poly.Polygraph.Net.ocpBuildGlue
#assert_no_axioms FX1Poly.Polygraph.Net.openNetCompose
#assert_no_axioms FX1Poly.Polygraph.Net.identityOpenNet
#assert_no_axioms FX1Poly.Polygraph.Net.ocpCanonOrder
#assert_no_axioms FX1Poly.Polygraph.Net.canonicalizeOpenNet
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransBeq
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransListBeq
#assert_no_axioms FX1Poly.Polygraph.Net.ocpNetBeq
#assert_no_axioms FX1Poly.Polygraph.Net.ocpOpenNetBeq
#assert_no_axioms FX1Poly.Polygraph.Net.decideOpenNetEq
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransBeqEq
#assert_no_axioms FX1Poly.Polygraph.Net.ocpTransListBeqEq
#assert_no_axioms FX1Poly.Polygraph.Net.ocpNetBeqEq
#assert_no_axioms FX1Poly.Polygraph.Net.ocpOpenNetBeqEq
#assert_no_axioms FX1Poly.Polygraph.Net.decideOpenNetEqSound
#assert_no_axioms FX1Poly.Polygraph.Net.OcpOpenNetConv
#assert_no_axioms FX1Poly.Polygraph.Net.OcpOpenNetConv.ofCanonEq
#assert_no_axioms FX1Poly.Polygraph.Net.OcpOpenNetConv.symm
#assert_no_axioms FX1Poly.Polygraph.Net.OcpOpenNetConv.trans
#assert_no_axioms FX1Poly.Polygraph.Net.ocpOpenNetConvRefl
#assert_no_axioms FX1Poly.Polygraph.Net.ocpOpenNetConvSound
#assert_no_axioms FX1Poly.Polygraph.Net.ocpExampleA
#assert_no_axioms FX1Poly.Polygraph.Net.ocpExampleB
#assert_no_axioms FX1Poly.Polygraph.Net.ocpIdOnLeftA
#assert_no_axioms FX1Poly.Polygraph.Net.ocpIdOnRightA
#assert_no_axioms FX1Poly.Polygraph.Net.ocpHasOpenNetCospanDecision
#assert_no_axioms FX1Poly.Polygraph.Net.ocpHasGeneralNetIsoDecision
#assert_no_axioms FX1Poly.Polygraph.Net.ocpHasCompositionalCoverability
#assert_no_axioms FX1Poly.Polygraph.Net.ocpHasUniversalIdentityLaw
#assert_no_axioms FX1Poly.Polygraph.Net.ocpHasCospanAssociativity
#assert_no_axioms FX1Poly.Polygraph.Net.ocpFireLeftIdDecidesEqual
#assert_no_axioms FX1Poly.Polygraph.Net.ocpFireRightIdDecidesEqual
#assert_no_axioms FX1Poly.Polygraph.Net.ocpFireDistinctDecideFalse
#assert_no_axioms FX1Poly.Polygraph.Net.ocpFireSelfDecidesEqual
#assert_no_axioms FX1Poly.Polygraph.Net.ocpFireGlueCanonicalPlaces
#assert_no_axioms FX1Poly.Polygraph.Net.ocpLeftIdConvConcrete
#assert_no_axioms FX1Poly.Polygraph.Net.ocpRightIdConvConcrete

end FX1PolyAudit
