import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Orders.RecursivePathOrderInductive

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Orders.RecursivePathOrderInductive

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Orders.RecursivePathOrderInductive`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The genuine INDUCTIVE recursive path order: the generic rose-tree RPO with multiset status,
-- positivity-accepted (subterm clause split into subtermEq/subtermStrict to avoid the kernel's nested-Or
-- rejection; multiset witnesses inlined to avoid passing the inductive to the external MultisetRedOne).
-- rpo_orients_natElim ORIENTS the branch-duplication obstruction arm — redex ≻ reduct for natElim(succ n) z s
-- with an ARBITRARY duplicated branch s — exactly what every flat measure failed; the subterm
-- property tames the duplication. fxPrecedence_wellFounded is the first WF ingredient. The full RPO
-- well-foundedness (Nipkow/Buchholz nested accessibility, fed by MultisetRedOne.consAccessible) is the crux.
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_orients_natElim

#assert_no_axioms FX1Poly.Core.RpoInductive.fxPrecedence_wellFounded

-- RPO well-foundedness: the Nipkow/Buchholz nested-accessibility theorem, zero-axiom and with
-- NO size measure. acc_node uses the rose-tree recursor twice (top-level wrapper + the predecessor's
-- predAcc, which supplies the precedence/multiset cases their children accessible — breaking the apparent
-- circularity); the four-clause Rpo inversion via `cases` is propext-clean. rpoWellFounded :
-- WellFounded prec → WellFounded (RpoBelow prec); fxRpoWellFounded instantiates it at fxPrecedence, so the
-- branch-duplication obstruction arm (oriented by rpo_orients_natElim) sits in a genuine well-founded order.
#assert_no_axioms FX1Poly.Core.RpoInductive.rpoWellFounded

#assert_no_axioms FX1Poly.Core.RpoInductive.fxRpoWellFounded

-- RPO congruence: the order is a CONGRUENCE — replacing one child by an RPO-smaller child makes
-- the node RPO-smaller (via the multiset clause: a single Dershowitz-Manna decrease, unchanged children
-- dominated as subterms, the replacement dominated through the larger child). This is the monotonicity /
-- compatibility-with-contexts that turns the root-redex order into a genuine REWRITE order — the load-bearing
-- ingredient that lifts a child-context ι step to a node-level RPO decrease. The four List append/membership
-- helpers it consumes are propext-clean re-proofs (Init's List.append_assoc and friends leak propext).
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_congruence

#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_congruence_head

end FX1PolyAudit
